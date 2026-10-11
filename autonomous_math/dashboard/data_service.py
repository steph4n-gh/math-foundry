"""Read-only views of the authoritative research snapshot and proof receipts."""
from __future__ import annotations
import json
import hashlib
import logging
import math
import os
from pathlib import Path
import re
import time
import threading
from typing import Any, Dict, Optional
import networkx as nx
import numpy as np
from autonomous_math.research_state import load_snapshot, validate_receipt, json_safe, proof_reuse_summary
logger = logging.getLogger("dashboard.data")
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
API_LOCK = threading.RLock()
CAMPAIGN_LABELS = {
    "spectral": "Spectral bounds", "extremal_coloring": "Extremal coloring",
    "independence_clique": "Independence & cliques", "metric_topological": "Metric & topology",
    "advanced_spectral": "Advanced spectra", "chemical_energy": "Graph energy",
    "expander_codes": "Binary adjacency codes",
}

class DashboardDataService:
    def __init__(self, repo_root=None, data_dir=None):
        self.repo_root = Path(repo_root or REPO_ROOT)
        self.research_dir = Path(data_dir or self.repo_root / "research_outputs").resolve()
        self._verified_counterexamples = {}
    def load_atlas(self):
        return load_snapshot(self.research_dir)
    def get_token_usage(self, now=None):
        """Sum saved request reports, including failed and uncommitted attempts.

        Atlas histories can be replaced or truncated. Each request directory is
        immutable in identity; its trace is updated as that request completes.
        Cached input and reasoning output are subsets, not additional tokens.
        The recent window uses trace modification time, not inferred billing time.
        """
        now = time.time() if now is None else now
        requests, unreadable, job_campaigns = {}, 0, {}
        def campaign_for(path):
            for directory in path.parents:
                if directory == self.research_dir:
                    break
                job_path = directory / "job.json"
                if job_path not in job_campaigns:
                    campaign = None
                    if job_path.is_file():
                        try:
                            job = json.loads(job_path.read_text())
                            campaign = job.get("campaign") or (job.get("options") or {}).get("campaign")
                        except (OSError, ValueError, TypeError, AttributeError):
                            pass
                    job_campaigns[job_path] = campaign if isinstance(campaign, str) and campaign in CAMPAIGN_LABELS else None
                if job_campaigns[job_path]:
                    return job_campaigns[job_path]
            return None
        for path in self.research_dir.rglob("trace.json"):
            try:
                with path.open() as stream:
                    modified = os.fstat(stream.fileno()).st_mtime
                    trace = json.load(stream)
                if not isinstance(trace, dict):
                    raise ValueError("Request trace must be an object")
            except (OSError, ValueError):
                unreadable += 1
                continue
            artifact = trace.get("artifact_path")
            if isinstance(artifact, str) and artifact:
                key = ("artifact", os.path.normpath(artifact))
            elif isinstance(trace.get("thread_id"), str) and trace["thread_id"]:
                key = ("thread", trace["thread_id"])
            else:
                key = ("path", str(path.resolve()))
            usage = trace.get("usage")
            reported = isinstance(usage, dict) and all(
                type(usage.get(k)) is int and usage[k] >= 0 for k in ("input_tokens", "output_tokens"))
            cached = usage.get("cached_input_tokens", 0) if reported else 0
            reported = reported and type(cached) is int and 0 <= cached <= usage["input_tokens"]
            pending = trace.get("status") in {"STARTING", "RUNNING"}
            # A copied pre-completion trace must not replace a final usage report.
            rank = (reported, not pending, modified)
            if key not in requests or rank > requests[key][0]:
                original = Path(artifact) / "trace.json" if isinstance(artifact, str) and artifact else None
                original = original if original and original.resolve().is_relative_to(self.research_dir) else None
                review = "novelty_attempts" in path.relative_to(self.research_dir).parts or (
                    original is not None and "novelty_attempts" in original.resolve().relative_to(self.research_dir).parts)
                campaign = None if review else (campaign_for(original) if original else None) or campaign_for(path)
                requests[key] = (rank, usage, cached, pending, modified, campaign, review)
        result = {"requests": len(requests), "reported_requests": 0, "unreported_requests": 0,
                  "pending_request_traces": 0, "unreadable_traces": unreadable,
                  "input_tokens": 0, "cached_input_tokens": 0, "output_tokens": 0,
                  "total_tokens": 0, "last_hour": {"reported_requests": 0, "unreported_requests": 0,
                                                   "total_tokens": 0}}
        result.update(completed_requests=0, completed_missing_usage_requests=0, completed_total_tokens=0)
        result["by_campaign"] = {}
        result["unattributed"] = {"requests": 0, "reported_requests": 0, "unreported_requests": 0,
                                  "pending_request_traces": 0, "total_tokens": 0}
        result["review"] = {"requests": 0, "reported_requests": 0, "unreported_requests": 0, "total_tokens": 0}
        for rank, usage, cached, pending, modified, campaign, review in requests.values():
            bucket = result["by_campaign"].setdefault(campaign, {"requests": 0, "reported_requests": 0,
                "unreported_requests": 0, "pending_request_traces": 0, "total_tokens": 0}) if campaign else result["unattributed"]
            bucket["requests"] += 1
            bucket["pending_request_traces"] += int(pending)
            recent = now - 3600 <= modified <= now
            result["pending_request_traces"] += int(pending)
            result["completed_requests"] += int(not pending)
            result["completed_missing_usage_requests"] += int(not pending and not rank[0])
            field = "reported_requests" if rank[0] else "unreported_requests"
            bucket[field] += 1
            if review:
                result["review"]["requests"] += 1
                result["review"][field] += 1
            result[field] += 1
            if recent:
                result["last_hour"][field] += 1
            if not rank[0]:
                continue
            result["input_tokens"] += usage["input_tokens"]
            result["cached_input_tokens"] += cached
            result["output_tokens"] += usage["output_tokens"]
            total = usage["input_tokens"] + usage["output_tokens"]
            bucket["total_tokens"] += total
            if review:
                result["review"]["total_tokens"] += total
            if not pending:
                result["completed_total_tokens"] += total
            result["total_tokens"] += total
            if recent:
                result["last_hour"]["total_tokens"] += total
        return result

    def get_campaigns(self, atlas, status, usage):
        """Expose tracked campaign work without backfilling historical attribution."""
        rotation = status.get("campaign_rotation") or atlas.get("campaign_rotation") or {}
        schedule = rotation.get("schedule")
        if not isinstance(schedule, list):
            selected = atlas.get("configuration", {}).get("campaign")
            schedule = [selected] if selected in CAMPAIGN_LABELS else list(CAMPAIGN_LABELS)
        schedule = [name for name in schedule if isinstance(name, str) and name in CAMPAIGN_LABELS]
        current = rotation.get("current") if status.get("state") == "running" else None
        progress = atlas.get("campaign_progress", {})
        rows = []
        for name, label in CAMPAIGN_LABELS.items():
            item = progress.get(name)
            tracked = isinstance(item, dict)
            item = item if tracked else {}
            visit = (status.get("campaign_visits") or {}).get(name) or {}
            ids = item.get("certified_ids")
            added = len(set(ids)) if isinstance(ids, list) and all(isinstance(i, str) for i in ids) else None
            state = ("running" if current == name else "outside_schedule" if name not in schedule else
                     "next" if rotation.get("next") == name else "visited" if item.get("completed_batches") else "untracked")
            rows.append({"name": name, "label": label, "state": state, "tracked": tracked,
                "completed_batches": item.get("completed_batches"), "last_checkpoint": item.get("last_checkpoint"),
                "last_completed_at": item.get("last_completed_at"), "unique_proofs_added": added,
                "last_visited_checkpoint": visit.get("checkpoint", item.get("last_checkpoint")),
                "last_visited_at": visit.get("started_at", item.get("last_completed_at")),
                "unsupported_lean_candidates": item.get("unsupported_lean_candidates"),
                "token_usage": usage.get("by_campaign", {}).get(name),
                "limitations": "Diameter, radius, and girth have no reviewed Lean translation; empirical candidates remain unproved." if name == "metric_topological" else
                    "Exact numerical code checks only through order 16; larger samples are undefined. Lean scope is all finite graphs." if name == "expander_codes" else None})
        records = atlas.get("theorems", {}).values()
        return {"revision": rotation.get("revision"), "current": current, "next": rotation.get("next"),
            "schedule": schedule, "started_checkpoint": rotation.get("started_checkpoint"), "rows": rows,
            "unattributed_usage": usage.get("unattributed"), "review_usage": usage.get("review"),
            "historical_unattributed_proofs": sum(r.get("status") == "LEAN_CERTIFIED" and
                r.get("certified_campaign") not in CAMPAIGN_LABELS for r in records),
            "batch_progress": status.get("batch_progress"), "active_batch": status.get("active_batch")}
    def get_telemetry(self, atlas=None):
        atlas = atlas if atlas is not None else self.load_atlas()
        status_path = self.research_dir / "run_status.json"
        status = json.loads(status_path.read_text()) if status_path.exists() else {"state": "unknown"}
        if status.get("state") == "running":
            alive = False
            try:
                os.kill(status["pid"], 0)
                alive = time.time() - status.get("heartbeat", 0) < 15
            except (OSError, KeyError):
                pass
            if not alive:
                status["state"] = "stale"
        from autonomous_math.sieve.instance_db import InstanceDatabase
        db = InstanceDatabase()
        configuration = atlas.get("configuration", {})
        batch = atlas.get("batch_metrics", {})
        code_catalog = atlas.get("code_catalog")
        if code_catalog is None and (configuration.get("campaign") == "expander_codes" or
                                    batch.get("research_family") == "expander_codes"):
            code_catalog = db.ensure_code_columns()
        records = atlas.get("theorems", {}).values()
        from autonomous_math.core.ast import Conjecture
        from autonomous_math.prover.trusted_lean import render_challenge
        formalization_blocked = 0
        for record in records:
            if record.get("status") != "EMPIRICAL_SURVIVOR" or not record.get("conjecture"):
                continue
            try:
                render_challenge(Conjecture.from_dict(record["conjecture"]))
            except ValueError:
                formalization_blocked += 1
        synthesis = [attempt for r in records for attempt in
                     (r.get("proof_attempt") or {}).get("synthesis_attempts", [])]
        proposals = atlas.get("model_proposals", [])
        latest_proposal = proposals[-1] if proposals else {}
        selection = status.get("model_selection")
        if selection:
            selection = dict(selection, source="runner", enabled=selection.get("enabled", True))
        else:
            request_config = next((a.get("configuration") for a in reversed(synthesis)
                                   if a.get("configuration")), {})
            selection = {"source": "historical", "enabled": configuration.get("proof_backend") != "none",
                         "model": configuration.get("model") or request_config.get("model_override") or request_config.get("model") or
                         request_config.get("configured_model"),
                         "reasoning_effort": configuration.get("reasoning_effort") or
                         request_config.get("reasoning_effort") or request_config.get("configured_reasoning_effort")}
        usage = self.get_token_usage()
        return {"total_conjectures": atlas.get("total_conjectures_generated", 0),
            "total_survived": atlas.get("total_survived", 0), "total_refuted": atlas.get("total_refuted", 0),
            "total_rediscoveries": atlas.get("total_verified_rediscoveries", 0),
            "total_novel": atlas.get("total_candidate_novel", 0),
            "total_unknown_literature": atlas.get("total_unknown_literature", 0),
            "total_lean_certified": atlas.get("total_lean_certified", 0),
            "active_flywheel_lemmas": atlas.get("total_lean_certified", 0),
            "catalog_graphs": atlas.get("catalog_graphs", len(db._cached_gi)),
            "base_catalog_graphs": len(db._cached_gi), "replayed_boundary_graphs": atlas.get("replayed_boundary_graphs", 0),
            "invariants_tracked": len(db._cached_matrix),
            "total_iterations": atlas.get("total_iterations", 0), "timestamp": atlas.get("saved_at"),
            "pipeline": {"configuration": configuration,
                "model_selection": selection, "code_catalog": code_catalog,
                "token_usage": usage, "campaigns": self.get_campaigns(atlas, status, usage),
                "last_batch": atlas.get("batch_metrics", {}),
                "formalization_blocked": formalization_blocked,
                "model_requests": len(synthesis) + len(atlas.get("model_proposals", [])),
                "research_agenda": latest_proposal.get("agenda"),
                "mathlib_lookup": latest_proposal.get("mathlib_lookup"),
                "proof_reuse": proof_reuse_summary(atlas),
                "model_proofs": sum((r.get("lean_proof") or {}).get("proof_origin") == "codex_synthesis"
                    for r in records)},
            "data_dir": str(self.research_dir), "runner": status,
            "data_state": "available" if (self.research_dir / "cumulative_discovery_atlas.json").exists() else "missing"}
    def get_theorems(self, filter_type="ALL", query="", guard=None, atlas=None):
        from autonomous_math.export.research_packet import proof_writeup
        atlas = atlas if atlas is not None else self.load_atlas()
        result = []
        for item in atlas.get("theorems", {}).values():
            item = dict(item)
            item.pop("legacy_record", None)
            item.pop("legacy_proof", None)
            if item.get("novelty_status") in {"CANDIDATE_NOVEL", "CANDIDATE_NOVEL_CONJECTURE"}:
                item["novelty_status"] = "UNKNOWN_IN_LITERATURE"
                item["novelty_score"] = 0.0
            if item.get("status") == "CANDIDATE_NOVEL":
                item["status"] = "UNVERIFIED"
            if filter_type == "LEAN_CERTIFIED" and item.get("status") != "LEAN_CERTIFIED": continue
            if filter_type in {"CANDIDATE_NOVEL", "UNKNOWN_IN_LITERATURE"} and item.get("novelty_status") != "UNKNOWN_IN_LITERATURE": continue
            if filter_type == "VERIFIED_REDISCOVERY" and item.get("novelty_status") not in {"VERIFIED_REDISCOVERY", "TEXTBOOK_FOLKLORE"}: continue
            if filter_type == "GUARDED" and not item.get("guard"): continue
            if guard and item.get("guard") != guard: continue
            searchable = {key: item.get(key) for key in ("id", "statement", "matched_theorem")}
            if query.lower() not in json.dumps(searchable, default=str).lower(): continue
            if item.get("status") == "LEAN_CERTIFIED" and item.get("conjecture"):
                item["writeup"] = proof_writeup(item)
            result.append(item)
        return sorted(result, key=lambda r: (r.get("status") != "LEAN_CERTIFIED", r["id"]))
    def get_counterexamples(self, atlas=None):
        with API_LOCK:
            return self._get_counterexamples(atlas)

    def _get_counterexamples(self, atlas=None):
        atlas = atlas if atlas is not None else self.load_atlas()
        from autonomous_math.core.ast import Conjecture
        from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier
        references = [("cycle_5", nx.cycle_graph(5)), ("petersen_graph", nx.petersen_graph()),
                      ("complete_bipartite_3_3", nx.complete_bipartite_graph(3,3)), ("star_graph_1_4", nx.star_graph(4))]
        result = [{"id": name, "name": name, "family": "Reference graph", "order": g.number_of_nodes(),
                   "size": g.number_of_edges(), "nodes": list(g), "edges": list(g.edges()),
                   "description": "Reference topology; not a discovery certificate."} for name,g in references]
        active_keys = set()
        for item in atlas.get("theorems", {}).values():
            if not item.get("counterexample") or not item.get("conjecture"): continue
            key = hashlib.sha256(json.dumps(json_safe({field: item[field] for field in
                ("id", "statement", "counterexample", "conjecture")}), sort_keys=True, allow_nan=False).encode()).hexdigest()
            active_keys.add(key)
            row = self._verified_counterexamples.get(key)
            if row is None:
                certificate = CounterexampleCertificate.from_dict(item["counterexample"])
                conjecture = Conjecture.from_dict(item["conjecture"])
                valid, errors = CounterexampleCertificateVerifier.verify_with_details(certificate, conjecture)
                if not valid: raise ValueError(f"Invalid counterexample {item['id']}: {errors}")
                graph = certificate.to_networkx()
                row = {"id": item["id"], "name": item["id"], "family": "Verified refutation",
                    "order": graph.number_of_nodes(), "size": graph.number_of_edges(), "nodes": list(graph),
                    "edges": list(graph.edges()), "statement": item["statement"], "description": item["statement"],
                    "certificate": item["counterexample"]}
                self._verified_counterexamples[key] = row
            result.append(row)
        # Discard obsolete entries when committed counterexamples change.
        self._verified_counterexamples = {key: row for key, row in self._verified_counterexamples.items()
                                         if key in active_keys}
        return result
    def get_lean_code(self, theorem_id):
        record = self.load_atlas().get("theorems", {}).get(theorem_id, {})
        receipt, error = validate_receipt((record.get("lean_proof") or {}).get("receipt_path", ""), theorem_id)
        if not receipt:
            return {"theorem_id": theorem_id, "found": False, "code": "-- No valid proof receipt.", "error": error}
        path = Path(receipt["source_path"])
        return {"theorem_id": theorem_id, "found": True, "code": path.read_text(), "file_path": str(path),
                "file_name": path.name, "tactic": receipt["tactic"], "duration_ms": receipt["duration_ms"],
                "receipt": receipt}

    def get_research_packet(self, theorem_id):
        from autonomous_math.export.research_packet import packet_response
        atlas = self.load_atlas()
        record = atlas.get("theorems", {}).get(theorem_id)
        if not record or record.get("status") != "LEAN_CERTIFIED":
            return {"found": False, "theorem_id": theorem_id,
                    "error": "No currently certified theorem with this identifier"}
        review = next((r for r in self.get_novelty_reviews(atlas).get("records", [])
                       if r.get("id") == theorem_id), None)
        try:
            return packet_response(record, review, self.research_dir)
        except (OSError, ValueError, KeyError, TypeError) as exc:
            return {"found": False, "theorem_id": theorem_id, "error": str(exc)}

    def get_pointcloud(
        self,
        x_inv: str = "max_degree",
        y_inv: str = "spectral_radius",
        z_inv: Optional[str] = None,
    ) -> Dict[str, Any]:
        """Compute 2D or 3D invariant coordinate points and convex hull facets."""
        from autonomous_math.sieve.instance_db import InstanceDatabase, CODE_COLUMNS

        db = InstanceDatabase()
        if any(axis in CODE_COLUMNS for axis in (x_inv, y_inv, z_inv)):
            db.ensure_code_columns()
        else:
            atlas = self.load_atlas()
            if (atlas.get("configuration", {}).get("campaign") == "expander_codes" or
                atlas.get("batch_metrics", {}).get("research_family") == "expander_codes"):
                db.ensure_code_columns()
        mat = db._cached_matrix or {}

        for axis in (x_inv, y_inv, z_inv):
            if axis is not None and axis not in mat:
                raise ValueError(f"Unsupported invariant: {axis}")

        x_vals = mat[x_inv]
        y_vals = mat[y_inv]
        z_vals = mat.get(z_inv) if z_inv and z_inv in mat else None

        coords = np.column_stack([x_vals, y_vals] + ([z_vals] if z_vals is not None else []))
        finite_ids = np.flatnonzero(np.all(np.isfinite(coords), axis=1))
        points = [{"id": int(i), "x": float(x_vals[i]), "y": float(y_vals[i]),
                   **({"z": float(z_vals[i])} if z_vals is not None else {})} for i in finite_ids]
        hull_indices = []
        hull_simplices = []
        try:
            from scipy.spatial import ConvexHull
            unique_coords, u_indices = np.unique(coords[finite_ids], axis=0, return_index=True)
            if len(unique_coords) >= (4 if z_vals is not None else 3):
                hull = ConvexHull(unique_coords, qhull_options="QJ")
                original_ids = finite_ids[u_indices]
                hull_indices = [int(original_ids[v]) for v in hull.vertices]
                hull_simplices = [[int(original_ids[v]) for v in simplex] for simplex in hull.simplices]
        except Exception as exc:
            logger.debug("ConvexHull computation failed: %s", exc)
        if len(points) > 2000:
            hull_ids = sorted(set(hull_indices))[:2000]
            other_ids = sorted(set(map(int, finite_ids)) - set(hull_ids))
            budget = 2000 - len(hull_ids)
            sampled = [other_ids[int(i)] for i in np.linspace(0, len(other_ids)-1, min(budget, len(other_ids)), dtype=int)] if budget else []
            keep = set(hull_ids + sampled)
            points = [p for p in points if p["id"] in keep]
            hull_indices = [i for i in hull_indices if i in keep]
            hull_simplices = [facet for facet in hull_simplices if set(facet) <= keep]

        return {
            "x_axis": x_inv,
            "y_axis": y_inv,
            "z_axis": z_inv,
            "total_points": len(points),
            "excluded_undefined_points": len(coords) - len(finite_ids),
            "points": points,
            "hull_indices": hull_indices,
            "hull_simplices": hull_simplices,
            "available_invariants": sorted(list(mat.keys())),
        }

    def get_flywheel_status(self, atlas=None):
        atlas = atlas if atlas is not None else self.load_atlas()
        lemmas = []
        for r in atlas.get("theorems", {}).values():
            if r.get("status") != "LEAN_CERTIFIED":
                continue
            proof = r.get("lean_proof") or {}
            if proof.get("verified") and proof.get("theorem_name"):
                from autonomous_math.core.ast import Conjecture
                c = Conjecture.from_dict(r["conjecture"])
                lemmas.append({"lemma_id": r["id"], "statement": r["statement"],
                    "lean_name": proof["theorem_name"], "tactic": proof["tactic"],
                    "invariants": sorted(c.lhs_expr.variables | c.rhs_expr.variables),
                    "receipt_path": r["lean_proof"]["receipt_path"], "is_machine_checked": True})
        fertility = atlas.get("invariant_fertility", {})
        return {"total_active_lemmas": len(lemmas), "lemmas": lemmas,
            "feedback": {"invariant_fertility": fertility,
                         "top_fertile_invariants": sorted(fertility.items(), key=lambda x: x[1], reverse=True)}}
    def get_mathlib_bridge_info(self):
        from autonomous_math.prover.trusted_lean import capability_report
        capabilities = capability_report()
        return {"title": "Trusted finite graph formalization", "workspace": str(REPO_ROOT / "certified_lean"),
            "supported_invariants": capabilities["invariants"],
            "supported_properties": capabilities["properties"], "capabilities": capabilities,
            "type_alignment": {"canonical_casting": "ENat.toNat for finite chromatic number; cliqueNum is Nat in the pinned Mathlib"},
            "canonical_aliases": [], "canonical_lemma_bridges": [],
            "spectral_energy_extensions": {"status": "NATIVE_MATHLIB_DEFINITIONS",
                "reason": capabilities["spectral_semantics"],
                "quantities": [n for n in capabilities["invariants"] if any(
                    token in n for token in ("spectral", "energy", "estrada", "connectivity"))]}}
    def get_snapshot(self):
        atlas = self.load_atlas()
        reviews = self.get_novelty_reviews(atlas)
        telemetry = self.get_telemetry(atlas)
        from autonomous_math.novelty.frontier import coding_frontier, progress_view
        period = telemetry.get("runner", {}).get("frontier_period") or atlas.get("frontier_period")
        frontier = progress_view(reviews.get("records", []), telemetry.get("pipeline", {}).get("token_usage"),
                                 period, time.time())
        if atlas.get("configuration", {}).get("campaign") == "expander_codes":
            frontier["question"] = coding_frontier()
        frontier["batch"] = {key: atlas.get("batch_metrics", {}).get(key, 0)
                             for key in ("routine_variants_suppressed", "routine_helpers_local_only")}
        return {"telemetry": telemetry, "theorems": self.get_theorems(atlas=atlas),
                "counterexamples": self.get_counterexamples(atlas), "flywheel": self.get_flywheel_status(atlas),
                "novelty_reviews": reviews, "research_frontier": frontier}

    def get_novelty_reviews(self, atlas=None):
        from autonomous_math.novelty.review import get_reviews
        try:
            return get_reviews(atlas if atlas is not None else self.load_atlas(), self.research_dir)
        except (OSError, ValueError, TypeError, KeyError) as exc:
            logger.warning("Originality review unavailable: %s", exc)
            return {"schema_version": 1, "status": "unavailable", "error": str(exc),
                    "updated_at": None, "counts": {}, "records": []}
