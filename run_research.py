#!/usr/bin/env python3
"""Evidence-based research runner. All modes commit the same validated snapshot schema."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import logging
import os
from pathlib import Path
import random
import signal
import threading
import time
import uuid
from functools import lru_cache
from typing import Any, Dict, Optional
import networkx as nx
import math
from autonomous_math.core.ast import Conjecture, InvariantNode, GuardPredicate
from autonomous_math.core.invariants import GraphInvariantEvaluator, STANDARD_SCALAR_INVARIANTS
from autonomous_math.conjecturing.generator import ConjectureGenerator
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier, SieveResult
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.flywheel import LemmaFlywheel
from autonomous_math.novelty.literature_crosscheck import LiteratureCrossChecker
from autonomous_math.export.lean_generator import LeanComparatorGenerator
from autonomous_math.research_state import atomic_save_json, writer_lock, load_snapshot, reconcile, json_safe, validate_receipt
REPO_ROOT = Path(__file__).resolve().parent
CANDIDATE_IDENTITY_REVISION = "lossless-numeric-v2"
MAX_WORKERS = 16
CAMPAIGN_ROTATION_REVISION = "campaign-focus-v1"
logger = logging.getLogger("research")

class GracefulDaemonInterrupt:
    def __init__(self):
        self.stop_requested = False
        self.stop_signal = None
        self.previous = {}
    def install(self):
        if threading.current_thread() is threading.main_thread():
            for sig in (signal.SIGINT, signal.SIGTERM):
                self.previous[sig] = signal.signal(sig, self._handler)
    def uninstall(self):
        for sig, handler in self.previous.items():
            signal.signal(sig, handler)
    def _handler(self, signum, frame):
        if self.stop_signal is None:
            self.stop_signal = {"number": int(signum), "name": signal.Signals(signum).name,
                                "received_at": time.time()}
        self.stop_requested = True


def _record_stop_diagnostics(status, stop):
    """Persist the first stop origin while retaining any received signal."""
    if getattr(stop, "stop_signal", None) is not None:
        status["stop_signal"] = dict(stop.stop_signal)
    if stop.stop_requested:
        status.setdefault("stop_origin", "signal" if status.get("stop_signal") else "requested_stop")
        status.setdefault("stop_reason", "Received " + status["stop_signal"]["name"]
                          if status.get("stop_signal") else "Cooperative research stop requested")


def _check_batch_stop(stop, deadline):
    # Keep the existing interruption and finite deadline semantics; attach the
    # source of the interruption so the coordinator does not discard it.
    if stop.stop_requested or time.monotonic() >= deadline:
        error = InterruptedError("Research stopped before batch commit")
        if stop.stop_requested:
            error.stop_origin = "signal" if getattr(stop, "stop_signal", None) else "requested_stop"
        else:
            error.stop_origin = "batch_deadline"
        raise error

CAMPAIGN_PRESETS = {
    "spectral": {
        "title": "Spectral Graph Theory & Eigenvalue Bounds",
        "description": "Explores relationships between adjacency eigenvalues, Laplacian spectrum, algebraic connectivity, and chromatic/independence numbers.",
        "pairs": [
            ("chromatic_number", "spectral_radius"),
            ("chromatic_number", "laplacian_spectral_radius"),
            ("algebraic_connectivity", "min_degree"),
            ("spectral_radius", "max_degree"),
            ("spectral_radius", "average_degree"),
        ],
        "triads": [
            ("chromatic_number", ["spectral_radius", "clique_number"]),
            ("signless_laplacian_spectral_radius", ["max_degree", "spectral_radius"]),
            ("spectral_radius", ["max_degree", "average_degree"]),
        ],
    },
    "advanced_spectral": {
        "title": "Higher-Order Spectral Invariants & Non-Linear Envelopes",
        "description": "Explores signless Laplacian q_1, normalized Laplacian spectral gap, Estrada index EE, graph energy E, and Nordhaus-Gaddum sums.",
        "pairs": [
            ("signless_laplacian_spectral_radius", "max_degree"),
            ("signless_laplacian_spectral_radius", "spectral_radius"),
            ("estrada_index", "spectral_radius"),
            ("graph_energy", "spectral_radius"),
            ("normalized_laplacian_spectral_gap", "order"),
        ],
        "triads": [
            ("signless_laplacian_spectral_radius", ["max_degree", "spectral_radius"]),
            ("estrada_index", ["order", "spectral_radius"]),
            ("graph_energy", ["order", "size"]),
        ],
    },
    "extremal_coloring": {
        "title": "Extremal Coloring & Degree Inequalities",
        "description": "Explores upper and lower bounds on chromatic number relative to local degrees, cliques, and girth.",
        "pairs": [
            ("chromatic_number", "max_degree"),
            ("chromatic_number", "clique_number"),
            ("chromatic_number", "average_degree"),
            ("chromatic_number", "density"),
        ],
        "triads": [
            ("chromatic_number", ["max_degree", "clique_number"]),
            ("chromatic_number", ["average_degree", "clique_number"]),
            ("chromatic_number", ["density", "clique_number"]),
            ("chromatic_number", ["max_degree", "clique_number"], "is_triangle_free"),
            ("chromatic_number", ["max_degree", "clique_number"], "is_bipartite"),
        ],
    },
    "independence_clique": {
        "title": "Ramsey, Independence, & Clique Bounds",
        "description": "Explores trade-offs between independence number, clique number, order, and size.",
        "pairs": [
            ("independence_number", "order"),
            ("independence_number", "max_degree"),
            ("clique_number", "order"),
            ("size", "order"),
        ],
        "triads": [
            ("size", ["order", "clique_number"]),
            ("independence_number", ["order", "max_degree"]),
            ("clique_number", ["order", "independence_number"]),
            ("size", ["order", "clique_number"], "is_triangle_free"),
        ],
    },
    "metric_topological": {
        "title": "Metric & Topological Graph Theory Invariants",
        "description": "Explores girth g(G), diameter D(G), radius R(G), triangle count T(G), density rho(G), and order n (Moore bounds, diameter-clique trade-offs, triangle-free packing).",
        "pairs": [
            ("diameter", "radius"),
            ("radius", "diameter"),
            ("girth", "diameter"),
            ("triangle_count", "order"),
            ("triangle_count", "size"),
            ("diameter", "order"),
            ("density", "order"),
            ("girth", "order"),
            ("diameter", "clique_number"),
        ],
        "triads": [
            ("order", ["diameter", "max_degree"]),
            ("order", ["girth", "min_degree"]),
            ("diameter", ["order", "clique_number"]),
            ("radius", ["diameter", "order"]),
            ("triangle_count", ["order", "size"]),
            ("triangle_count", ["order", "max_degree"]),
            ("size", ["order", "density"]),
            ("triangle_count", ["order", "size"], "is_triangle_free"),
            ("diameter", ["order", "radius"], "is_connected"),
            ("order", ["diameter", "max_degree"], "is_connected"),
            ("order", ["girth", "min_degree"], "is_triangle_free"),
        ],
    },
    "chemical_energy": {
        "title": "Chemical Graph Theory, Energy & Estrada Index",
        "description": "Explores graph energy E(G), Estrada index EE(G), spectral spread s(G), order n, size m, and spectral radius lambda_1 (Koolen-Moulton bounds, Gutman bounds, EE vs E).",
        "pairs": [
            ("graph_energy", "order"),
            ("graph_energy", "size"),
            ("graph_energy", "spectral_radius"),
            ("estrada_index", "graph_energy"),
            ("estrada_index", "spectral_radius"),
            ("spectral_spread", "spectral_radius"),
            ("spectral_spread", "max_degree"),
            ("spectral_spread", "order"),
        ],
        "triads": [
            ("graph_energy", ["order", "size"]),
            ("graph_energy", ["order", "spectral_radius"]),
            ("estrada_index", ["order", "spectral_radius"]),
            ("estrada_index", ["order", "graph_energy"]),
            ("spectral_spread", ["spectral_radius", "max_degree"]),
            ("spectral_spread", ["order", "spectral_radius"]),
            ("graph_energy", ["order", "size"], "is_connected"),
        ],
    },
    "expander_codes": {
        "title": "Unique Neighbors & Binary Adjacency Codes",
        "description": "Studies C(G)=ker A(G) over GF(2), code distance and dimension, and unique-neighbor guarantees.",
        "proposal_family": "expander_codes",
        "focus_invariants": ["parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"],
        "bridge_invariants": ["order", "size", "min_degree", "max_degree", "normalized_laplacian_spectral_gap"],
        "pairs": [("parity_code_distance", "unique_neighbor_radius"),
                  ("parity_code_dimension", "order"), ("unique_neighbor_radius", "min_degree")],
        "triads": [("parity_code_distance", ["unique_neighbor_radius", "order"]),
                   ("parity_code_dimension", ["order", "max_degree"]),
                   ("parity_code_distance", ["unique_neighbor_radius", "min_degree"], "is_regular")],
    },
}

from autonomous_math.conjecturing.model_proposals import campaign_family, family_variables
for _name, _preset in CAMPAIGN_PRESETS.items():
    _family = campaign_family(_name)
    _preset.update(campaign=_name, proposal_family=_name,
                   focus_invariants=_family["focus"], bridge_invariants=_family["bridges"])


def _campaign_eligible(candidate, options, atlas=None):
    focus = set(options.get("focus_invariants", []))
    if not focus:
        return True
    conclusion, variables = family_variables(candidate)
    allowed = focus | set(options.get("bridge_invariants", []))
    # Existing callers supplying only a focus retain their original behavior.
    within = not options.get("campaign") or variables <= allowed
    if conclusion & focus and within:
        return True
    # A helper may use another invariant only for an actual active-campaign parent.
    for identifier in candidate.metadata.get("helper_for", []):
        row = (atlas or {}).get("theorems", {}).get(identifier, {})
        if row.get("conjecture"):
            parent = Conjecture.from_dict(row["conjecture"])
            parent_conclusion, parent_variables = family_variables(parent)
            if parent_conclusion & focus and (not options.get("campaign") or parent_variables <= allowed):
                return True
    return False


def _prepare_campaign_rotation(atlas, presets):
    schedule = [p.get("campaign", "unscoped") for p in presets]
    if (any(name not in CAMPAIGN_PRESETS and not (name == "unscoped" and len(schedule) == 1) for name in schedule)
        or len(set(schedule)) != len(schedule)):
        raise ValueError("Campaign schedule must contain distinct known campaigns")
    previous = atlas.get("campaign_rotation", {})
    if previous.get("revision") != CAMPAIGN_ROTATION_REVISION or previous.get("schedule") != schedule:
        if previous:
            atlas.setdefault("campaign_period_history", []).append({
                "rotation": copy.deepcopy(previous), "progress": copy.deepcopy(atlas.get("campaign_progress", {})),
                "history": copy.deepcopy(atlas.get("campaign_history", []))})
            atlas["campaign_period_history"] = atlas["campaign_period_history"][-20:]
        atlas["campaign_rotation"] = {"revision": CAMPAIGN_ROTATION_REVISION, "schedule": schedule,
            "next_index": 0, "started_checkpoint": atlas["total_iterations"], "started_at": time.time()}
        atlas["campaign_progress"] = {}
        atlas["campaign_history"] = []
    cursor = atlas["campaign_rotation"].get("next_index")
    if type(cursor) is not int or not 0 <= cursor < len(schedule):
        raise ValueError("Invalid committed campaign cursor")


def _campaign_view(atlas, current=None):
    rotation = copy.deepcopy(atlas["campaign_rotation"])
    schedule, cursor = rotation["schedule"], rotation["next_index"]
    rotation.update(current=current, next=schedule[(cursor + (current is not None)) % len(schedule)])
    return rotation


def _commit_campaign_batch(working, before, campaign, started_at):
    """Attribute only this committed batch's exact additions, never the shared library."""
    previous = {key for key, row in before["theorems"].items() if row.get("status") == "LEAN_CERTIFIED"}
    added = sorted(key for key, row in working["theorems"].items()
                   if row.get("status") == "LEAN_CERTIFIED" and key not in previous)
    for identifier in added:
        working["theorems"][identifier]["certified_campaign"] = campaign
    metrics = working.get("batch_metrics", {})
    batch = {"campaign": campaign, "checkpoint": working["total_iterations"], "started_at": started_at,
        "completed_at": time.time(), "certified_added_ids": added,
        "generated_candidates": metrics.get("generated_candidates", 0), "screened_candidates": metrics.get("screened", 0),
        "proof_targets": metrics.get("proof_targets", 0), "unsupported_lean_candidates": metrics.get("unsupported_targets", 0)}
    progress = working.setdefault("campaign_progress", {}).setdefault(campaign, {"completed_batches": 0,
        "generated_candidates": 0, "screened_candidates": 0, "proof_targets": 0, "certified_added": 0,
        "certified_ids": [], "unsupported_lean_candidates": 0})
    progress["completed_batches"] += 1
    for field in ("generated_candidates", "screened_candidates", "proof_targets", "unsupported_lean_candidates"):
        progress[field] += batch[field]
    progress["certified_ids"] = sorted(set(progress["certified_ids"]) | set(added))
    progress.update(certified_added=len(progress["certified_ids"]), last_checkpoint=working["total_iterations"],
                    last_completed_at=batch["completed_at"])
    working.setdefault("campaign_history", []).append(batch)
    working["campaign_history"] = working["campaign_history"][-100:]
    rotation = working["campaign_rotation"]
    rotation["next_index"] = (rotation["next_index"] + 1) % len(rotation["schedule"])
    metrics.update(campaign=campaign, certified_added_ids=added, elapsed_sec=batch["completed_at"] - started_at)
@lru_cache(maxsize=1)
def _holdouts():
    from autonomous_math.sieve.adversarial_holdouts import holdout_graphs
    from autonomous_math.core.graph_types import GraphInstance
    return tuple(GraphInstance.from_networkx(g) for g in holdout_graphs())


def independent_holdout(conjecture, check=lambda: None):
    tested = 0
    visited = 0
    undefined = 0
    for graph in _holdouts():
        check()
        visited += 1
        try:
            if not conjecture.applies(graph):
                continue
            names = sorted(conjecture.lhs_expr.variables | conjecture.rhs_expr.variables)
            invariants = GraphInvariantEvaluator.evaluate(graph, names)
            holds, lhs, rhs = conjecture.evaluate(graph, invariants=invariants)
        except (ArithmeticError, ValueError, TimeoutError):
            undefined += 1
            continue
        if math.isnan(lhs) or math.isnan(rhs):
            undefined += 1
            continue
        tested += 1
        if not holds:
            cert = CounterexampleCertificate.from_counterexample_graph(graph, conjecture,
                witness={"type": "direct_evaluation", "details": {"lhs_value": lhs, "rhs_value": rhs}})
            return SieveResult(status="REFUTED", conjecture=conjecture,
                tested_instances_count=visited, checked_instances_count=tested,
                undefined_instances_count=undefined, counterexample_certificate=cert)
    return SieveResult(status="SURVIVED" if tested else "INCONCLUSIVE", conjecture=conjecture,
        tested_instances_count=visited, checked_instances_count=tested, undefined_instances_count=undefined)


def _generate(preset, pair_limit, triad_limit):
    gen = ConjectureGenerator()
    focus = set(preset.get("focus_invariants", []))
    if preset.get("proposal_family") == "expander_codes":
        InstanceDatabase().ensure_code_columns()
        from autonomous_math.prover.trusted_lean import expander_code_candidates
        result = expander_code_candidates()
    else:
        result = gen.generate_archetypal()
        result.extend(gen.generate_advanced_spectral_candidates())
        result.extend(gen.generate_metric_candidates())
        result.extend(gen.generate_chemical_candidates())
        # Elementary seeds enter only the campaign whose scope includes them.
        result.append(Conjecture.create(id="chromatic_le_order", lhs=InvariantNode("chromatic_number"),
                                       rel="<=", rhs=InvariantNode("order")))
        from autonomous_math.prover.trusted_lean import bootstrap_candidates
        result.extend(bootstrap_candidates())
    for y, x in preset["pairs"]:
        result.extend(gen.generate_parametric_bounds(y, x)[:pair_limit])
        result.extend(gen.generate_nonlinear_bounds(y, x)[:pair_limit])
    for triad in preset.get("triads", []):
        y, xs = triad[:2]
        result.extend(gen.generate_multivariate_bounds(target_y=y, target_xs=xs,
            guard=triad[2] if len(triad)>2 else None)[:triad_limit])
    if focus:
        result = [c for c in result if _campaign_eligible(c, preset)]
    for i, candidate in enumerate(result):
        if candidate.id.startswith("hull_") or candidate.id.startswith("hull3d_"):
            identity = {k: candidate.to_dict()[k] for k in ("lhs_expr", "rel", "rhs_expr", "guard_predicate")}
            suffix = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()[:12]
            result[i] = candidate.model_copy(update={"id": candidate.id + "_" + suffix})
        if preset.get("campaign"):
            result[i].metadata["campaign"] = preset["campaign"]
    return result


def reassess_survivors(atlas, check=lambda: None):
    """Apply a changed challenger to old candidates before learning from the snapshot."""
    from autonomous_math.sieve.adversarial_holdouts import HOLDOUT_REVISION
    if atlas.get("holdout_revision") == HOLDOUT_REVISION:
        return 0
    refuted = 0
    for record in atlas.get("theorems", {}).values():
        check()
        if record.get("status") not in {"EMPIRICAL_SURVIVOR", "LEAN_CERTIFIED"} or not record.get("conjecture"):
            continue
        candidate = Conjecture.from_dict(record["conjecture"])
        result = independent_holdout(candidate, check)
        record.update(holdout_tested=result.checked_instances_count, holdout_status=result.status,
                      holdout_revision=HOLDOUT_REVISION)
        if result.is_refuted:
            if record.get("status") == "LEAN_CERTIFIED":
                raise ValueError(f"Challenger contradicts a checked theorem: {candidate.id}")
            cert = result.counterexample_certificate
            valid, errors = CounterexampleCertificateVerifier.verify_with_details(cert, candidate)
            if not valid:
                raise ValueError(f"Invalid reassessment certificate for {candidate.id}: {errors}")
            record.update(status="REFUTED", counterexample=cert.to_dict(), lean_proof=None,
                          reassessed_at=time.time())
            atlas.setdefault("recent_refutations", []).append(copy.deepcopy(record))
            refuted += 1
        elif not result.is_survived:
            record["status"] = "INCONCLUSIVE"
    atlas["total_refuted"] = atlas.get("total_refuted", 0) + refuted
    atlas["holdout_revision"] = HOLDOUT_REVISION
    atlas["challenger_reassessment"] = {"revision": HOLDOUT_REVISION, "new_refutations": refuted}
    return refuted


def replay_counterexamples(atlas, *, deferred=None, check=None):
    """Feed independently checked boundary graphs into the next generation and sieve."""
    from autonomous_math.core.graph_types import GraphInstance
    db = InstanceDatabase()
    seen = {g.canonical_hash for g in db._cached_gi}
    added = 0
    for record in atlas.get("theorems", {}).values():
        if check is not None:
            check()
        if not record.get("counterexample") or not record.get("conjecture"):
            continue
        candidate = Conjecture.from_dict(record["conjecture"])
        attempt = record.get("proof_attempt") or {}
        if attempt.get("status") == "REFUTED":
            if record["counterexample"] != attempt.get("counterexample_certificate") or record.get("lean_proof"):
                raise ValueError(f"Contradictory saved prover refutation {record['id']}")
            try:
                cert = _verified_prover_refutation(attempt, candidate)
            except TimeoutError as exc:
                if check is not None:
                    check()
                # Preserve the historical refutation, but do not learn from a
                # certificate whose current bounded replay is inconclusive.
                graph = GraphInstance.from_networkx(
                    CounterexampleCertificate.from_dict(record["counterexample"]).to_networkx())
                item = {"id": record["id"], "graph_hash": graph.canonical_hash,
                    "order": graph.order, "size": graph.size, "reason": str(exc),
                    "stage": "certificate_revalidation",
                    "certificate_sha256": hashlib.sha256(json.dumps(
                        record["counterexample"], sort_keys=True).encode()).hexdigest(),
                    "conjecture_sha256": hashlib.sha256(json.dumps(
                        candidate.to_dict(), sort_keys=True).encode()).hexdigest()}
                if deferred is not None:
                    deferred.append(item)
                logger.warning("Deferred counterexample certificate replay: %s", item)
                continue
        else:
            cert = CounterexampleCertificate.from_dict(record["counterexample"])
            valid, errors = CounterexampleCertificateVerifier.verify_with_details(cert, candidate)
            if not valid:
                raise ValueError(f"Cannot learn from invalid counterexample {record['id']}: {errors}")
        graph = GraphInstance.from_networkx(cert.to_networkx(), name=f"learned_{record['id']}")
        if graph.canonical_hash not in seen:
            try:
                db.add_instance(graph)
            except TimeoutError as exc:
                # Keep the checked refutation; an unfinished invariant is never
                # replaced by a heuristic value or admitted to the sieve cache.
                item = {"id": record["id"], "graph_hash": graph.canonical_hash,
                    "order": graph.order, "size": graph.size, "reason": str(exc),
                    "stage": "catalog_admission",
                    "certificate_sha256": hashlib.sha256(
                        json.dumps(cert.to_dict(), sort_keys=True).encode()).hexdigest()}
                if deferred is not None:
                    deferred.append(item)
                logger.warning("Deferred counterexample catalog admission: %s", item)
                seen.add(graph.canonical_hash)
                continue
            seen.add(graph.canonical_hash)
            added += 1
    return added


def compose_checked_bounds(atlas):
    """Generate transitive targets from compatible certified universal inequalities."""
    bounds = []
    fingerprints = {}
    for record in atlas.get("theorems", {}).values():
        if record.get("status") != "LEAN_CERTIFIED":
            continue
        receipt, _ = validate_receipt(record["lean_proof"]["receipt_path"], record["id"], fingerprints)
        if not receipt:
            continue
        c = Conjecture.from_dict(receipt["conjecture"])
        if c.guard_predicate or c.rel not in {"<=", ">="}:
            continue
        bounds.append((c.lhs_expr, c.rhs_expr, c.id) if c.rel == "<=" else (c.rhs_expr, c.lhs_expr, c.id))
    result = {}
    for left, middle, first in bounds:
        for other_middle, right, second in bounds:
            if middle.to_dict() != other_middle.to_dict() or left.to_dict() == right.to_dict():
                continue
            identity = json.dumps([left.to_dict(), right.to_dict()], sort_keys=True)
            key = hashlib.sha256(identity.encode()).hexdigest()[:16]
            result[key] = Conjecture.create(id=f"composed_{key}", lhs=left, rel="<=", rhs=right,
                metadata={"origin": "checked_transitivity", "parents": [first, second]})
            if len(result) == 20:
                return list(result.values())
    return list(result.values())


def _candidate_key(candidate):
    """A mathematical identity independent of labels and explanatory metadata."""
    left, right, relation = candidate.lhs_expr.canonical_key, candidate.rhs_expr.canonical_key, candidate.rel
    if relation in {">=", ">"}:
        left, right, relation = right, left, {">=": "<=", ">": "<"}[relation]
    guard = candidate.to_dict()["guard_predicate"]
    def normalize_guard(value):
        if not value:
            return None
        value = GuardPredicate.from_dict(value).to_dict()
        if value["predicate_type"] == "universal":
            return None
        if value["predicate_type"] == "conjunction":
            guards = [g for g in (normalize_guard(child) for child in value.get("guards") or []) if g]
            if not guards:
                return None
            value["guards"] = sorted(guards, key=lambda item: json.dumps(item, sort_keys=True))
        return value
    guard = normalize_guard(guard)
    return json.dumps([left, relation, right, guard], sort_keys=True, allow_nan=False)


def _screening_key(graph_hashes=None):
    from autonomous_math.sieve.adversarial_holdouts import HOLDOUT_REVISION
    paths = [Path(__file__), REPO_ROOT / "autonomous_math/core/invariants.py",
             REPO_ROOT / "autonomous_math/core/expander_codes.py",
             REPO_ROOT / "autonomous_math/core/ast.py", REPO_ROOT / "autonomous_math/sieve/instance_db.py",
             REPO_ROOT / "autonomous_math/sieve/adversarial_holdouts.py"]
    if graph_hashes is None:
        graph_hashes = [getattr(g, "canonical_hash", str(g)) for g in InstanceDatabase()._cached_gi]
    payload = [HOLDOUT_REVISION, [hashlib.sha256(p.read_bytes()).hexdigest() for p in paths], sorted(graph_hashes)]
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


def _snapshot(atlas):
    records = atlas.get("theorems", {})
    return {"certified": [copy.deepcopy(r) for r in records.values() if r.get("status") == "LEAN_CERTIFIED"],
            "boundaries": [copy.deepcopy(r) for r in records.values() if r.get("counterexample")],
            "flywheel_lemmas": copy.deepcopy(atlas.get("flywheel_lemmas", [])),
            "invariant_fertility": copy.deepcopy(atlas.get("invariant_fertility", {}))}


def _flywheel(snapshot, directory):
    from autonomous_math.prover.flywheel import FlywheelLemma
    wheel = LemmaFlywheel(storage_path=Path(directory) / "flywheel_lemmas.json")
    wheel.lemmas = {}
    wheel.feedback.invariant_fertility = copy.deepcopy(snapshot.get("invariant_fertility", {}))
    saved = {item["lemma_id"]: item for item in snapshot.get("flywheel_lemmas", [])}
    fingerprints = {}
    for record in sorted(snapshot.get("certified", []), key=lambda r: r["id"]):
        receipt, error = validate_receipt(record["lean_proof"]["receipt_path"], record["id"], fingerprints)
        if not receipt or receipt.get("conjecture") != record.get("conjecture"):
            raise ValueError(f"Invalid committed proof {record['id']}: {error}")
        if record["id"] in saved:
            wheel.lemmas[record["id"]] = FlywheelLemma(**saved[record["id"]])
        else:
            from autonomous_math.prover.trusted_lean import render_guard
            c = Conjecture.from_dict(record["conjecture"])
            wheel.lemmas[record["id"]] = FlywheelLemma(lemma_id=c.id, statement=c.statement,
                lean_name=receipt["theorem_name"], lean_prop="", tactic=receipt["tactic"],
                invariants=sorted(c.lhs_expr.variables | c.rhs_expr.variables),
                receipt_path=record["lean_proof"]["receipt_path"], guard=render_guard(c.guard_predicate))
        # Scheduling hints are outside the certified AST and cannot supply premises.
        wheel.lemmas[record["id"]].helper_for = sorted(set(record.get("helper_for", [])) |
            set(record["conjecture"].get("metadata", {}).get("helper_for", [])))
    return wheel


def _synthesizer(options):
    if options["proof_backend"] == "none":
        return None
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    return CodexProofSynthesizer(workspace_dir=REPO_ROOT / "certified_lean", model=options["model"],
        reasoning_effort=options.get("reasoning_effort"),
        max_rounds=options["model_rounds"], timeout_per_request=options["model_request_timeout"])


def _proof_budget(options):
    return 50.0 + (options["model_rounds"] * (options["model_request_timeout"]+10.0+getattr(LeanProofSearch, "GENERATED_RETRY_TIMEOUT_SEC", 30.0))
                   if options["proof_backend"] == "codex" else 0.0)


def _prover(snapshot, directory, options):
    return LeanProofSearch(flywheel=_flywheel(snapshot, directory), max_attempts=4,
        auto_register_flywheel=False, synthesizer=_synthesizer(options),
        total_timeout_sec=_proof_budget(options))


def _sieve_delta(candidates, check):
    db, crosschecker = InstanceDatabase(), LiteratureCrossChecker()
    from autonomous_math.prover.trusted_lean import expander_code_candidates
    known_codes = {_candidate_key(c) for c in expander_code_candidates()}
    records = []
    for candidate in candidates:
        check()
        catalog = db.sieve_conjecture(candidate)
        result, holdout = catalog, None
        if result.is_survived:
            holdout = independent_holdout(candidate, check)
            result = holdout
        record = {"id": candidate.id, "statement": candidate.statement, "conjecture": candidate.to_dict(),
            "status": "EMPIRICAL_SURVIVOR" if result.is_survived else "INCONCLUSIVE", "lean_proof": None,
            "guard": candidate.to_dict()["guard_predicate"], "novelty_status": "UNKNOWN_IN_LITERATURE",
            "novelty_score": 0.0, "catalog_tested": catalog.checked_instances_count,
            "catalog_visited": catalog.tested_instances_count, "undefined_instances": catalog.undefined_instances_count,
            "holdout_tested": holdout.checked_instances_count if holdout else 0,
            "holdout_status": holdout.status if holdout else "NOT_RUN"}
        if result.is_refuted:
            record.update(status="REFUTED", counterexample=result.counterexample_certificate.to_dict())
        elif result.is_survived:
            if _candidate_key(candidate) in known_codes:
                record.update(novelty_status="TEXTBOOK_FOLKLORE", matched_theorem=None)
            else:
                report = crosschecker.cross_check(candidate, online=False)
                record.update(novelty_status=report.status.value,
                    matched_theorem=report.matched_theorem.model_dump() if report.matched_theorem else None)
        records.append(record)
    return records


def _verified_prover_refutation(attempt, candidate):
    """A worker/model label cannot refute a claim without exact certificate replay."""
    if (attempt.get("status") != "REFUTED" or attempt.get("is_machine_checked") is not False
        or attempt.get("conjecture_id") != candidate.id
        or any(attempt.get(key) for key in ("receipt_path", "verified_file_path", "successful_tactic", "proof_origin"))):
        raise ValueError("Contradictory or mismatched prover refutation")
    from autonomous_math.sieve.model_counterexamples import verify_model_counterexample_certificate
    return verify_model_counterexample_certificate(attempt.get("counterexample_certificate"), candidate)


def _defer_prover_refutation(record, candidate, error, replay_stage):
    """Retain an inconclusive witness without publishing or learning a refutation."""
    from autonomous_math.core.graph_types import GraphInstance
    record = copy.deepcopy(record)
    attempt = record["proof_attempt"]
    certificate = attempt["counterexample_certificate"]
    graph = GraphInstance.from_networkx(CounterexampleCertificate.from_dict(certificate).to_networkx())
    attempt.update(status="UNRESOLVED", counterexample_certificate=None,
        deferred_counterexample_certificate=certificate,
        error_message=f"Prover refutation replay deferred after verifier timeout: {error}")
    attempt.setdefault("diagnostics", []).append({"phase": "proof_refutation_replay",
        "replay_stage": replay_stage, "exit_code": 124, "failure_kind": "verifier_timeout",
        "compiler_launched": False, "reason": str(error), "graph_hash": graph.canonical_hash,
        "order": graph.order, "size": graph.size,
        "certificate_sha256": hashlib.sha256(json.dumps(certificate, sort_keys=True).encode()).hexdigest(),
        "conjecture_sha256": hashlib.sha256(json.dumps(candidate.to_dict(), sort_keys=True).encode()).hexdigest()})
    record.pop("counterexample", None)
    logger.warning("Deferred proof-stage refutation replay: %s", attempt["diagnostics"][-1])
    return record


def _run_job(job, snapshot, options, deadline, active, check):
    directory = Path(job["directory"])
    directory.mkdir(parents=True, exist_ok=True)
    if job["kind"] == "planning":
        random.setstate(job["rng_state"])
        before = {r["id"]: r for r in job["records"]}
        planning = {"theorems": copy.deepcopy(before), "holdout_revision": job.get("holdout_revision"),
                    "total_refuted": 0, "recent_refutations": []}
        reassess_survivors(planning, check)
        replay = {r["id"]: r for r in snapshot["boundaries"]}
        replay.update({r["id"]: r for r in planning["recent_refutations"]})
        deferred = []
        added = replay_counterexamples({"theorems": replay}, deferred=deferred, check=check)
        check()
        candidates = _generate(job["preset"], job["pair_limit"], job["triad_limit"])
        candidates.extend(compose_checked_bounds(planning))
        database = InstanceDatabase()
        return {"job_id": job["job_id"], "kind": "planning", "candidates": [c.to_dict() for c in candidates],
            "records": [r for identity, r in planning["theorems"].items() if r != before[identity]],
            "holdout_revision": planning["holdout_revision"],
            "challenger_reassessment": planning.get("challenger_reassessment"),
            "replayed_boundary_graphs": added,
            "deferred_counterexample_graphs": deferred,
            "catalog_graph_hashes": [g.canonical_hash for g in database._cached_gi],
            "catalog_graphs": len(database._cached_gi), "invariants_tracked": len(database._cached_matrix),
            "random_state": random.getstate(),
            "code_catalog": database.ensure_code_columns() if job["preset"].get("proposal_family") == "expander_codes" else None}
    if job["kind"] == "proposal":
        from autonomous_math.conjecturing.model_proposals import propose_candidates
        synthesizer = _synthesizer(options)
        active.append(synthesizer)
        candidates, trace = propose_candidates(synthesizer, job["context"], directory,
                                              deadline, options["model_candidates"])
        return {"job_id": job["job_id"], "kind": "proposal", "candidates": [c.to_dict() for c in candidates], "trace": trace}
    candidates = [Conjecture.from_dict(c) for c in job["candidates"]]
    if job["kind"] == "sieve":
        deferred = []
        if options.get("replay_boundary", True):
            replay_counterexamples({"theorems": {r["id"]: r for r in snapshot["boundaries"]}},
                                   deferred=deferred, check=check)
        atomic_save_json({"deferred_counterexample_graphs": deferred}, directory / "boundary_replay.json")
        if options.get("research_family") == "expander_codes":
            InstanceDatabase().ensure_code_columns()
        return {"job_id": job["job_id"], "kind": "sieve", "records": _sieve_delta(candidates, check),
                "catalog_graph_hashes": [g.canonical_hash for g in InstanceDatabase()._cached_gi],
                "deferred_counterexample_graphs": deferred}
    if job["kind"] != "proof":
        raise ValueError("Unknown research job")
    # Routine helpers can still earn their own certificate, using only local
    # tactics and checked library reuse. They never consume another AI request.
    proof_options = dict(options, proof_backend="none") if job.get("local_only") else options
    prover = _prover(snapshot, directory, proof_options)
    active.append(prover)
    records = []
    for candidate in candidates:
        remaining = deadline-time.monotonic()-15.0
        if remaining <= 0:
            from autonomous_math.prover.lean_prover import LeanVerificationResult
            verification = LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=0,
                error_message="Shared proof budget exhausted before this target",
                diagnostics=[{"exit_code": 124, "stage": "shared_budget"}])
        else:
            check()
            verification = prover.prove_conjecture(candidate, output_dir=directory / "verified",
                total_timeout_sec=min(_proof_budget(proof_options), remaining))
        if verification.status in {"ERROR", "TOOLCHAIN_UNAVAILABLE"}:
            raise RuntimeError(verification.error_message)
        record = {"id": candidate.id, "conjecture": candidate.to_dict(),
                  "proof_attempt": verification.to_dict(), "proof_search_key": job["search_keys"][candidate.id]}
        if verification.status == "REFUTED":
            try:
                _verified_prover_refutation(record["proof_attempt"], candidate)
            except TimeoutError as exc:
                check()
                record = _defer_prover_refutation(record, candidate, exc, "worker")
            else:
                record["counterexample"] = record["proof_attempt"]["counterexample_certificate"]
        elif verification.is_proven:
            record["lean_proof"] = {"receipt_path": str(verification.receipt_path)}
        records.append(record)
    return {"job_id": job["job_id"], "kind": "proof", "records": records}


def _job_worker(connection, job, snapshot, options, budget):
    active, finished, send_lock = [], threading.Event(), threading.Lock()
    def send_message(message):
        with send_lock:
            connection.send(message)
    def terminate(signum, frame):
        for item in active:
            cancel = getattr(item, "cancel", None)
            if cancel:
                cancel()
        raise InterruptedError("Research worker termination requested")
    signal.signal(signal.SIGTERM, terminate)
    parent_pid = job.get("owner_pid", os.getppid())
    def monitor():
        last_groups = None
        while not finished.wait(0.2):
            if os.getppid() != parent_pid:
                os.kill(os.getpid(), signal.SIGTERM)
                return
            groups = sorted({gid for item in active for gid in
                             getattr(item, "active_process_groups", lambda: [])()})
            if groups != last_groups:
                try:
                    send_message({"process_groups": groups})
                except (OSError, EOFError):
                    return
                last_groups = groups
    threading.Thread(target=monitor, daemon=True).start()
    deadline = time.monotonic() + budget
    def check():
        if time.monotonic() >= deadline:
            raise TimeoutError("Research job exceeded its budget")
    try:
        if os.getppid() != parent_pid:
            raise InterruptedError("Research parent exited before worker startup")
        result = _run_job(job, snapshot, options, deadline, active, check)
        check()
        # A terminal success promises that all owned activity has finished.
        # Publishing first lets the parent's exit grace interrupt this cleanup.
        for item in active:
            cancel = getattr(item, "cancel", None)
            if cancel:
                cancel()
        active.clear()
        finished.set()
        check()
        send_message({"delta": result})
    except BaseException as exc:
        try:
            send_message({"error": f"{type(exc).__name__}: {exc}"})
        except (BrokenPipeError, EOFError, OSError):
            pass
    finally:
        for item in active:
            cancel = getattr(item, "cancel", None)
            if cancel:
                cancel()
        finished.set()
        connection.close()


def _dispatch_jobs(jobs, snapshot, options, stop, deadline, status, synchronous=False, timing=None):
    """Refill bounded process slots; only the parent merges the private deltas."""
    started = time.monotonic()
    slots = min(1 if synchronous else options["workers"], len(jobs))
    intervals, results, peak = {}, [], 0
    snapshot_hash = hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest() if jobs else None
    for job in jobs:
        job["campaign"] = options.get("campaign")
        job["research_family"] = options.get("research_family")
        atomic_save_json({"job_id": job["job_id"], "kind": job["kind"], "campaign": job["campaign"],
            "research_family": job["research_family"], "focus_invariants": options.get("focus_invariants", []),
            "bridge_invariants": options.get("bridge_invariants", []),
            "candidate_ids": [candidate["id"] for candidate in job.get("candidates", [])],
            "input_snapshot_sha256": snapshot_hash},
            Path(job["directory"]) / "job.json")
    status["batch_progress"] = {"campaign": options.get("campaign"), "kind": jobs[0]["kind"] if jobs else None,
        "jobs_total": len(jobs), "jobs_started": 0, "jobs_completed": 0, "active_workers": 0}

    def check():
        _check_batch_stop(stop, deadline)

    def record_timing():
        elapsed = time.monotonic()-started if jobs else 0.0
        busy = sum(item["finished_sec"]-item["started_sec"] for item in intervals.values())
        if timing is not None:
            # These are occupied process-slot wall times, including startup and
            # reaping, rather than CPU utilization or model-service throughput.
            timing.update(elapsed_sec=elapsed, busy_sec=busy,
                idle_sec=max(0.0, slots*elapsed-busy), slots=slots,
                max_active_workers=peak, jobs_started=len(intervals),
                jobs_completed=len(results), job_timings=intervals)
        status["batch_progress"].update(jobs_started=len(intervals), jobs_completed=len(results), active_workers=0)

    if synchronous:
        try:
            for job in jobs:
                check()
                peak = 1
                interval = {"started_sec": time.monotonic()-started}
                intervals[job["job_id"]] = interval
                status["batch_progress"].update(jobs_started=len(intervals), active_workers=1)
                try:
                    results.append(_run_job(job, snapshot, options, deadline, [], check))
                    status["batch_progress"]["jobs_completed"] = len(results)
                    check()
                finally:
                    interval["finished_sec"] = time.monotonic()-started
            return sorted(results, key=lambda item: item["job_id"])
        finally:
            record_timing()

    import multiprocessing as mp
    from autonomous_math.prover.codex_synthesis import signal_process_group
    context, running, entries, next_job = mp.get_context("spawn"), [], [], 0

    def reap(entry):
        process, errors, forced = entry["process"], [], False
        interrupted = None
        reap_started = time.monotonic()
        try:
            if entry["done"]:
                # A successful delta is not an exited process. Await teardown
                # under the existing batch deadline, preserving cancellation.
                while process.is_alive():
                    try:
                        check()
                    except InterruptedError as exc:
                        interrupted = exc
                        break
                    process.join(timeout=min(0.1, max(0.0, deadline-time.monotonic())))
            if process.is_alive():
                forced = True
                process.terminate()
            process.join(timeout=2)
            if process.is_alive():
                forced = True
                process.kill()
                process.join(timeout=2)
            if process.is_alive():
                raise RuntimeError(f"Worker {entry['job']['job_id']} remained alive after termination")
            if entry["done"] and process.exitcode != 0 and interrupted is None:
                raise RuntimeError(f"Worker {entry['job']['job_id']} failed after returning its delta (exit={process.exitcode})")
        except Exception as exc:
            errors.append(exc)
        # A received delta does not guarantee that the worker's finally block
        # finished. If forced to stop it, clean its reported child groups too.
        for gid in entry["groups"] if not entry["done"] or forced or process.exitcode != 0 else []:
            try:
                signal_process_group(gid, signal.SIGKILL)
            except Exception as exc:
                exc.add_note(f"Cleanup of reported process group {gid} for {entry['job']['job_id']}")
                errors.append(exc)
        entry["receive"].close()
        entry["reaped"] = True
        interval = intervals[entry["job"]["job_id"]]
        interval.update(finished_sec=time.monotonic()-started,
            exit_code=process.exitcode, forced_termination=forced,
            reaping_sec=time.monotonic()-reap_started)
        if "delta_received_sec" in interval:
            interval["delta_to_exit_sec"] = interval["finished_sec"]-interval["delta_received_sec"]
        if errors:
            raise RuntimeError("Research worker cleanup failed: " + "; ".join(str(error) for error in errors)) from errors[0]
        if interrupted is not None:
            raise interrupted
        if entry["done"]:
            check()

    try:
        while next_job < len(jobs) or running:
            check()
            while next_job < len(jobs) and len(running) < slots:
                check()  # Cancellation must not admit a queued target.
                job = jobs[next_job]
                receive, send = context.Pipe(duplex=False)
                worker_job = dict(job, owner_pid=os.getpid())
                process = context.Process(target=_job_worker, args=(send, worker_job, snapshot, options,
                                           max(0.01, deadline-time.monotonic())))
                launched = time.monotonic()-started
                try:
                    process.start()
                except BaseException:
                    receive.close()
                    raise
                finally:
                    send.close()
                entry = {"process": process, "receive": receive, "job": job,
                         "groups": set(), "done": False, "reaped": False}
                entries.append(entry)
                running.append(entry)
                intervals[job["job_id"]] = {"started_sec": launched}
                status["batch_progress"].update(jobs_started=len(intervals), active_workers=len(running))
                next_job += 1
                peak = max(peak, len(running))
            progressed = False
            for entry in list(running):
                receive, process = entry["receive"], entry["process"]
                if receive.poll(0.02):
                    try:
                        message = receive.recv()
                    except EOFError:
                        raise RuntimeError(f"Worker {entry['job']['job_id']} exited without a delta")
                    progressed = True
                    if "process_groups" in message:
                        entry["groups"] = set(message["process_groups"])
                    elif "error" in message:
                        raise RuntimeError(message["error"])
                    elif "delta" in message:
                        delta = message["delta"]
                        if delta.get("job_id") != entry["job"]["job_id"] or delta.get("kind") != entry["job"]["kind"]:
                            raise ValueError("Worker delta does not match its assigned job")
                        results.append(delta)
                        status["batch_progress"]["jobs_completed"] = len(results)
                        entry["done"] = True
                        intervals[entry["job"]["job_id"]]["delta_received_sec"] = time.monotonic()-started
                        reap(entry)  # Release an actual process slot before refilling it.
                        running.remove(entry)
                        status["batch_progress"]["active_workers"] = len(running)
                elif not process.is_alive():
                    raise RuntimeError(f"Worker {entry['job']['job_id']} exited without a delta (exit={process.exitcode})")
            if not progressed:
                threading.Event().wait(0.02)
        return sorted(results, key=lambda item: item["job_id"])
    finally:
        cleanup_errors = []
        for entry in entries:
            if entry["reaped"]:
                continue
            try:
                reap(entry)
            except Exception as exc:
                cleanup_errors.append(exc)
        record_timing()
        if cleanup_errors:
            raise RuntimeError("Research worker cleanup failed: " + "; ".join(str(error) for error in cleanup_errors)) from cleanup_errors[0]


def _jobs(kind, candidates, directory, workers, search_keys=None):
    count = len(candidates) if kind == "proof" else min(workers, len(candidates))
    return [{"job_id": f"{kind}-{index:02d}", "kind": kind,
             "directory": str(Path(directory) / f"{kind}-{index:02d}"),
             "candidates": [c.to_dict() for c in candidates[index::count]],
             "search_keys": search_keys or {}} for index in range(count)]


def _validated_delta_records(deltas, jobs, check=None):
    assigned = {job["job_id"]: job for job in jobs}
    if len(deltas) != len(assigned) or {d["job_id"] for d in deltas} != set(assigned):
        raise ValueError("Missing or duplicate worker delta")
    validated = []
    fingerprints = {}
    for delta in sorted(deltas, key=lambda d: d["job_id"]):
        job = assigned[delta["job_id"]]
        if delta.get("kind") != job["kind"]:
            raise ValueError("Worker changed its job kind")
        expected = {c["id"]: c for c in job["candidates"]}
        records = delta.get("records", [])
        if len(records) != len(expected) or {r["id"] for r in records} != set(expected):
            raise ValueError("Worker returned unassigned or duplicate claims")
        for record in records:
            if check is not None:
                check()
            candidate = Conjecture.from_dict(expected[record["id"]])
            if record.get("conjecture") != candidate.to_dict():
                raise ValueError("Worker changed the assigned conjecture")
            if job["kind"] == "sieve":
                if set(record) - {"id", "statement", "conjecture", "status", "lean_proof", "guard",
                    "novelty_status", "novelty_score", "catalog_tested", "catalog_visited", "undefined_instances",
                    "holdout_tested", "holdout_status", "counterexample", "matched_theorem"}:
                    raise ValueError("Sieve worker returned unassigned state")
                if record.get("lean_proof"):
                    raise ValueError("Sieve worker cannot certify proofs")
                if record.get("status") not in {"EMPIRICAL_SURVIVOR", "REFUTED", "INCONCLUSIVE"}:
                    raise ValueError("Sieve worker returned an invalid status")
                if record.get("status") == "REFUTED":
                    certificate = CounterexampleCertificate.from_dict(record["counterexample"])
                    valid, errors = CounterexampleCertificateVerifier.verify_with_details(certificate, candidate)
                    if not valid:
                        raise ValueError(f"Unverified worker counterexample: {errors}")
            elif job["kind"] == "proof":
                if set(record) - {"id", "conjecture", "proof_attempt", "proof_search_key", "lean_proof", "counterexample"}:
                    raise ValueError("Proof worker returned unassigned state")
                if record.get("proof_search_key") != job["search_keys"][candidate.id]:
                    raise ValueError("Worker changed the proof context")
                proof = record.get("lean_proof")
                attempt = record.get("proof_attempt") or {}
                if attempt.get("status") == "REFUTED":
                    if proof or record.get("counterexample") != attempt.get("counterexample_certificate"):
                        raise ValueError("Prover refutation is missing its attached certificate or contradicts a proof")
                    try:
                        _verified_prover_refutation(attempt, candidate)
                    except TimeoutError as exc:
                        if check is not None:
                            check()
                        record = _defer_prover_refutation(record, candidate, exc, "parent")
                elif "counterexample" in record or attempt.get("counterexample_certificate") is not None:
                    raise ValueError("Counterexample attached without a prover refutation")
                if proof:
                    path = Path(proof["receipt_path"]).resolve()
                    if not path.is_relative_to(Path(job["directory"]).resolve()):
                        raise ValueError("Worker receipt is outside its private directory")
                    receipt, errors = validate_receipt(path, candidate.id, fingerprints)
                    if not receipt or receipt.get("conjecture") != candidate.to_dict():
                        raise ValueError(f"Unverified worker proof: {errors}")
                    if any(not Path(receipt[key]).resolve().is_relative_to(Path(job["directory"]).resolve())
                           for key in ("source_path", "challenge_path")):
                        raise ValueError("Worker proof artifacts escaped the private directory")
            validated.append(record)
    return sorted(validated, key=lambda r: r["id"])


PROOF_RETRY_FIELDS = ("next_retry_at", "next_retry_iteration", "proof_retry_count", "proof_retry_reason")


def _proof_retry_reason(attempt):
    if attempt.get("status") in {"MACHINE_CHECKED_PROVEN", "REFUTED"}:
        return None
    if any(d.get("phase") == "proof_refutation_replay" and d.get("failure_kind") == "verifier_timeout"
           for d in attempt.get("diagnostics", [])):
        return "verifier_timeout"
    if attempt.get("status") in {"ERROR", "TOOLCHAIN_UNAVAILABLE"}:
        return "toolchain_error"
    synthesis = attempt.get("synthesis_attempts", [])
    if synthesis:
        # A terminal model answer supersedes timeouts from preliminary fixed tactics.
        reason = {"MODEL_UNKNOWN": "model_unknown", "TIMEOUT": "model_timeout",
                "COMPILER_TIMEOUT": "compiler_timeout", "COMPILER_ADMISSION_TIMEOUT": "compiler_admission_timeout", "ERROR": "model_error",
                "FAILED": "model_error", "CANCELLED": "cancelled"}.get(synthesis[-1].get("status"))
        if reason:
            return reason
        diagnostics = attempt.get("diagnostics", [])
        if (diagnostics and diagnostics[-1].get("phase") == "shared_budget"
                and diagnostics[-1].get("exit_code") == 124
                and diagnostics[-1].get("compiler_launched") is False):
            return "shared_budget_exhausted"
        return None
    if "budget exhausted" in (attempt.get("error_message") or "").lower():
        return "shared_budget_exhausted"
    if any(d.get("failure_kind") == "compiler_admission_timeout" for d in attempt.get("diagnostics", [])):
        return "compiler_admission_timeout"
    if any(d.get("exit_code") == 124 for d in attempt.get("diagnostics", [])):
        return "compiler_timeout"
    return None


def _retryable(attempt):
    return _proof_retry_reason(attempt) is not None


def _clear_proof_retry(record):
    for field in PROOF_RETRY_FIELDS:
        record.pop(field, None)


def _schedule_proof_retry(record, previous_key, iteration):
    if previous_key != record.get("proof_search_key"):
        _clear_proof_retry(record)
    reason = _proof_retry_reason(record.get("proof_attempt") or {})
    if reason is None:
        _clear_proof_retry(record)
        return
    count = min(record.get("proof_retry_count", 0) + 1, 5)
    record.update(proof_retry_count=count, proof_retry_reason=reason,
        next_retry_at=time.time() + min(300 * 2 ** (count - 1), 3600),
        next_retry_iteration=iteration + min(2 ** count, 16))


def _migrate_candidate_identity(atlas):
    """Invalidate legacy negative caches without changing any mathematical statement."""
    previous = atlas.get("candidate_identity_revision")
    if previous == CANDIDATE_IDENTITY_REVISION:
        return
    fields = ("proof_search_key", "proof_search_skipped", "screening_key", *PROOF_RETRY_FIELDS)
    invalidated = []
    for record in atlas.get("theorems", {}).values():
        if record.get("status") in {"LEAN_CERTIFIED", "REFUTED"}:
            continue
        if any(field in record for field in fields):
            invalidated.append(record["id"])
        for field in fields:
            record.pop(field, None)
    atlas["candidate_identity_revision"] = CANDIDATE_IDENTITY_REVISION
    atlas["candidate_identity_migration"] = {"from_revision": previous,
        "to_revision": CANDIDATE_IDENTITY_REVISION, "invalidated_record_ids": sorted(invalidated),
        "invalidated_count": len(invalidated)}


def _coordinate_candidates(candidates, atlas, directory, lean_limit, stop, deadline, status, options,
                           synchronous=False, screen_key=None):
    def check():
        _check_batch_stop(stop, deadline)
    from autonomous_math.prover.trusted_lean import render_challenge
    _migrate_candidate_identity(atlas)
    from autonomous_math.conjecturing.model_proposals import missing_lemma_candidates
    helpers, helper_errors = missing_lemma_candidates(atlas, focus=options.get("focus_invariants", ()))
    candidates = list(candidates) + helpers
    screen_key = screen_key or _screening_key()
    snapshot = _snapshot(atlas)
    existing = {_candidate_key(Conjecture.from_dict(r["conjecture"])): r
                for r in atlas["theorems"].values() if r.get("conjecture")}
    focus = set(options.get("focus_invariants", []))
    if focus:
        candidates = [c for c in candidates if _campaign_eligible(c, options, atlas)]
    generated_count = len(candidates)
    unique = {}
    for candidate in candidates:
        key = _candidate_key(candidate)
        old = existing.get(key)
        if old:
            helper_for = candidate.metadata.get("helper_for", [])
            candidate = Conjecture.from_dict(old["conjecture"])
            if helper_for:
                old["helper_for"] = sorted(set(old.get("helper_for", [])) | set(helper_for))
            if helper_for and old.get("status") != "LEAN_CERTIFIED":
                candidate.metadata["helper_for"] = sorted(set(candidate.metadata.get("helper_for", [])) | set(helper_for))
                old["conjecture"] = candidate.to_dict()
        elif candidate.id in atlas["theorems"] or any(c.id == candidate.id for c in unique.values()):
            candidate = candidate.model_copy(update={"id": candidate.id + "_" + hashlib.sha256(key.encode()).hexdigest()[:12]})
        unique.setdefault(key, candidate)
    # Old survivors are re-screened on a changed catalog even when generation did not rediscover them.
    for key, old in existing.items():
        if old.get("status") in {"EMPIRICAL_SURVIVOR", "INCONCLUSIVE", "UNVERIFIED"}:
            candidate = Conjecture.from_dict(old["conjecture"])
            if _campaign_eligible(candidate, options, atlas):
                unique.setdefault(key, candidate)
    ordered = sorted(unique.values(), key=lambda c: (c.id != "chromatic_le_order",
        c.metadata.get("origin") != "known_foundational_bound",
        c.metadata.get("origin") != "checked_transitivity",
        not bool(c.metadata.get("helper_for")),
        c.metadata.get("origin") != "codex_proposal", c.id))
    screening = [c for c in ordered if not (existing.get(_candidate_key(c), {}).get("status") in {"LEAN_CERTIFIED", "REFUTED"})
                 and existing.get(_candidate_key(c), {}).get("screening_key") != screen_key]
    metrics = {"unique_candidates": len(unique), "sieve_jobs": 0, "proof_jobs": 0,
               "screened": len(screening), "deduplicated": len(candidates)-len({_candidate_key(c) for c in candidates}),
               "cached_screens": len(ordered)-len(screening), "proof_targets": 0, "unsupported_targets": 0,
               "worker_timing": {"sieve": {}, "proof": {}}}
    metrics.update(campaign=options.get("campaign"), generated_candidates=generated_count)
    metrics["missing_lemma_tasks"] = len(helpers)
    metrics["missing_lemma_task_errors"] = helper_errors
    if focus:
        metrics["research_focus"] = sorted(focus)
        metrics["research_family"] = options.get("research_family")
    jobs = _jobs("sieve", screening, directory, options["workers"])
    status["stage"] = "sieve"
    deltas = _dispatch_jobs(jobs, snapshot, options, stop, deadline, status, synchronous,
                           timing=metrics["worker_timing"]["sieve"])
    records = _validated_delta_records(deltas, jobs, check=check)
    screening_keys = {}
    for delta in deltas:
        key = _screening_key(delta["catalog_graph_hashes"]) if "catalog_graph_hashes" in delta else screen_key
        for record in delta["records"]:
            screening_keys[record["id"]] = key
        for item in delta.get("deferred_counterexample_graphs", []):
            if item not in atlas.setdefault("deferred_counterexample_graphs", []):
                atlas["deferred_counterexample_graphs"].append(copy.deepcopy(item))
    metrics["sieve_jobs"] = len(jobs)
    wheel = _flywheel(snapshot, Path(directory) / "scheduler")
    for record in records:
        old = atlas["theorems"].get(record["id"], {})
        is_new = _candidate_key(Conjecture.from_dict(record["conjecture"])) not in existing
        record.update(discovered_iteration=old.get("discovered_iteration", atlas["total_iterations"]+1),
            last_evaluated_iteration=atlas["total_iterations"]+1, timestamp=time.time(),
            screening_key=screening_keys[record["id"]])
        if options.get("campaign"):
            record["last_screened_campaign"] = options["campaign"]
            if old.get("first_campaign"):
                record["first_campaign"] = old["first_campaign"]
            elif is_new:
                record["first_campaign"] = options["campaign"]
        for field in ("proof_attempt", "proof_search_key", "last_proof_attempt_sequence", *PROOF_RETRY_FIELDS):
            if field in old:
                record[field] = old[field]
        if record["status"] == "REFUTED":
            if old.get("status") != "REFUTED":
                atlas["total_refuted"] += 1
                atlas["recent_refutations"].append(copy.deepcopy(record))
                wheel.feedback.record_refutation(Conjecture.from_dict(record["conjecture"]),
                    CounterexampleCertificate.from_dict(record["counterexample"]))
        elif record["status"] == "EMPIRICAL_SURVIVOR" and is_new:
            wheel.feedback.record_sieve_survival(Conjecture.from_dict(record["conjecture"]))
        atlas["theorems"][record["id"]] = record
        atlas["total_conjectures_generated"] += 1
    eligible, keys, parent_prover = [], {}, None
    from autonomous_math.novelty.routine_filter import find_routine_variant
    checked_rows, receipt_fingerprints, checked_receipts = [], {}, {}
    for row in atlas["theorems"].values():
        if row.get("status") != "LEAN_CERTIFIED":
            continue
        receipt, error = validate_receipt((row.get("lean_proof") or {}).get("receipt_path", ""),
                                          row["id"], receipt_fingerprints)
        if receipt and receipt.get("conjecture") == row.get("conjecture"):
            receipt_path = Path(row["lean_proof"]["receipt_path"])
            receipt_bytes = receipt_path.read_bytes()
            if json.loads(receipt_bytes) != receipt:
                continue  # Do not bind an artifact replaced after its validation.
            checked_receipts[row["id"]] = {
                "receipt_path": str(receipt_path),
                "receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest(),
                "conjecture_sha256": hashlib.sha256(json.dumps(receipt["conjecture"], sort_keys=True).encode()).hexdigest(),
                **{key: receipt[key] for key in ("source_sha256", "challenge_sha256", "workspace_sha256",
                                                "lean_binary_sha256", "axioms")},
            }
            checked_rows.append(row)
    routine_helpers = set()
    metrics.update(routine_variants_suppressed=0, routine_helpers_local_only=0, routine_variants=[])
    translator_hash = hashlib.sha256(Path(REPO_ROOT / "autonomous_math/prover/trusted_lean.py").read_bytes()).hexdigest()
    for candidate in ordered:
        record = atlas["theorems"].get(candidate.id, {})
        if record.get("status") != "EMPIRICAL_SURVIVOR":
            continue
        try:
            render_challenge(candidate)
        except ValueError as exc:
            metrics["unsupported_targets"] += 1
            record["formalization"] = {"status": "UNSUPPORTED", "reason": str(exc)}
            if lean_limit != 0:
                key = "unsupported:" + hashlib.sha256((translator_hash+_candidate_key(candidate)).encode()).hexdigest()
                if record.get("proof_search_key") == key:
                    record["proof_search_skipped"] = True
                else:
                    from autonomous_math.prover.lean_prover import LeanVerificationResult
                    record.update(proof_attempt=LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                        theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=0,
                        error_message=str(exc)).to_dict(), proof_search_key=key, proof_search_skipped=False)
            continue
        record.pop("formalization", None)
        if lean_limit == 0:
            continue
        routine = find_routine_variant(candidate, checked_rows)
        if routine:
            routine["parent_bindings"] = {ident: checked_receipts[ident] for ident in routine["parent_ids"]}
            record["routine_variant"] = routine
            metrics["routine_variants"].append({"id": candidate.id, **routine})
            if candidate.metadata.get("helper_for") or record.get("helper_for"):
                routine_helpers.add(candidate.id)
                metrics["routine_helpers_local_only"] += 1
            else:
                record["proof_search_skipped"] = True
                metrics["routine_variants_suppressed"] += 1
                continue
        else:
            record.pop("routine_variant", None)
        record["last_evaluated_iteration"] = atlas["total_iterations"]+1
        prior = record.get("proof_attempt") or {}
        if parent_prover is None:
            parent_prover = _prover(snapshot, Path(directory) / "scheduler", options)
            if not (parent_prover.is_available() and parent_prover.toolchain.ensure_workspace_built()):
                raise RuntimeError("Requested Lean verification requires the ready pinned certified_lean workspace")
        key = parent_prover.search_key(candidate)
        if candidate.id in routine_helpers:
            key = "local_routine_helper:" + key
        if record.get("proof_search_key") != key:
            _clear_proof_retry(record)
        if (record.get("proof_search_key") == key and _retryable(prior)
            and (time.time() < record.get("next_retry_at", 0)
                 or atlas["total_iterations"] + 1 < record.get("next_retry_iteration", 0))):
            record["proof_search_skipped"] = True
            continue
        if record.get("proof_search_key") == key and prior.get("status") == "UNRESOLVED" and not _retryable(prior):
            record["proof_search_skipped"] = True
            continue
        record["proof_search_skipped"] = False
        eligible.append(candidate)
        keys[candidate.id] = key
    priority = {candidate.id: index for index, candidate in enumerate(ordered)}
    def attempt_order(candidate):
        record = atlas["theorems"][candidate.id]
        sequence = record.get("last_proof_attempt_sequence")
        prior = record.get("proof_attempt") or {}
        if sequence is None and (prior.get("attempts_count", 0) or prior.get("synthesis_attempts") or _retryable(prior)):
            sequence = 0  # An older checkpoint tried this target before scheduling metadata existed.
        return sequence is not None, sequence or 0, priority[candidate.id]
    eligible.sort(key=attempt_order)
    proof_candidates = eligible if lean_limit is None else eligible[:lean_limit]
    metrics["proof_targets"] = len(proof_candidates)
    metrics["proof_deferred"] = len(eligible)-len(proof_candidates)
    jobs = _jobs("proof", proof_candidates, directory, options["workers"], keys)
    for job in jobs:
        if all(candidate["id"] in routine_helpers for candidate in job["candidates"]):
            job["local_only"] = True
    status["stage"] = "proof"
    deltas = _dispatch_jobs(jobs, snapshot, options, stop, deadline, status, synchronous,
                           timing=metrics["worker_timing"]["proof"])
    proof_records = _validated_delta_records(deltas, jobs, check=check)
    metrics["proof_jobs"] = len(jobs)
    sequence = max(atlas.get("proof_schedule_sequence", 0),
                   max((r.get("last_proof_attempt_sequence", 0) for r in atlas["theorems"].values()), default=0))
    attempted = {}
    for candidate in proof_candidates:
        sequence += 1
        attempted[candidate.id] = sequence
        if options.get("campaign"):
            atlas["theorems"][candidate.id]["last_proof_campaign"] = options["campaign"]
    atlas["proof_schedule_sequence"] = sequence
    for result in proof_records:
        record = atlas["theorems"][result["id"]]
        was_refuted = record.get("status") == "REFUTED"
        previous_key = record.get("proof_search_key")
        record.update({k: v for k, v in result.items() if k not in {"id", "conjecture"}})
        record["last_proof_attempt_sequence"] = attempted[result["id"]]
        _schedule_proof_retry(record, previous_key, atlas["total_iterations"] + 1)
        if result.get("counterexample"):
            record.update(status="REFUTED", lean_proof=None)
            for field in (*PROOF_RETRY_FIELDS, "proof_search_skipped"):
                record.pop(field, None)
            if not was_refuted:
                atlas["total_refuted"] += 1
                atlas["recent_refutations"].append(copy.deepcopy(record))
                wheel.feedback.record_refutation(Conjecture.from_dict(record["conjecture"]),
                    CounterexampleCertificate.from_dict(record["counterexample"]))
        if result.get("lean_proof"):
            receipt, _ = validate_receipt(result["lean_proof"]["receipt_path"], result["id"])
            record["status"] = "LEAN_CERTIFIED"
            wheel.register_lemma(Conjecture.from_dict(record["conjecture"]), tactic=receipt["tactic"],
                conjecture_id=result["id"], theorem_name=receipt["theorem_name"],
                receipt_path=result["lean_proof"]["receipt_path"])
    atlas["flywheel_lemmas"] = [lem.to_dict() for lem in wheel.lemmas.values()]
    atlas["invariant_fertility"] = wheel.feedback.invariant_fertility
    atlas["active_flywheel_lemmas"] = len(wheel.lemmas)
    if "catalog_graphs" not in atlas:
        atlas["catalog_graphs"] = len(InstanceDatabase()._cached_gi)
        atlas["invariants_tracked"] = len(InstanceDatabase()._cached_matrix)
    atlas["batch_metrics"] = metrics
    _check_batch_stop(stop, deadline)
    return reconcile(atlas)


def _options(workers=1, proof_backend="none", model=None, model_rounds=2,
             model_request_timeout=150, model_candidates=0, reasoning_effort=None):
    from autonomous_math.prover.codex_synthesis import REASONING_EFFORTS
    if type(workers) is not int or not 1 <= workers <= MAX_WORKERS or proof_backend not in {"none", "codex"}:
        raise ValueError(f"Workers must be integers 1..{MAX_WORKERS} and proof backend none or codex")
    if (not 1 <= model_rounds <= 3 or not math.isfinite(model_request_timeout)
        or not 0 < model_request_timeout <= 1200 or not 0 <= model_candidates <= 8
        or reasoning_effort is not None and reasoning_effort not in REASONING_EFFORTS):
        raise ValueError("Invalid bounded model settings")
    return dict(workers=workers, proof_backend=proof_backend, model=model, model_rounds=model_rounds,
                model_request_timeout=model_request_timeout, model_candidates=model_candidates,
                reasoning_effort=reasoning_effort)


def _evaluate_batch(candidates, atlas, directory, lean_limit, interrupted, deadline, stage):
    """Synchronous compatibility entrypoint; live execution always uses bounded jobs."""
    options = dict(_options(), replay_boundary=False)
    return _coordinate_candidates(candidates, atlas, Path(directory), lean_limit, interrupted, deadline,
                                  stage, options, synchronous=True)


def _sample_preset(preset, atlas, invariants=None):
    from autonomous_math.prover.flywheel import FlywheelFeedback
    feedback = FlywheelFeedback()
    feedback.invariant_fertility = atlas.get("invariant_fertility", {})
    invariants = invariants or [v for v in InstanceDatabase()._cached_matrix if not v.startswith("is_")]
    focus = set(preset.get("focus_invariants", []))
    if focus:
        invariants = sorted((set(invariants) | focus) & (focus | set(preset.get("bridge_invariants", []))))
    campaign = preset.get("campaign")
    history_rows = atlas.setdefault("campaign_sampling_history", {}).get(campaign, []) if campaign else atlas.get("sampling_history", [])
    history = set(tuple(p) for p in history_rows)
    if len(history) > 60:
        history.clear()
    pairs = []
    for _ in range(2):
        pair = feedback.sample_pair(invariants, history)
        if focus and not set(pair) & focus:
            pair = (random.choice(sorted(focus - {pair[1]})), pair[1])
        pairs.append(pair)
        history.add(pair)
    y, xs, guard = feedback.sample_triad(invariants, [None, "is_connected", "is_tree", "is_bipartite", "is_regular"])
    if focus and not ({y} | set(xs)) & focus:
        y = random.choice(sorted(focus - set(xs)))
    if campaign:
        atlas["campaign_sampling_history"][campaign] = sorted(history)
    else:
        atlas["sampling_history"] = sorted(history)
    return dict(preset, pairs=pairs, triads=[(y, xs, guard)])


def _merge_plan(plan, job, atlas):
    """Validate a planning delta before changing any coordinator-owned knowledge."""
    from autonomous_math.sieve.adversarial_holdouts import HOLDOUT_REVISION
    if plan.get("holdout_revision") != HOLDOUT_REVISION:
        raise ValueError("Planner used a different challenger revision")
    if (plan.get("catalog_graphs") != len(plan.get("catalog_graph_hashes", []))
        or any(not isinstance(value, str) or len(value) != 64 for value in plan["catalog_graph_hashes"])):
        raise ValueError("Invalid planner catalog fingerprint")
    random.Random().setstate(plan["random_state"])
    candidates = [Conjecture.from_dict(c) for c in plan["candidates"]]
    original = {r["id"]: r for r in job["records"]}
    records = plan.get("records", [])
    if len({r["id"] for r in records}) != len(records):
        raise ValueError("Duplicate planner reassessment")
    refutations = []
    allowed = {"holdout_tested", "holdout_status", "holdout_revision", "status", "counterexample", "reassessed_at", "lean_proof"}
    for record in records:
        before = original.get(record["id"])
        if not before or any(record.get(key) != value for key, value in before.items() if key not in allowed):
            raise ValueError("Planner changed committed proof or conjecture data")
        if set(record) - set(before) - allowed:
            raise ValueError("Planner returned unassigned state")
        if record.get("lean_proof") != before.get("lean_proof"):
            raise ValueError("Planner changed committed proof data")
        if before.get("status") == "LEAN_CERTIFIED" and record.get("status") != "LEAN_CERTIFIED":
            raise ValueError("Planner contradicted a checked theorem")
        if record.get("status") == "REFUTED":
            candidate = Conjecture.from_dict(record["conjecture"])
            certificate = CounterexampleCertificate.from_dict(record["counterexample"])
            valid, errors = CounterexampleCertificateVerifier.verify_with_details(certificate, candidate)
            if not valid:
                raise ValueError(f"Invalid planning counterexample: {errors}")
            refutations.append(record)
        elif record.get("status") not in {before.get("status"), "INCONCLUSIVE"}:
            raise ValueError("Planner returned an invalid reassessment status")
    for record in sorted(records, key=lambda r: r["id"]):
        atlas["theorems"][record["id"]] = record
    atlas["total_refuted"] += len(refutations)
    atlas["recent_refutations"].extend(sorted(refutations, key=lambda r: r["id"]))
    for key in ("holdout_revision", "replayed_boundary_graphs", "catalog_graphs", "invariants_tracked"):
        atlas[key] = plan[key]
    if plan.get("challenger_reassessment") is not None:
        atlas["challenger_reassessment"] = plan["challenger_reassessment"]
    if plan.get("code_catalog") is not None:
        atlas["code_catalog"] = plan["code_catalog"]
    atlas["deferred_counterexample_graphs"] = copy.deepcopy(plan.get("deferred_counterexample_graphs", []))
    return candidates


def _bounded_batch(preset, atlas, directory, pair_limit, triad_limit, lean_limit, stop, deadline, status,
                   adaptive=False, options=None):
    options = dict(options or _options(), focus_invariants=preset.get("focus_invariants", []),
                   bridge_invariants=preset.get("bridge_invariants", []), campaign=preset.get("campaign"),
                   research_family=preset.get("proposal_family"))
    working = copy.deepcopy(atlas)
    initial_rng = random.getstate()
    started = time.monotonic()
    def ceiling(target_count):
        # Proof jobs contain one target each; the budget covers all admitted
        # target waves, not merely the number of concurrently occupied slots.
        waves = math.ceil(target_count/options["workers"])
        proposal = options["model_request_timeout"] if options["proof_backend"] == "codex" and options["model_candidates"] else 0
        return min(deadline, started+60.0+proposal+waves*_proof_budget(options))
    batch_deadline = ceiling(lean_limit if lean_limit is not None else max(1, len(atlas["theorems"])))
    attempt_dir = Path(directory) / "jobs" / f"round-{atlas['total_iterations']+1:08d}-{uuid.uuid4().hex[:12]}"
    status["active_batch"] = {"campaign": options.get("campaign"), "checkpoint": atlas["total_iterations"] + 1,
        "started_at": time.time(), "directory": str(attempt_dir), "state": "running"}
    def check():
        _check_batch_stop(stop, batch_deadline)
    try:
        if adaptive:
            from autonomous_math.sieve.instance_db import KEYS_TO_VECTORIZE
            preset = _sample_preset(preset, working, KEYS_TO_VECTORIZE)
        status["stage"] = "planning"
        planning_job = {"job_id": "planning-00", "kind": "planning", "directory": str(attempt_dir / "planning-00"),
            "records": [r for r in working["theorems"].values() if r.get("conjecture") and r.get("status") != "REFUTED"],
            "holdout_revision": working.get("holdout_revision"), "preset": preset,
            "pair_limit": pair_limit, "triad_limit": triad_limit, "rng_state": random.getstate()}
        plan = _dispatch_jobs([planning_job], _snapshot(working), options, stop, batch_deadline, status)[0]
        candidates = _merge_plan(plan, planning_job, working)
        random.setstate(plan["random_state"])
        if lean_limit is None:
            batch_deadline = ceiling(len(working["theorems"])+len(candidates))
        check()
        review_feedback = None
        if options["proof_backend"] == "codex" and options["model_candidates"]:
            from autonomous_math.conjecturing.model_proposals import build_review_feedback
            from autonomous_math.novelty.review import get_reviews
            # One immutable coordinator snapshot; proposal children never read a
            # sidecar being updated by the asynchronous review worker.
            try:
                review_feedback = build_review_feedback(dict(working, research_family=options.get("research_family")),
                                                       get_reviews(working, directory), directory)
            except (ValueError, OSError, KeyError, TypeError) as exc:
                logger.warning("Review guidance unavailable; ordinary exploration continues: %s", exc)
        proposal_context = hashlib.sha256(json.dumps({**{key: options[key] for key in
            ("proof_backend", "model", "reasoning_effort", "model_rounds", "model_request_timeout", "model_candidates",
             "research_family")}, "review_feedback_sha256": (review_feedback or {}).get("sha256")}, sort_keys=True).encode()).hexdigest()
        if (options["proof_backend"] == "codex" and options["model_candidates"]
            and (working.get("model_proposal_context") != proposal_context
                 or time.time() >= working.get("model_proposals_retry_at", 0))):
            context = {"theorems": working["theorems"],
                       "recent_refutations": working.get("recent_refutations", []),
                       "total_iterations": working.get("total_iterations", 0),
                       "research_family": options.get("research_family"), "code_catalog": working.get("code_catalog"),
                       "campaign_rotation": status.get("campaign_rotation")}
            if review_feedback is not None:
                context["review_feedback"] = copy.deepcopy(review_feedback)
            job = {"job_id": "proposal-00", "kind": "proposal", "directory": str(attempt_dir / "proposal-00"), "context": context}
            status["stage"] = "model_proposals"
            proposal = _dispatch_jobs([job], _snapshot(working), options, stop, batch_deadline, status)[0]
            from autonomous_math.prover.trusted_lean import render_challenge
            additions = [Conjecture.from_dict(c) for c in proposal["candidates"]]
            if len(additions) > options["model_candidates"]:
                raise ValueError("Worker exceeded the proposal budget")
            for candidate in additions:
                render_challenge(candidate)
            candidates.extend(additions)
            working.setdefault("model_proposals", []).append(proposal["trace"])
            working["model_proposals"] = working["model_proposals"][-20:]
            working["model_proposal_context"] = proposal_context
            if proposal["trace"].get("status") in {"ERROR", "FAILED"}:
                working["model_proposals_retry_at"] = time.time()+60
            else:
                working.pop("model_proposals_retry_at", None)
        _coordinate_candidates(candidates, working, attempt_dir, lean_limit, stop, batch_deadline, status, options,
                               screen_key=_screening_key(plan["catalog_graph_hashes"]))
        working["random_state"] = random.getstate()
        return working
    except BaseException:
        InstanceDatabase.clear_cache()  # A failed round must not leak learned graphs into a later run.
        random.setstate(initial_rng)
        raise


def _execute(directory, presets, max_iterations, timeout_sec, pair_limit, triad_limit, lean_limit, seed,
             workers=1, proof_backend="codex", model=None, model_rounds=2,
             model_request_timeout=150, model_candidates=2, reasoning_effort=None, campaign=None):
    directory = Path(directory).resolve()
    # Unscoped synthetic presets remain available to the existing internal test
    # and evaluation entry point; public campaign choices are checked upstream.
    presets = [dict(p, campaign=p.get("campaign", "unscoped")) for p in presets]
    options = _options(workers, proof_backend, model, model_rounds, model_request_timeout, model_candidates, reasoning_effort)
    if (max_iterations is not None and max_iterations < 0
        or timeout_sec is not None and (not math.isfinite(timeout_sec) or timeout_sec <= 0)):
        raise ValueError("Iterations must be nonnegative and timeout positive")
    if min(pair_limit, triad_limit) < 0 or lean_limit is not None and lean_limit < 0:
        raise ValueError("Candidate limits must be nonnegative")
    with writer_lock(directory):
        InstanceDatabase.clear_cache()
        atlas = load_snapshot(directory)  # corrupt data is an error, never silently replaced
        _migrate_candidate_identity(atlas)
        random.seed(seed)
        if "random_state" in atlas:
            def tuples(value):
                return tuple(tuples(v) for v in value) if isinstance(value, list) else value
            random.setstate(tuples(atlas["random_state"]))
        atlas.setdefault("random_state", random.getstate())
        atlas["schema_version"] = 2
        atlas["configuration"] = {"initial_seed": atlas.get("configuration", {}).get("initial_seed", seed),
            "requested_seed": seed, "resumed_rng": "random_state" in atlas and atlas["total_iterations"] > 0,
            "pair_limit": pair_limit, "triad_limit": triad_limit, "lean_limit": lean_limit, "campaign": campaign, **options}
        _prepare_campaign_rotation(atlas, presets)
        schedule = atlas["campaign_rotation"]["schedule"]
        from autonomous_math.conjecturing.model_proposals import REVIEW_FEEDBACK_REVISION
        previous_frontier = atlas.get("frontier_period") or {}
        if (previous_frontier.get("revision") != REVIEW_FEEDBACK_REVISION
            or previous_frontier.get("campaign_schedule") != schedule
            or previous_frontier.get("campaign_rotation_revision") != CAMPAIGN_ROTATION_REVISION):
            if previous_frontier:
                atlas.setdefault("frontier_period_history", []).append(copy.deepcopy(previous_frontier))
                atlas["frontier_period_history"] = atlas["frontier_period_history"][-20:]
            atlas["frontier_period"] = {"revision": REVIEW_FEEDBACK_REVISION, "started_at": time.time(),
                "starting_checkpoint": atlas["total_iterations"], "configuration": copy.deepcopy(atlas["configuration"]),
                "campaign_schedule": list(schedule), "campaign_rotation_revision": CAMPAIGN_ROTATION_REVISION,
                "starting_certified_ids": sorted(key for key, row in atlas["theorems"].items()
                                                 if row.get("status") == "LEAN_CERTIFIED")}
        stop = GracefulDaemonInterrupt()
        stop.install()
        status = {"run_id": str(uuid.uuid4()), "pid": os.getpid(), "state": "running", "stage": "starting",
                  "committed_iteration": atlas["total_iterations"], "started_at": time.time(),
                  "frontier_period": copy.deepcopy(atlas["frontier_period"]),
                  "campaign_rotation": _campaign_view(atlas), "campaign_progress": copy.deepcopy(atlas["campaign_progress"]),
                  "model_selection": {"enabled": False, "model": None, "reasoning_effort": None}}
        try:
            status["campaign_visits"] = json.loads((directory / "run_status.json").read_text()).get("campaign_visits", {})
        except (OSError, ValueError):
            status["campaign_visits"] = {}
        if proof_backend == "codex":
            selection = _synthesizer(options).configuration()
            status["model_selection"] = {"enabled": True,
                                         "model": selection["model_override"] or selection["configured_model"],
                                         "reasoning_effort": selection["reasoning_effort"]}
        finished = threading.Event()
        heartbeat_error = []
        deadline = time.monotonic() + timeout_sec if timeout_sec is not None else float("inf")
        reviewer = None
        from autonomous_math.prover.replay_worker import ReplayWorker
        replayer = ReplayWorker(directory, stop_requested=lambda: stop.stop_requested, deadline=deadline)
        try:
            replayer.start()
        except BaseException:
            stop.uninstall()
            raise
        if proof_backend == "codex":
            from autonomous_math.novelty.review_worker import ReviewWorker
            try:
                reviewer = ReviewWorker(directory,
                    _synthesizer(dict(options, model_request_timeout=max(300, model_request_timeout))),
                    stop_requested=lambda: stop.stop_requested, deadline=deadline)
                reviewer.start()
            except Exception as exc:
                reviewer = None
                logger.warning("Automated originality reviewer could not start: %s", exc)
                status["novelty_review"] = {"status": "error", "error": str(exc)}
        def heartbeat():
            while not finished.is_set():
                _record_stop_diagnostics(status, stop)
                status["independent_replay"] = dict(replayer.state)
                if reviewer:
                    try:
                        reviewer.pulse()
                    except Exception as exc:
                        logger.warning("Originality reviewer heartbeat failed: %s", exc)
                try:
                    replayer.pulse()
                    atomic_save_json(dict(status, heartbeat=time.time()), directory / "run_status.json")
                except Exception as exc:
                    heartbeat_error.append(exc)
                    status.update(stop_origin="heartbeat_error", stop_reason=str(exc))
                    stop.stop_requested = True
                    return
                finished.wait(2)
        thread = threading.Thread(target=heartbeat, daemon=True)
        thread.start()
        count = 0
        try:
            while max_iterations is None or count < max_iterations:
                if stop.stop_requested:
                    _record_stop_diagnostics(status, stop)
                    break
                if time.monotonic() >= deadline:
                    status.update(stop_origin="outer_deadline", stop_reason="Configured research deadline exhausted")
                    break
                if (directory / "stop_after_checkpoint.json").exists():
                    status["stop_origin"] = "checkpoint_boundary"
                    status["stop_reason"] = "Requested stop at committed checkpoint boundary"
                    break
                status["stage"] = "generation"
                preset = presets[atlas["campaign_rotation"]["next_index"]]
                batch_started_at = time.time()
                status["campaign_rotation"] = _campaign_view(atlas, preset["campaign"])
                status["campaign_visits"][preset["campaign"]] = {"checkpoint": atlas["total_iterations"] + 1,
                    "started_at": batch_started_at, "run_id": status["run_id"]}
                try:
                    working = _bounded_batch(preset, atlas, directory, pair_limit, triad_limit, lean_limit,
                        stop, deadline, status, adaptive=len(presets)>1, options=options)
                except InterruptedError as exc:
                    status.update(interruption_reason=str(exc), interrupted_at=time.time(),
                                  interrupted_stage=status["stage"])
                    origin = getattr(exc, "stop_origin", None)
                    if origin is None:
                        origin = "batch_interruption"
                        if stop.stop_requested:
                            origin = "signal" if stop.stop_signal else "requested_stop"
                    status.setdefault("stop_origin", origin)
                    status.setdefault("stop_reason", str(exc))
                    _record_stop_diagnostics(status, stop)
                    if status.get("active_batch"):
                        status["active_batch"]["state"] = "interrupted"
                    break
                if heartbeat_error:
                    raise heartbeat_error[0]
                working["total_iterations"] += 1
                _commit_campaign_batch(working, atlas, preset["campaign"], batch_started_at)
                def tuples(value):
                    return tuple(tuples(v) for v in value) if isinstance(value, list) else value
                random.setstate(tuples(working["random_state"]))
                working["saved_at"] = time.time()
                status["stage"] = "checkpoint"
                atomic_save_json(working, directory / "cumulative_discovery_atlas.json")
                atlas = working
                if status.get("active_batch"):
                    status["active_batch"]["state"] = "committed"
                count += 1
                status["committed_iteration"] = atlas["total_iterations"]
                status["campaign_rotation"] = _campaign_view(atlas)
                status["campaign_progress"] = copy.deepcopy(atlas["campaign_progress"])
                print(f"Committed iteration {atlas['total_iterations']}: {atlas['total_lean_certified']} certified, "
                      f"{sum(r.get('status') == 'EMPIRICAL_SURVIVOR' for r in atlas['theorems'].values())} "
                      f"empirical survivors, {atlas['total_refuted']} refutation attempts")
                _refresh_novelty_reviews(atlas, directory, status, stop, deadline,
                                         online=proof_backend == "codex")
                replayer.wake()
                if reviewer:
                    reviewer.wake()
            if heartbeat_error:
                raise heartbeat_error[0]
            if "stop_origin" not in status:
                status.update(stop_origin="iteration_limit", stop_reason="Configured iteration limit reached")
            atlas.setdefault("saved_at", time.time())
            atomic_save_json(atlas, directory / "cumulative_discovery_atlas.json")
            status.update(state="stopped", stage="complete", stopped_at=time.time())
            status["campaign_rotation"] = _campaign_view(atlas)
            return atlas
        except BaseException as exc:
            status.setdefault("stop_origin", "failure")
            status.setdefault("stop_reason", str(exc))
            status.update(state="failed", error=str(exc), stage=status["stage"])
            if status.get("active_batch"):
                status["active_batch"]["state"] = "failed"
            raise
        finally:
            shutdown_error = None
            failed_before_shutdown = status.get("state") == "failed"
            for worker_name, worker in (("independent_replay", replayer), ("originality_review", reviewer)):
                if worker is None:
                    continue
                try:
                    worker.close()
                except Exception as exc:
                    shutdown_error = shutdown_error or exc
                    status.setdefault("shutdown_errors", []).append({"worker": worker_name, "error": str(exc)})
                    if status.get("state") != "failed":
                        status.update(state="failed", error=str(exc), stage="shutdown")
                    logger.error("%s shutdown failed: %s", worker_name, exc)
            finished.set()
            thread.join(timeout=5)
            if thread.is_alive():
                exc = RuntimeError("Research heartbeat did not stop before shutdown deadline")
                shutdown_error = shutdown_error or exc
                status.setdefault("shutdown_errors", []).append({"worker": "research_heartbeat", "error": str(exc)})
                if status.get("state") != "failed":
                    status.update(state="failed", error=str(exc), stage="shutdown")
                logger.error("Research heartbeat shutdown failed: %s", exc)
            stop.uninstall()
            _record_stop_diagnostics(status, stop)
            atomic_save_json(dict(status, heartbeat=time.time()), directory / "run_status.json")
            if shutdown_error and not failed_before_shutdown:
                raise shutdown_error


def _refresh_novelty_reviews(atlas, directory, status, stop, deadline, *, online=True):
    """Review committed proofs without making literature availability a proof gate."""
    if stop.stop_requested or time.monotonic() >= deadline:
        return
    from autonomous_math.novelty.review import update_reviews
    status["stage"] = "originality_review"
    try:
        review = update_reviews(atlas, directory, max_searches=2, online=online,
            timeout_sec=min(3.0, max(0.05, (deadline - time.monotonic()) / 2)),
            stop_requested=lambda: stop.stop_requested or time.monotonic() >= deadline)
        status["novelty_review"] = {"status": "complete", "updated_at": review.get("updated_at"),
                                   "counts": review.get("counts", {})}
    except Exception as exc:
        # The theorem checkpoint is already durable. Surface this independent
        # stage's failure and retry next round; never change proof certification.
        logger.warning("Originality review unavailable: %s", exc)
        status["novelty_review"] = {"status": "error", "error": str(exc)}


def run_continuous_daemon(output_dir=None, max_iterations=None, timeout_sec=None,
        limit_per_pair=3, limit_per_triad=3, max_lean_targets=3, seed=7, *, workers=1,
        proof_backend="codex", model=None, model_rounds=2, model_request_timeout=150, model_candidates=2,
        reasoning_effort=None, campaign=None):
    if campaign is not None and campaign not in CAMPAIGN_PRESETS:
        raise ValueError(f"Unknown campaign {campaign}")
    presets = [CAMPAIGN_PRESETS[campaign]] if campaign else list(CAMPAIGN_PRESETS.values())
    return _execute(output_dir or REPO_ROOT / "research_outputs", presets,
        max_iterations, timeout_sec, limit_per_pair, limit_per_triad, max_lean_targets, seed,
        workers, proof_backend, model, model_rounds, model_request_timeout, model_candidates,
        reasoning_effort=reasoning_effort, campaign=campaign)


def run_campaign(preset_name="spectral", output_dir=None, limit_per_pair=4, limit_per_triad=4,
                 max_lean_proof_targets=3, seed=7, *, workers=1, proof_backend="codex", model=None,
                 model_rounds=2, model_request_timeout=150, model_candidates=2, reasoning_effort=None):
    if preset_name not in CAMPAIGN_PRESETS:
        raise ValueError(f"Unknown campaign {preset_name}")
    directory = Path(output_dir or REPO_ROOT / "research_outputs")
    atlas = _execute(directory, [CAMPAIGN_PRESETS[preset_name]], 1, None,
        limit_per_pair, limit_per_triad, max_lean_proof_targets, seed,
        workers, proof_backend, model, model_rounds, model_request_timeout, model_candidates,
        reasoning_effort=reasoning_effort, campaign=preset_name)
    records = list(atlas["theorems"].values())
    known = [r for r in records if r["novelty_status"] in {"VERIFIED_REDISCOVERY", "TEXTBOOK_FOLKLORE"}]
    unknown = [r for r in records if r["novelty_status"] == "UNKNOWN_IN_LITERATURE"]
    summary = {"campaign": preset_name, "title": CAMPAIGN_PRESETS[preset_name]["title"],
        "total_conjectures": atlas["total_conjectures_generated"], "survived_count": atlas["total_survived"],
        "refuted_count": atlas["total_refuted"], "proven_count": atlas["total_lean_certified"],
        "novelty_summary": {"verified_rediscoveries_count": len(known), "candidate_novel_count": 0,
             "unknown_literature_count": len(unknown), "verified_rediscoveries": known, "candidate_novel_conjectures": []},
        "lean_verification": {"machine_checked_proven_count": atlas["total_lean_certified"],
             "verified_proofs": [r for r in records if r["status"] == "LEAN_CERTIFIED"]},
        "refuted": [r for r in records if r["status"] == "REFUTED"]}
    with writer_lock(directory):
        atomic_save_json(summary, directory / "research_digest.json")
    return summary

def generate_master_latex_report(master_catalog: Dict[str, Any]) -> str:
    """Render measured campaign results without implying empirical checks are proofs."""
    def tex(value):
        escapes = {"\\": r"\textbackslash{}", "_": r"\_", "%": r"\%", "&": r"\&",
                   "#": r"\#", "$": r"\$", "{": r"\{", "}": r"\}", "^": r"\^{}", "~": r"\~{}"}
        return "".join(escapes.get(char, char) for char in str(value))
    lines = [r"\documentclass{article}", r"\usepackage{booktabs}", r"\begin{document}",
             r"\section*{Autonomous research campaign results}",
             "Counts describe finite experiments and content-bound proof receipts. "
             "Local registry matches establish attribution only. Unmatched entries have unknown literature status; "
             "empirical survival does not establish a universal theorem.",
             r"\begin{tabular}{lrrrr}", r"\toprule",
             r"Campaign & Attempts & Current survivors & Refutation attempts & Lean receipts \\", r"\midrule"]
    campaigns = master_catalog.get("campaigns", {})
    for name, data in campaigns.items():
        lines.append(f"{tex(name)} & {data.get('total_conjectures', 0)} & {data.get('survived_count', 0)} & "
                     f"{data.get('refuted_count', 0)} & {data.get('proven_count', 0)} " + r"\\")
    lines += [r"\bottomrule", r"\end{tabular}", r"\section*{Local reference registry matches}", r"\begin{itemize}"]
    seen = set()
    for data in campaigns.values():
        for record in data.get("novelty_summary", {}).get("verified_rediscoveries", []):
            stmt = record.get("statement", record.get("conjecture", ""))
            key = json.dumps(stmt, sort_keys=True)
            if key in seen: continue
            seen.add(key)
            match = record.get("matched_theorem") or {}
            lines.append(r"\item " + tex(match.get("theorem_name", "Local reference")) + ": " + tex(stmt))
    if not seen: lines.append(r"\item No matches recorded.")
    lines += [r"\end{itemize}", r"\section*{Proof receipts}", r"\begin{itemize}"]
    seen = set()
    for data in campaigns.values():
        for record in data.get("lean_verification", {}).get("verified_proofs", []):
            proof = record.get("lean_proof") or record
            receipt, _ = validate_receipt(proof.get("receipt_path", ""), record.get("id", record.get("conjecture_id")))
            if not receipt or receipt["source_sha256"] in seen: continue
            seen.add(receipt["source_sha256"])
            lines.append(r"\item " + tex(receipt["conjecture_id"]) + ": " + tex(receipt["tactic"]) +
                         "; duration " + tex(round(receipt["duration_ms"], 1)) + " ms; " + tex(receipt["source_sha256"]))
    if not seen: lines.append(r"\item No valid kernel receipts available.")
    lines += [r"\end{itemize}", r"\end{document}"]
    return "\n".join(lines) + "\n"


def run_all_campaigns(output_dir=None, limit_per_pair=4, limit_per_triad=4, max_lean_proof_targets=3, seed=7,
                      **worker_options):
    directory = Path(output_dir or REPO_ROOT / "research_outputs")
    with writer_lock(directory):
        campaigns = {name: run_campaign(name, directory / name, limit_per_pair, limit_per_triad,
            max_lean_proof_targets, seed, **worker_options) for name in CAMPAIGN_PRESETS}
        atlas = load_snapshot(directory)
        for name in campaigns:
            child = load_snapshot(directory / name)
            atlas["theorems"].update(child["theorems"])
        atlas.update(total_iterations=sum(load_snapshot(directory / n)["total_iterations"] for n in campaigns),
            total_conjectures_generated=sum(c["total_conjectures"] for c in campaigns.values()),
            total_refuted=sum(c["refuted_count"] for c in campaigns.values()), saved_at=time.time())
        reconcile(atlas)
        atomic_save_json(atlas, directory / "cumulative_discovery_atlas.json")
        master = {"campaigns": campaigns, "aggregate_metrics": {"total_campaigns": len(campaigns),
            "total_conjectures_evaluated": atlas["total_conjectures_generated"], "total_survived": atlas["total_survived"],
            "total_refuted": atlas["total_refuted"], "total_lean_certified": atlas["total_lean_certified"],
            "total_verified_rediscoveries": atlas["total_verified_rediscoveries"], "total_candidate_novel": 0}}
        atomic_save_json(master, directory / "master_catalog.json")
        (directory / "master_report.tex").write_text(generate_master_latex_report(master))
        return master


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", "-c", default=None, choices=list(CAMPAIGN_PRESETS))
    parser.add_argument("--output-dir", "-o", type=Path, default=REPO_ROOT / "research_outputs")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--all-campaigns", action="store_true")
    modes.add_argument("--continuous", "--daemon", action="store_true")
    modes.add_argument("--dashboard", action="store_true")
    parser.add_argument("--port", type=int, default=8050)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--max-iterations", type=int)
    parser.add_argument("--timeout-sec", type=float)
    parser.add_argument("--limit-per-pair", type=int, default=4)
    parser.add_argument("--limit-per-triad", type=int, default=4)
    parser.add_argument("--max-lean-targets", type=int, default=3)
    parser.add_argument("--workers", type=int, default=1, choices=range(1, MAX_WORKERS+1))
    parser.add_argument("--proof-backend", choices=("none", "codex"), default="codex")
    parser.add_argument("--model", default=None)
    from autonomous_math.prover.codex_synthesis import REASONING_EFFORTS
    parser.add_argument("--reasoning-effort", choices=REASONING_EFFORTS, default=None)
    parser.add_argument("--model-rounds", type=int, default=2, choices=range(1, 4))
    parser.add_argument("--model-request-timeout", type=float, default=150)
    parser.add_argument("--model-candidates", type=int, default=2)
    args = parser.parse_args()
    worker_options = {name: getattr(args, name) for name in
                      ("workers", "proof_backend", "model", "reasoning_effort", "model_rounds", "model_request_timeout", "model_candidates")}
    if args.dashboard:
        from autonomous_math.dashboard.server import run_dashboard
        run_dashboard(args.port, args.host, data_dir=args.output_dir)
    elif args.continuous:
        run_continuous_daemon(args.output_dir, args.max_iterations, args.timeout_sec,
            args.limit_per_pair, args.limit_per_triad, args.max_lean_targets, args.seed, campaign=args.campaign, **worker_options)
    elif args.all_campaigns:
        run_all_campaigns(args.output_dir, args.limit_per_pair, args.limit_per_triad, args.max_lean_targets,
                          args.seed, **worker_options)
    else:
        run_campaign(args.campaign or "spectral", args.output_dir, args.limit_per_pair, args.limit_per_triad,
                     args.max_lean_targets, args.seed, **worker_options)

if __name__ == "__main__":
    main()
