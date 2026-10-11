#!/usr/bin/env python3
"""Small frozen comparison of fixed, model/frozen, and training-reuse search.

Prepare once, then run each arm separately under comparable machine load. The
portfolio contains known results and a predeclared composition; it estimates
bounded proof-search performance, not theorem novelty or sealed-premise learning.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import time

from autonomous_math.core.ast import BinaryOpNode as B, ConstantNode as C, InvariantNode as I, Conjecture, GuardPredicate
from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
from autonomous_math.prover.flywheel import FlywheelLemma, LemmaFlywheel
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.trusted_lean import render_challenge
from autonomous_math.research_state import atomic_save_json, atomic_save_text, load_snapshot, sha256, validate_receipt, workspace_fingerprint, writer_lock
from autonomous_math.sieve.certificates import CounterexampleCertificateVerifier
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.model_counterexamples import verify_model_counterexample_certificate
from run_research import independent_holdout

ROOT = Path(__file__).resolve().parent
ARMS = ("fixed", "model_frozen", "model_learning")
BUDGET = {"fixed_attempts": 4, "attempt_timeout_sec": 10.0, "target_timeout_sec": 360.0,
          "model_rounds": 2, "request_timeout_sec": 150.0}
FOCUSED_BUDGET = {"fixed_attempts": 4, "attempt_timeout_sec": 10.0, "target_timeout_sec": 220.0,
                  "model_rounds": 1, "request_timeout_sec": 150.0}
LIMITATIONS = [
    "Four selected known targets, one pass per arm, and no claim of theorem novelty or general discovery rate.",
    "Evaluation proofs never enter any library; only this arm's successful training proofs enter the learning library.",
    "The model can inspect pinned Mathlib. Library freezing does not make this a sealed novel-premise benchmark.",
    "The independent-set target needs an additional color-class capacity bridge; the energy evaluation is a predeclared composition.",
    "Model nondeterminism and arm order can affect this small comparison. A library reference is not proof of causal necessity.",
    "Recorded usage comes from retained per-request traces. Missing usage is unknown, and cached/reasoning tokens are not added again to input/output totals.",
]


def statement_key(candidate):
    fields = candidate.to_dict()
    exact = {key: fields[key] for key in ("lhs_expr", "rel", "rhs_expr", "guard_predicate")}
    return hashlib.sha256(json.dumps(exact, sort_keys=True, allow_nan=False).encode()).hexdigest()


def portfolio():
    n, m, d, chi, alpha, energy = (I(k) for k in
        ("order", "size", "max_degree", "chromatic_number", "independence_number", "graph_energy"))
    specs = [
        ("training", "greedy_coloring", chi, B("+", d, C(1)), "known_result", "Coloring and maximum degree", []),
        ("training", "mcclelland_energy", B("^", energy, C(2)), B("*", B("*", C(2), n), m),
         "known_result", "Adjacency spectrum and edge count", []),
        ("evaluation", "independent_set_capacity", n, B("*", alpha, B("+", d, C(1))),
         "known_result_with_additional_bridge", "Independent sets via coloring class capacity", ["greedy_coloring"]),
        ("evaluation", "energy_degree_composition", B("^", energy, C(2)), B("*", B("^", n, C(2)), d),
         "predeclared_known_composition", "Spectral energy and degree density", ["mcclelland_energy", "degree_sum_density_bound"]),
    ]
    rows = []
    for phase, name, lhs, rhs, classification, family, dependencies in specs:
        candidate = Conjecture.create(id=f"portfolio_{name}", lhs=lhs, rel="<=", rhs=rhs,
            metadata={"origin": "frozen_generative_portfolio", "classification": classification,
                      "novelty_status": "NO_NOVELTY_CLAIM"})
        challenge, _ = render_challenge(candidate)
        rows.append({"phase": phase, "name": name, "conjecture": candidate.to_dict(),
            "statement_key": statement_key(candidate), "challenge_sha256": hashlib.sha256(challenge.encode()).hexdigest(),
            "classification": classification, "family": family, "anticipated_dependencies": dependencies})
    if len({row["statement_key"] for row in rows}) != len(rows):
        raise ValueError("Portfolio statements overlap")
    return rows


def focused_portfolio():
    """Two training families, two transfer targets and an unrelated control.

    All are known mathematics. Held out means excluded from training and library
    registration in this experiment, not unknown to the model or filesystem.
    """
    n, m, chi, alpha, omega, energy = (I(k) for k in
        ("order", "size", "chromatic_number", "independence_number", "clique_number", "graph_energy"))
    triangle_free = GuardPredicate(predicate_type="property", property_name="is_triangle_free")
    specs = [
        ("training", "color_independence", B("+", chi, alpha), B("+", n, C(1)), None,
         "coloring", "known_result", []),
        ("training", "energy_edges", B("^", energy, C(2)), B("*", B("*", C(2), n), m), None,
         "spectral", "known_result", []),
        ("evaluation", "clique_independence", B("+", omega, alpha), B("+", n, C(1)), None,
         "coloring", "predeclared_known_composition", ["color_independence", "archetype_chi_ge_omega"]),
        ("evaluation", "energy_order", B("^", energy, C(2)), B("*", B("^", n, C(2)), B("-", n, C(1))), None,
         "spectral", "known_result_with_additional_bridge", ["energy_edges", "simple_graph_edge_card_bound"]),
        ("evaluation", "triangle_free_density", B("*", C(4), m), B("^", n, C(2)), triangle_free,
         "extremal", "unrelated_family_control", []),
    ]
    rows = []
    for phase, name, lhs, rhs, guard, family, classification, dependencies in specs:
        candidate = Conjecture.create(id=f"focused_{name}", lhs=lhs, rel="<=", rhs=rhs, guard=guard,
            metadata={"origin": "focused_learning_evaluation", "classification": classification,
                      "novelty_status": "NO_NOVELTY_CLAIM"})
        challenge, _ = render_challenge(candidate)
        rows.append({"phase": phase, "name": name, "conjecture": candidate.to_dict(),
            "statement_key": statement_key(candidate), "challenge_sha256": hashlib.sha256(challenge.encode()).hexdigest(),
            "classification": classification, "family": family, "anticipated_dependencies": dependencies})
    return rows


def false_control():
    return Conjecture.create(id="portfolio_false_greedy_boundary", lhs=I("chromatic_number"), rel="<=", rhs=I("max_degree"),
        metadata={"origin": "separate_false_control", "scope": "not included in the four-target proof denominators"})


def screen(candidate, database):
    started = time.monotonic()
    catalog = database.sieve_conjecture(candidate)
    holdout = independent_holdout(candidate) if catalog.is_survived else None
    result = holdout or catalog
    certificate = result.counterexample_certificate
    replayed, errors = CounterexampleCertificateVerifier.verify_with_details(certificate, candidate) if certificate else (None, [])
    if result.is_refuted and not replayed:
        raise ValueError(f"Invalid host refutation for {candidate.id}: {errors}")
    return {"id": candidate.id, "conjecture": candidate.to_dict(), "statement_key": statement_key(candidate),
        "status": result.status, "catalog": catalog.to_dict(), "holdout": holdout.to_dict() if holdout else None,
        "counterexample": certificate.to_dict() if certificate else None, "counterexample_replayed": replayed,
        "elapsed_sec": time.monotonic() - started}


def source_hashes():
    paths = [Path(__file__), ROOT / "run_research.py", ROOT / "pyproject.toml", ROOT / "library/catalog.json",
             *sorted((ROOT / "autonomous_math").rglob("*.py")), *sorted((ROOT / "library/proofs").glob("*.lean"))]
    return {str(path.relative_to(ROOT)): sha256(path) for path in paths}


def validate_model_refutation(row, candidate):
    """Replay an exact-target model witness without admitting it as a proof."""
    certificate = row.get("counterexample")
    if (row.get("is_machine_checked") is not False
            or any(row.get(key) for key in ("receipt_path", "verified_file_path", "successful_tactic", "proof_origin"))
            or not certificate or certificate != row.get("counterexample_certificate")):
        raise ValueError("Model refutation lacks a consistent non-proof certificate")
    verify_model_counterexample_certificate(certificate, candidate)


def initial_library(seed_dir, directory):
    """Copy exactly the seven catalog proofs; ignore all later live discoveries."""
    directory.mkdir(parents=True, exist_ok=True)
    catalog = json.loads((ROOT / "library/catalog.json").read_text())
    items = catalog["theorems"]
    if len(items) != 7 or len({item["id"] for item in items}) != 7:
        raise ValueError("This predeclared comparison requires exactly seven catalog foundations")
    atlas = load_snapshot(seed_dir)
    wheel = LemmaFlywheel(storage_path=directory / "flywheel.json")
    wheel.lemmas = {}
    bindings = []
    fingerprints = {}
    for item in items:
        record = atlas["theorems"].get(item["id"], {})
        receipt, error = validate_receipt((record.get("lean_proof") or {}).get("receipt_path", ""), item["id"], fingerprints)
        if record.get("status") != "LEAN_CERTIFIED" or not receipt:
            raise ValueError(f"Missing valid foundation {item['id']}: {error}")
        if receipt.get("conjecture") != item["conjecture"] or receipt["source_sha256"] != item["source_sha256"]:
            raise ValueError(f"Foundation differs from the checked-in catalog: {item['id']}")
        bound = copy.deepcopy(receipt)
        original_path = (record["lean_proof"]["receipt_path"])
        for field, suffix in (("source", ".lean"), ("challenge", ".challenge.lean")):
            destination = directory / f"{receipt['source_sha256']}{suffix}"
            atomic_save_text(Path(receipt[f"{field}_path"]).read_text(), destination)
            bound[f"{field}_path"] = str(destination)
        receipt_path = directory / f"{receipt['source_sha256']}.receipt.json"
        atomic_save_json(bound, receipt_path)
        checked, error = validate_receipt(receipt_path, item["id"], fingerprints)
        if not checked:
            raise ValueError(f"Invalid copied foundation: {error}")
        candidate = Conjecture.from_dict(item["conjecture"])
        wheel.register_lemma(candidate, bound["tactic"], receipt_path=receipt_path)
        bindings.append({"id": candidate.id, "statement_key": statement_key(candidate),
            "receipt_path": str(receipt_path), "receipt_sha256": sha256(receipt_path),
            "original_receipt_path": str(original_path), "original_receipt_sha256": sha256(Path(original_path)),
            "source_sha256": bound["source_sha256"], "challenge_sha256": bound["challenge_sha256"]})
    return [lemma.to_dict() for lemma in wheel.lemmas.values()], bindings


def prepare(output_dir, seed_dir=ROOT / "research_outputs", profile="legacy", repetitions=1):
    if profile not in {"legacy", "focused"} or type(repetitions) is not int or not 1 <= repetitions <= 3:
        raise ValueError("Choose a known profile and one to three predeclared repetitions")
    directory = Path(output_dir).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    if any(directory.iterdir()):
        raise ValueError("Preparation requires a fresh empty evidence directory")
    started = time.monotonic()
    sources = source_hashes()
    budget = dict(FOCUSED_BUDGET if profile == "focused" else BUDGET)
    configuration = CodexProofSynthesizer(max_rounds=budget["model_rounds"], timeout_per_request=budget["request_timeout_sec"]).configuration()
    workspace = workspace_fingerprint(ROOT / "certified_lean")
    rows = focused_portfolio() if profile == "focused" else portfolio()
    initial, bindings = initial_library(Path(seed_dir).resolve(), directory / "initial")
    if {row["statement_key"] for row in rows} & {binding["statement_key"] for binding in bindings}:
        raise ValueError("Training or evaluation target is already an initial foundation")
    database = InstanceDatabase()
    screening = {row["conjecture"]["id"]: screen(Conjecture.from_dict(row["conjecture"]), database) for row in rows}
    control = screen(false_control(), database)
    if control["status"] != "REFUTED" or not control["counterexample_replayed"]:
        raise ValueError("The false χ≤Δ control must be independently refuted and replayed")
    atomic_save_json({"targets": screening, "separate_false_control": control}, directory / "host_screening.json")
    if source_hashes() != sources:
        raise RuntimeError("Source changed during preparation; retain this partial evidence and prepare afresh")
    exposure = load_snapshot(Path(seed_dir).resolve())
    prior = {statement_key(Conjecture.from_dict(r["conjecture"])): r.get("status")
             for r in exposure.get("theorems", {}).values() if r.get("conjecture")}
    limitations = list(LIMITATIONS)
    if profile == "focused":
        limitations[0] = "Five selected known targets: two training families, two held-out transfer targets and one unrelated-family control. No novelty or general discovery-rate claim."
        limitations[3] = "The coloring transfer is a predeclared composition; the spectral transfer needs an additional edge-cardinality bridge. The triangle-free target is an unrelated-family control."
    limitations.append("Repeated trials are separate stochastic runs, not controlled model seeds. Alternating model-arm order reduces one ordering confound; the filesystem is not sealed.")
    manifest = {"schema_version": 2, "profile": profile, "repetitions": repetitions,
        "arm_order": [list(ARMS) if index % 2 == 0 else ["fixed", "model_learning", "model_frozen"] for index in range(repetitions)],
        "portfolio": rows, "arms": list(ARMS), "budget": budget,
        "initial_library": initial, "initial_receipt_bindings": bindings, "source_sha256": sources,
        "workspace_sha256": workspace, "model_configuration": configuration,
        "host_screening_sha256": sha256(directory / "host_screening.json"),
        "setup_elapsed_sec": time.monotonic() - started, "limitations": limitations,
        "prior_live_exposure": {r["conjecture"]["id"]: prior.get(r["statement_key"], "not_in_saved_atlas") for r in rows},
        "seed_snapshot_path": str(Path(seed_dir).resolve() / "cumulative_discovery_atlas.json"),
        "setup_replay_scope": "Copied content-bound receipts validated; independent full baseline kernel replay is retained separately."}
    atomic_save_json(manifest, directory / "manifest.json")
    return manifest


def check_frozen(directory, manifest):
    if source_hashes() != manifest["source_sha256"]:
        raise RuntimeError("Evaluation source changed after freeze")
    if workspace_fingerprint(ROOT / "certified_lean") != manifest["workspace_sha256"]:
        raise RuntimeError("Pinned compiler dependencies changed after freeze")
    budget = manifest["budget"]
    configuration = CodexProofSynthesizer(max_rounds=budget["model_rounds"], timeout_per_request=budget["request_timeout_sec"]).configuration()
    # JSON canonicalizes configuration tuples as lists when loading the manifest.
    if json.dumps(configuration, sort_keys=True) != json.dumps(manifest["model_configuration"], sort_keys=True):
        raise RuntimeError("Model configuration or CLI changed after freeze")
    if sha256(directory / "host_screening.json") != manifest["host_screening_sha256"]:
        raise RuntimeError("Frozen host screening changed")
    for binding in manifest["initial_receipt_bindings"]:
        if sha256(Path(binding["receipt_path"])) != binding["receipt_sha256"] or not validate_receipt(binding["receipt_path"], binding["id"])[0]:
            raise RuntimeError(f"Initial proof binding changed: {binding['id']}")


def request_costs(rows, artifact_root=None):
    """Count retained host requests once; absent usage remains explicitly unknown."""
    traces, seen, totals, missing_usage = [], set(), {}, 0
    requests = []
    for row in rows:
        for index, saved in enumerate(row.get("synthesis_attempts", [])):
            artifact = saved.get("artifact_path")
            key = str(Path(artifact).resolve()) if artifact else f"{row['id']}:missing_trace:{index}"
            if key in seen:
                raise ValueError("A model request trace was assigned to multiple results")
            seen.add(key)
            requests.append((artifact, saved, "completed_target"))
    # Cancellation can leave a complete request trace before its target returns.
    # Include those retained costs even though no final target verdict exists.
    for path in sorted(Path(artifact_root).rglob("trace.json")) if artifact_root else []:
        key = str(path.parent.resolve())
        if key not in seen:
            requests.append((key, {}, "unfinished_target"))
            seen.add(key)
    for artifact, saved, assignment in requests:
        path = Path(artifact) / "trace.json" if artifact else None
        trace = json.loads(path.read_text()) if path and path.is_file() else saved
        usage = trace.get("usage") or {}
        valid_usage = {name: value for name, value in usage.items() if type(value) is int and value >= 0}
        complete = all(name in valid_usage for name in ("input_tokens", "output_tokens"))
        missing_usage += not complete
        for name, value in valid_usage.items():
            totals[name] = totals.get(name, 0) + value
        traces.append({"artifact_path": artifact, "trace_sha256": sha256(path) if path and path.is_file() else None,
            "status": trace.get("status"), "actual_model": trace.get("actual_model"), "assignment": assignment,
            "cli_launch_recorded": bool(trace.get("command")), "usage": valid_usage,
            "usage_complete": complete, "duration_ms": trace.get("duration_ms")})
    return {"host_request_attempts": len(traces), "recorded_cli_requests": sum(t["cli_launch_recorded"] for t in traces),
        "requests_with_missing_usage": missing_usage, "recorded_usage_sums": totals,
        "total_input_plus_output_tokens_if_complete": totals.get("input_tokens", 0) + totals.get("output_tokens", 0) if not missing_usage else None,
        "traces": traces}


def counts(rows):
    groups = {name: set() for name in ("certified", "refuted", "unresolved")}
    for row in rows:
        verdict = "certified" if row["status"] == "MACHINE_CHECKED_PROVEN" else "refuted" if row["status"] == "REFUTED" else "unresolved"
        groups[verdict].add(row["statement_key"])
    return {name: len(values) for name, values in groups.items()}


def _direct_library_references(receipt, library):
    source = Path(receipt["source_path"]).read_text()
    name = receipt["theorem_name"].split(".")[-1]
    body = source[source.rindex(f"theorem {name} "):].split(":= by", 1)[1]
    names = {key: value if isinstance(value, str) else value.lean_name for key, value in library.items()}
    references = LeanProofSearch._identifier_references(body, names.values())
    return sorted(key for key, name in names.items() if name in references)


def arm_directory(directory, manifest, arm, repetition=1):
    if type(repetition) is not int or not 1 <= repetition <= manifest.get("repetitions", 1):
        raise ValueError("Repetition is outside the frozen protocol")
    return directory / f"trial_{repetition:02d}" / arm if manifest.get("repetitions", 1) > 1 else directory / arm


def run_arm(output_dir, arm, repetition=1):
    started = time.monotonic()
    if arm not in ARMS:
        raise ValueError(f"Unknown arm: {arm}")
    directory = Path(output_dir).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    check_frozen(directory, manifest)
    with writer_lock(directory):
        target_dir = arm_directory(directory, manifest, arm, repetition)
        if target_dir.exists():
            raise ValueError("This arm already has evidence; do not overwrite or retry selected results")
        target_dir.mkdir(parents=True)
        wheel = LemmaFlywheel(storage_path=target_dir / "flywheel.json")
        wheel.lemmas = {item["lemma_id"]: FlywheelLemma(**item) for item in manifest["initial_library"]}
        wheel.save()
        budget = manifest["budget"]
        synthesizer = CodexProofSynthesizer(max_rounds=budget["model_rounds"], timeout_per_request=budget["request_timeout_sec"]) if arm != "fixed" else None
        if synthesizer and not synthesizer.is_available():
            raise RuntimeError("Configured model CLI is unavailable")
        prover = LeanProofSearch(flywheel=wheel, auto_register_flywheel=False, max_attempts=budget["fixed_attempts"],
            timeout_per_attempt=budget["attempt_timeout_sec"], total_timeout_sec=budget["target_timeout_sec"], synthesizer=synthesizer)
        screening = json.loads((directory / "host_screening.json").read_text())["targets"]
        rows = []
        report = {"arm": arm, "repetition": repetition, "state": "running", "manifest_sha256": sha256(directory / "manifest.json"),
                  "initial_library_count": len(wheel.lemmas), "budget": manifest["budget"], "rows": rows}
        atomic_save_json(report, target_dir / "results.json")
        try:
            for spec in manifest["portfolio"]:
                check_frozen(directory, manifest)
                candidate = Conjecture.from_dict(spec["conjecture"])
                before = set(wheel.lemmas)
                t0 = time.monotonic()
                row = {**spec, "id": candidate.id, "library_before": sorted(before)}
                if screening[candidate.id]["status"] == "REFUTED":
                    row.update(status="REFUTED", attempts_count=0, synthesis_attempts=[],
                               counterexample=screening[candidate.id]["counterexample"])
                else:
                    result = prover.prove_conjecture(candidate, output_dir=target_dir / "verified", total_timeout_sec=budget["target_timeout_sec"])
                    row.update(result.to_dict())
                    if result.status == "REFUTED":
                        row["counterexample"] = row.get("counterexample_certificate")
                        validate_model_refutation(row, candidate)
                    if result.is_proven:
                        receipt, error = validate_receipt(result.receipt_path, candidate.id)
                        if not receipt:
                            raise ValueError(f"Invalid accepted proof: {error}")
                        row["direct_library_references"] = _direct_library_references(receipt, wheel.lemmas)
                        initial_ids = {item["lemma_id"] for item in manifest["initial_library"]}
                        row["training_lemma_references"] = sorted(set(row["direct_library_references"]) - initial_ids)
                        row["transitive_training_lemma_references"] = sorted(set(receipt.get("transitive_used_lemma_ids", [])) & (before - initial_ids))
                        row["receipt_sha256"] = sha256(result.receipt_path)
                        if arm == "model_learning" and spec["phase"] == "training":
                            wheel.register_lemma(candidate, result.successful_tactic, receipt_path=result.receipt_path)
                row["elapsed_sec"] = time.monotonic() - t0
                row["library_after"] = sorted(wheel.lemmas)
                row["explanation_status"] = "MODEL_GENERATED_UNREVIEWED" if row.get("explanation") else None
                if spec["phase"] == "evaluation" and set(wheel.lemmas) != before:
                    raise RuntimeError("Evaluation proof leaked into the library")
                if arm != "model_learning" and len(wheel.lemmas) != 7:
                    raise RuntimeError("A frozen library changed")
                if len(row.get("synthesis_attempts", [])) > budget["model_rounds"]:
                    raise RuntimeError("Target exceeded its predeclared host request cap")
                rows.append(row)
                report.update(elapsed_sec=time.monotonic() - started, trained_library_count=len(wheel.lemmas))
                atomic_save_json(report, target_dir / "results.json")
                print(f"{arm} {spec['phase']} {candidate.id}: {row['status']}", flush=True)
                check_frozen(directory, manifest)
            report["state"] = "completed"
        except BaseException as exc:
            report.update(state="interrupted" if isinstance(exc, KeyboardInterrupt) else "aborted", error=str(exc))
            raise
        finally:
            cleanup_error = None
            try:
                prover.cancel()
            except BaseException as exc:
                cleanup_error = exc
                report.update(state="aborted", cleanup_error=str(exc))
            report.update(elapsed_sec=time.monotonic() - started, trained_library_count=len(wheel.lemmas),
                counts=counts(rows), training_counts=counts([r for r in rows if r["phase"] == "training"]),
                evaluation_counts=counts([r for r in rows if r["phase"] == "evaluation"]),
                targets_without_final_verdict=len(manifest["portfolio"]) - len(rows), costs=request_costs(rows, target_dir))
            atomic_save_json(report, target_dir / "results.json")
            if cleanup_error:
                raise RuntimeError("Proof-process cleanup failed; evidence retained") from cleanup_error
    return report


def paired_outcomes(frozen, learning):
    """Compare every held-out pair, keeping losses and all timeout outcomes."""
    left = {r["statement_key"]: r for r in frozen.get("rows", []) if r["phase"] == "evaluation"}
    right = {r["statement_key"]: r for r in learning.get("rows", []) if r["phase"] == "evaluation"}
    pairs = []
    for key in sorted(left.keys() & right.keys()):
        f, g = left[key], right[key]
        fs, gs = f["status"] == "MACHINE_CHECKED_PROVEN", g["status"] == "MACHINE_CHECKED_PROVEN"
        pairs.append({"id": g["id"], "family": g["family"], "classification": g["classification"],
            "frozen_status": f["status"], "learning_status": g["status"],
            "outcome": "both" if fs and gs else "learning_only" if gs else "frozen_only" if fs else "neither",
            "seconds_saved_if_both_certified": f["elapsed_sec"] - g["elapsed_sec"] if fs and gs else None,
            "model_requests_saved_if_both_certified": len(f.get("synthesis_attempts", [])) - len(g.get("synthesis_attempts", [])) if fs and gs else None,
            "training_lemma_references": g.get("training_lemma_references", []) if gs else [],
            "transitive_training_lemma_references": g.get("transitive_training_lemma_references", []) if gs else []})
    return {"pairs": pairs, "paired_targets": len(pairs),
        "unpaired_targets": len(left.keys() ^ right.keys()),
        **{label: sum(p["outcome"] == label for p in pairs) for label in ("both", "learning_only", "frozen_only", "neither")},
        "net_additional_certified_targets": sum((p["outcome"] == "learning_only") - (p["outcome"] == "frozen_only") for p in pairs),
        "certified_targets_referencing_training": sum(bool(p["training_lemma_references"] or p["transitive_training_lemma_references"]) for p in pairs),
        "interpretation": "Observed paired outcomes and source references, not causal necessity or a general learning rate. Timing savings are reported only when both arms certify the same target; setup and training costs remain in each arm report."}


def _arm_summary(report, directory):
    costs = request_costs(report["rows"], directory)
    evaluation = [r for r in report["rows"] if r["phase"] == "evaluation"]
    successes = counts(evaluation)["certified"]
    elapsed = sum(r["elapsed_sec"] for r in evaluation)
    result = {key: report.get(key) for key in ("state", "counts", "training_counts", "evaluation_counts", "elapsed_sec", "trained_library_count", "targets_without_final_verdict")}
    result.update(costs=costs, evaluation_elapsed_sec=elapsed,
        evaluation_certifications_per_hour=3600 * successes / elapsed if elapsed > 0 else None,
        evaluation_model_requests=sum(len(r.get("synthesis_attempts", [])) for r in evaluation),
        observed_training_reference_targets=sum(bool(r.get("training_lemma_references") or r.get("transitive_training_lemma_references")) for r in evaluation))
    return result


def summarize(output_dir):
    directory = Path(output_dir).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    check_frozen(directory, manifest)
    screening = json.loads((directory / "host_screening.json").read_text())["targets"]
    trials = []
    for repetition in range(1, manifest.get("repetitions", 1) + 1):
        arms, reports = {}, {}
        for arm in ARMS:
            path = arm_directory(directory, manifest, arm, repetition) / "results.json"
            if not path.exists():
                arms[arm] = {"state": "not_run"}
                continue
            report = json.loads(path.read_text())
            if report["manifest_sha256"] != sha256(directory / "manifest.json"):
                raise ValueError("Arm report belongs to a different frozen manifest")
            if report.get("repetition", 1) != repetition or report["arm"] != arm:
                raise ValueError("Arm or repetition does not match its directory")
            rows = report["rows"]
            if len(rows) > len(manifest["portfolio"]) or (report["state"] == "completed" and len(rows) != len(manifest["portfolio"])):
                raise ValueError("Completed arm does not cover every frozen target")
            library_names = {item["lemma_id"]: item["lean_name"] for item in manifest["initial_library"]}
            initial_ids = set(library_names)
            permitted_library = set(initial_ids)
            for row, spec in zip(rows, manifest["portfolio"]):
                if any(row[key] != spec[key] for key in ("statement_key", "phase", "family", "conjecture")):
                    raise ValueError("Arm target differs from its frozen protocol")
                if set(row["library_before"]) != permitted_library:
                    raise ValueError("Arm used a library outside the frozen training policy")
                if row["status"] == "MACHINE_CHECKED_PROVEN":
                    receipt, _ = validate_receipt(row["receipt_path"], row["id"])
                    if (sha256(Path(row["receipt_path"])) != row["receipt_sha256"] or not receipt
                            or receipt.get("conjecture") != spec["conjecture"]):
                        raise ValueError("Accepted proof changed or does not certify the frozen target")
                    row["direct_library_references"] = _direct_library_references(receipt, library_names)
                    row["training_lemma_references"] = sorted(set(row["direct_library_references"]) & (permitted_library - initial_ids))
                    row["transitive_training_lemma_references"] = sorted(set(receipt.get("transitive_used_lemma_ids", [])) & (permitted_library - initial_ids))
                    if arm == "model_learning" and spec["phase"] == "training":
                        permitted_library.add(row["id"])
                        library_names[row["id"]] = receipt["theorem_name"]
                else:
                    row["direct_library_references"] = []
                    row["training_lemma_references"] = []
                    row["transitive_training_lemma_references"] = []
                screened = screening[row["id"]]
                if row["status"] == "REFUTED":
                    if screened["status"] == "REFUTED":
                        if row.get("counterexample") != screened.get("counterexample"):
                            raise ValueError("Refutation differs from the frozen host screening")
                    else:
                        validate_model_refutation(row, Conjecture.from_dict(spec["conjecture"]))
                elif screened["status"] == "REFUTED":
                    raise ValueError("A frozen refutation was omitted from the arm outcomes")
                elif row.get("counterexample") is not None or row.get("counterexample_certificate") is not None:
                    raise ValueError("Counterexample attached without a refuted outcome")
                if set(row["library_after"]) != permitted_library:
                    raise ValueError("Evaluation or foreign proof leaked into the library")
            if report.get("counts") != counts(rows):
                raise ValueError("Arm counts do not match the retained target outcomes")
            expected_counts = {"training_counts": counts([r for r in rows if r["phase"] == "training"]),
                               "evaluation_counts": counts([r for r in rows if r["phase"] == "evaluation"]),
                               "trained_library_count": len(permitted_library),
                               "targets_without_final_verdict": len(manifest["portfolio"]) - len(rows)}
            if any(report.get(key) != value for key, value in expected_counts.items()):
                raise ValueError("Phase counts, library count or unfinished targets disagree with retained outcomes")
            reports[arm] = report
            arms[arm] = _arm_summary(report, path.parent)
        trial = {"repetition": repetition, "arms": arms,
                 "paired_learning": paired_outcomes(reports.get("model_frozen", {}), reports.get("model_learning", {}))}
        trials.append(trial)
    comparison = {"manifest_sha256": sha256(directory / "manifest.json"), "setup_elapsed_sec": manifest["setup_elapsed_sec"],
        "profile": manifest.get("profile", "legacy"), "repetitions": len(trials), "trials": trials,
        "all_arms_completed": all(t["arms"][arm]["state"] == "completed" for t in trials for arm in ARMS),
        "aggregate_paired_learning": {key: sum(t["paired_learning"][key] for t in trials) for key in
            ("paired_targets", "both", "learning_only", "frozen_only", "neither", "net_additional_certified_targets", "certified_targets_referencing_training")},
        "aggregation_unit": "target runs across predeclared repetitions, not distinct theorem discoveries",
        "separate_false_control": "REFUTED and certificate replayed; excluded from portfolio counts",
        "limitations": manifest["limitations"]}
    if len(trials) == 1:
        comparison["arms"] = trials[0]["arms"]
    atomic_save_json(comparison, directory / "comparison.json")
    return comparison


def run_all(output_dir):
    directory = Path(output_dir).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    check_frozen(directory, manifest)
    for repetition, order in enumerate(manifest.get("arm_order", [list(ARMS)]), 1):
        for arm in order:
            path = arm_directory(directory, manifest, arm, repetition) / "results.json"
            if path.is_file() and json.loads(path.read_text()).get("state") == "completed":
                summarize(directory)  # Verify retained evidence before continuing.
                continue
            run_arm(directory, arm, repetition)
    return summarize(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prepare_parser = sub.add_parser("prepare", help="Freeze the exact portfolio, receipts, code and configured model; no model requests")
    prepare_parser.add_argument("--output-dir", type=Path, required=True)
    prepare_parser.add_argument("--seed-dir", type=Path, default=ROOT / "research_outputs")
    prepare_parser.add_argument("--profile", choices=("legacy", "focused"), default="legacy")
    prepare_parser.add_argument("--repetitions", type=int, default=1)
    run_parser = sub.add_parser("run-arm", help="Execute one bounded arm, retaining all results")
    run_parser.add_argument("--output-dir", type=Path, required=True)
    run_parser.add_argument("--arm", choices=ARMS, required=True)
    run_parser.add_argument("--repetition", type=int, default=1)
    all_parser = sub.add_parser("run", help="Run every predeclared trial in its frozen order; retain failures and completed arms")
    all_parser.add_argument("--output-dir", type=Path, required=True)
    summary_parser = sub.add_parser("summarize", help="Validate retained receipts and aggregate exact results and request traces")
    summary_parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    result = prepare(args.output_dir, args.seed_dir, args.profile, args.repetitions) if args.command == "prepare" else run_arm(args.output_dir, args.arm, args.repetition) if args.command == "run-arm" else run_all(args.output_dir) if args.command == "run" else summarize(args.output_dir)
    print(json.dumps({key: value for key, value in result.items() if key in {"state", "arm", "counts", "arms", "trials", "aggregate_paired_learning", "setup_elapsed_sec"}}, indent=2))


if __name__ == "__main__":
    main()
