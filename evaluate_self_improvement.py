#!/usr/bin/env python3
"""Bounded, reproducible ablation of checked-lemma and counterexample reuse.

The held-out statements are selected consequences of known bounds. This measures
transfer within that portfolio, not novel theorem discovery or general learning.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import time

from autonomous_math.core.ast import BinaryOpNode as B, ConstantNode as C, InvariantNode as I, Conjecture, GuardPredicate
from autonomous_math.prover.flywheel import FlywheelLemma, LemmaFlywheel
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.trusted_lean import bootstrap_candidates, bound_signature
from autonomous_math.research_state import atomic_save_json, load_snapshot, validate_receipt, workspace_fingerprint
from autonomous_math.sieve.certificates import CounterexampleCertificateVerifier
from autonomous_math.sieve.instance_db import InstanceDatabase
from run_research import independent_holdout, replay_counterexamples

ROOT = Path(__file__).resolve().parent


def statement_key(candidate):
    fields = candidate.to_dict()
    return hashlib.sha256(json.dumps({k: fields[k] for k in
        ("lhs_expr", "rel", "rhs_expr", "guard_predicate")}, sort_keys=True).encode()).hexdigest()


def heldout_targets():
    n, m, d, w, chi = (I(k) for k in ("order", "size", "max_degree", "clique_number", "chromatic_number"))
    specs = [
        ("density_margin", B("*", C(2), m), B("*", n, B("+", d, C(1)))),
        ("clique_degree_margin", w, B("+", d, C(2))),
        ("clique_density_composition", B("*", w, B("-", w, C(1))), B("*", n, d)),
        ("clique_edge_margin", B("*", w, B("-", w, C(1))), B("+", B("*", C(2), m), C(1))),
        ("color_order_control", chi, B("+", n, C(1))),
        ("clique_color_control", w, B("+", chi, C(1))),
    ]
    return [Conjecture.create(id=f"evaluation_{name}", lhs=lhs, rel="<=", rhs=rhs,
        metadata={"origin": "evaluation_holdout", "scope": "known-bound consequence"})
        for name, lhs, rhs in specs]


def initial_library(atlas):
    """Select the same three common bounds even after the live library grows."""
    expected = {bound_signature(Conjecture.create(id="initial", lhs=I(left), rel="<=", rhs=I(right)))
        for left, right in (("chromatic_number", "order"), ("clique_number", "chromatic_number"), ("clique_number", "order"))}
    selected = {}
    for item in atlas.get("flywheel_lemmas", []):
        record = atlas["theorems"].get(item["lemma_id"], {})
        receipt, _ = validate_receipt(item["receipt_path"], item["lemma_id"])
        if record.get("status") == "LEAN_CERTIFIED" and receipt:
            candidate = Conjecture.from_dict(receipt["conjecture"])
            signature = bound_signature(candidate)
            if signature in expected:
                selected.setdefault(signature, item)
    if set(selected) != expected:
        raise ValueError("The evaluation requires the three common checked bounds χ≤n, ω≤χ, and ω≤n")
    return list(selected.values())


def counterexample_targets():
    # Training and test statements differ. Test graphs are already in the
    # common strengthened challenger: replay is expected to improve the cheap
    # catalog stage, not change the final refutation verdict.
    guard = GuardPredicate(property_name="is_connected")
    def independence(name, coefficient):
        return Conjecture.create(id=name, lhs=I("independence_number"), rel=">=",
            rhs=B("+", B("*", C(coefficient), I("complement_spectral_radius")), C(1)), guard=guard)
    def signless(name, coefficient):
        return Conjecture.create(id=name, lhs=I("signless_laplacian_spectral_radius"), rel=">=",
            rhs=B("+", B("*", C(coefficient), I("spectral_spread")), B("*", C(.9), I("max_degree"))), guard=guard)
    return ([independence("feedback_train_independence", .25), signless("feedback_train_signless", .25)],
            [independence("feedback_test_independence", .22), signless("feedback_test_signless", .249)])


def counterexample_ablation():
    db = InstanceDatabase()
    attrs = ("_cached_nx", "_cached_gi", "_cached_invariants", "_cached_matrix")
    baseline = {k: getattr(InstanceDatabase, k) for k in attrs}
    train, targets = counterexample_targets()
    atlas = {"theorems": {}}
    for candidate in train:
        result = independent_holdout(candidate)
        if not result.is_refuted:
            raise RuntimeError(f"Missing training refutation: {candidate.id}")
        cert = result.counterexample_certificate
        valid, errors = CounterexampleCertificateVerifier.verify_with_details(cert, candidate)
        if not valid:
            raise RuntimeError(errors)
        atlas["theorems"][candidate.id] = {"id": candidate.id, "conjecture": candidate.to_dict(),
            "counterexample": cert.to_dict()}
    arms = {}
    try:
        for learning in (False, True):
            for key, value in baseline.items():
                setattr(InstanceDatabase, key, dict(value) if isinstance(value, dict) else list(value))
            added = replay_counterexamples(atlas) if learning else 0
            samples = []
            for candidate in targets:
                start = time.monotonic()
                catalog = db.sieve_conjecture(candidate)
                catalog_ms = (time.monotonic() - start) * 1000
                result, stage = catalog, "catalog"
                if result.is_survived:
                    result, stage = independent_holdout(candidate), "holdout"
                certificate = result.counterexample_certificate
                if result.is_refuted and not CounterexampleCertificateVerifier.verify_with_details(certificate, candidate)[0]:
                    raise RuntimeError("Refutation replay failed")
                samples.append({"conjecture": candidate.to_dict(), "status": result.status,
                    "refutation_stage": stage if result.is_refuted else None,
                    "catalog_status": catalog.status, "catalog_ms": catalog_ms,
                    "total_ms": (time.monotonic() - start) * 1000,
                    "certificate": certificate.to_dict() if certificate else None})
            arms["learning" if learning else "frozen"] = {"learned_graphs": added, "samples": samples}
    finally:
        for key, value in baseline.items():
            setattr(InstanceDatabase, key, value)
    return {"training": [c.to_dict() for c in train], "arms": arms}


def proof_arm(directory, learning, initial_lemmas, train, targets, attempts, timeout, budget):
    directory.mkdir(parents=True, exist_ok=True)
    flywheel = LemmaFlywheel(storage_path=directory / "flywheel.json")
    flywheel.lemmas = {item["lemma_id"]: FlywheelLemma(**item) for item in initial_lemmas}
    prover = LeanProofSearch(flywheel=flywheel, auto_register_flywheel=learning,
        max_attempts=attempts, timeout_per_attempt=timeout)
    start = time.monotonic()
    rows = []
    for phase, candidates in (("training", train), ("holdout", targets)):
        for candidate in candidates:
            remaining = budget - (time.monotonic() - start)
            if remaining <= 0:
                rows.append({"phase": phase, "id": candidate.id, "status": "BUDGET_EXHAUSTED", "attempts_count": 0})
                continue
            prover.timeout_per_attempt = min(timeout, remaining / attempts)
            result = prover.prove_conjecture(candidate, output_dir=directory / "verified")
            if result.status in {"ERROR", "TOOLCHAIN_UNAVAILABLE"}:
                raise RuntimeError(result.error_message)
            row = {"phase": phase, "id": candidate.id, "conjecture": candidate.to_dict(), **result.to_dict()}
            if result.is_proven and not validate_receipt(result.receipt_path, candidate.id)[0]:
                raise RuntimeError("Invalid experiment proof receipt")
            rows.append(row)
            # Test-set proofs do not train subsequent test targets. This keeps
            # the held-out evaluation an assessment of training transfer.
            if phase == "holdout" and candidate.id in flywheel.lemmas:
                del flywheel.lemmas[candidate.id]
            print(f"{'learning' if learning else 'frozen'} {phase} {candidate.id}: {result.status}", flush=True)
            atomic_save_json(rows, directory / "results.json")
    return {"learning": learning, "budget_sec": budget, "elapsed_sec": time.monotonic()-start,
        "initial_library_count": len(initial_lemmas), "trained_library_count": len(flywheel.lemmas),
        "training_certified": sum(r["phase"] == "training" and r["status"] == "MACHINE_CHECKED_PROVEN" for r in rows),
        "heldout_certified": sum(r["phase"] == "holdout" and r["status"] == "MACHINE_CHECKED_PROVEN" for r in rows),
        "heldout_attempts": sum(r["attempts_count"] for r in rows if r["phase"] == "holdout"),
        "rows": rows}


def run(output_dir, seed_dir=ROOT / "research_outputs", trials=2, attempts=4, timeout=10.0, budget=240.0):
    output_dir = Path(output_dir).resolve()
    if (output_dir / "manifest.json").exists():
        raise ValueError("Use a fresh experiment directory to preserve the frozen manifest")
    if trials < 1 or attempts < 1 or timeout <= 0 or budget <= 0:
        raise ValueError("Trials, attempts and time budgets must be positive")
    atlas = load_snapshot(seed_dir)
    initial = initial_library(atlas)
    train, targets = bootstrap_candidates(), heldout_targets()
    if {statement_key(c) for c in train} & {statement_key(c) for c in targets}:
        raise ValueError("Training and held-out statements overlap")
    if {c.id for c in train} & {item["lemma_id"] for item in initial}:
        raise ValueError("Starting library already contains the training bounds; choose the pre-training snapshot")
    manifest = {"schema_version": 1, "initial_library": initial, "training": [c.to_dict() for c in train],
        "holdout": [c.to_dict() for c in targets], "trials": trials, "attempts_per_target": attempts,
        "timeout_per_attempt_sec": timeout, "budget_per_arm_sec": budget,
        "workspace_sha256": workspace_fingerprint(ROOT / "certified_lean"),
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [Path(__file__), ROOT/'run_research.py', *sorted((ROOT/'autonomous_math').rglob('*.py'))]},
        "limitations": "Selected known-bound consequences test proof transfer. This is not an estimate of general discovery rate, novelty, or production sampling improvement."}
    atomic_save_json(manifest, output_dir / "manifest.json")
    evidence = {"state": "running", "manifest_sha256": hashlib.sha256((output_dir/'manifest.json').read_bytes()).hexdigest(),
        "counterexample_ablation": counterexample_ablation(), "proof_trials": []}
    for trial in range(trials):
        arms = {}
        for learning in ((False, True) if trial % 2 == 0 else (True, False)):
            name = "learning" if learning else "frozen"
            arms[name] = proof_arm(output_dir/f"trial_{trial}"/name, learning, initial, train, targets, attempts, timeout, budget)
        if any(hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected
               for path, expected in manifest["source_sha256"].items()):
            raise RuntimeError("Experiment source changed during evaluation; rerun with a fresh manifest")
        evidence["proof_trials"].append({"trial": trial, "arms": arms,
            "additional_heldout_certified": arms["learning"]["heldout_certified"] - arms["frozen"]["heldout_certified"]})
        atomic_save_json(evidence, output_dir / "comparison.json")
    evidence["state"] = "completed"
    atomic_save_json(evidence, output_dir / "comparison.json")
    return evidence


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--seed-dir", type=Path, default=ROOT/'research_outputs')
    parser.add_argument("--trials", type=int, default=2)
    parser.add_argument("--max-attempts", type=int, default=4)
    parser.add_argument("--timeout-per-attempt", type=float, default=10)
    parser.add_argument("--budget-per-arm", type=float, default=240)
    args = parser.parse_args()
    run(args.output_dir, args.seed_dir, args.trials, args.max_attempts, args.timeout_per_attempt, args.budget_per_arm)
