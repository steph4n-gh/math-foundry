#!/usr/bin/env python3
"""Small frozen generation comparison; reviews guide, host and kernel decide.

Prepare once, execute each arm once in predeclared alternating order, then replay
accepted sources separately. No generated result enters the seed or any library.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import random
import time

from autonomous_math.conjecturing.model_proposals import build_review_feedback, proposal_statement_key, propose_candidates
from autonomous_math.core.ast import Conjecture
from autonomous_math.novelty.review import get_reviews
from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer, REASONING_EFFORTS
from autonomous_math.prover.flywheel import FlywheelLemma, LemmaFlywheel
from autonomous_math.prover.lean_prover import LeanProofSearch, LeanToolchain, _target_axiom_report
from autonomous_math.research_state import ALLOWED_AXIOMS, atomic_save_json, atomic_save_text, load_snapshot, sha256, validate_receipt, workspace_fingerprint, writer_lock
from autonomous_math.sieve.instance_db import InstanceDatabase
from evaluate_generative import request_costs, screen, validate_model_refutation
from run_research import _flywheel, _snapshot, replay_counterexamples

ROOT = Path(__file__).resolve().parent
ARMS = ("frozen", "review_informed")
PAIRS = (("expander_codes", 4101, ARMS),
         ("degree_and_structural_classes", 4102, tuple(reversed(ARMS))))
BUDGET = {"proposal_limit": 2, "proposal_requests": 1, "proof_targets": 1,
          "model_rounds": 1, "request_timeout_sec": 300.0, "fixed_attempts": 4,
          "attempt_timeout_sec": 10.0, "target_timeout_sec": 360.0,
          "recorded_token_admission_cap": 1_000_000}
LIMITATIONS = [
    "Two stochastic pairs estimate bounded generation/search yield, not general discovery rate or causality.",
    "Both arms use the same frozen checked library and host seeds. The model has no controllable stochastic seed.",
    "Review assertions and suggested gaps are untrusted guidance. No unmatched statement is declared original or nonroutine.",
    "The CLI is read-only but its filesystem is not sealed. It can know mathematics or access previous artifacts; inspect retained tool traces before making a causal claim.",
    "A recorded-token admission cap can stop another call after known usage; it cannot bound an individual call, missing usage, or enforce a hard total token cap.",
    "Independent kernel replay is additional qualification, excluded from arm search costs and denominators.",
]


def source_hashes():
    paths = [Path(__file__), ROOT / "evaluate_generative.py", ROOT / "run_research.py", ROOT / "pyproject.toml",
             *sorted((ROOT / "autonomous_math").rglob("*.py"))]
    return {str(path.relative_to(ROOT)): sha256(path) for path in paths}


def _configuration(budget, model_options=None):
    return CodexProofSynthesizer(workspace_dir=ROOT / "certified_lean", max_rounds=budget["model_rounds"],
        timeout_per_request=budget["request_timeout_sec"], **(model_options or {})).configuration()


def prepare(seed_dir, review_dir, output_dir, model=None, reasoning_effort=None):
    directory, seed, reviews_dir = (Path(p).resolve() for p in (output_dir, seed_dir, review_dir))
    if directory.exists():
        raise ValueError("Evaluation directory already exists; do not replace evidence")
    directory.mkdir(parents=True)
    model_options = {"model": model, "reasoning_effort": reasoning_effort}
    configuration = _configuration(BUDGET, model_options)
    sources = source_hashes()
    atlas = load_snapshot(seed)
    reviews = get_reviews(atlas, reviews_dir)
    feedback = {}
    for family, _, _ in PAIRS:
        feedback[family] = build_review_feedback(dict(atlas, research_family=family), reviews, reviews_dir)
        if not any(item["provenance"] == "completed_source_validated_ai_guidance"
                   and any(comparison.get("source_type") in {"primary_literature", "local_mathlib"}
                           for comparison in item["comparisons"])
                   for item in feedback[family]["entries"]):
            raise ValueError(f"{family} needs a current source-validated relevant completed review before freeze")
    atomic_save_json(atlas, directory / "seed_atlas.json")
    atomic_save_json(feedback, directory / "review_feedback.json")
    wheel = _flywheel(_snapshot(atlas), directory / "initial_library")
    bindings, fingerprints = [], {}
    for identifier, record in sorted(atlas["theorems"].items()):
        if record.get("status") != "LEAN_CERTIFIED":
            continue
        path = record["lean_proof"]["receipt_path"]
        receipt, error = validate_receipt(path, identifier, fingerprints)
        if not receipt or receipt["conjecture"] != record["conjecture"]:
            raise ValueError(f"Invalid seed receipt {identifier}: {error}")
        bindings.append({"id": identifier, "receipt_path": path, "receipt_sha256": sha256(path),
            "conjecture": receipt["conjecture"], "source_sha256": receipt["source_sha256"]})
    if len(wheel.lemmas) != len(bindings):
        raise ValueError("Frozen library differs from certified seed")
    manifest = {"schema_version": 1, "budget": BUDGET, "arms": list(ARMS),
        "pairs": [{"pair": i + 1, "family": family, "host_seed": host_seed, "arm_order": list(order)}
                  for i, (family, host_seed, order) in enumerate(PAIRS)],
        "seed_path": str(seed / "cumulative_discovery_atlas.json"),
        "seed_sha256": sha256(seed / "cumulative_discovery_atlas.json"),
        "seed_atlas_sha256": sha256(directory / "seed_atlas.json"),
        "review_directory": str(reviews_dir), "review_sidecar_sha256": sha256(reviews_dir / "novelty_reviews.json"),
        "review_feedback_sha256": sha256(directory / "review_feedback.json"),
        "initial_library": [lemma.to_dict() for lemma in wheel.lemmas.values()],
        "initial_receipt_bindings": bindings, "source_sha256": sources,
        "workspace_sha256": workspace_fingerprint(ROOT / "certified_lean"),
        "model_options": model_options, "model_configuration": configuration, "limitations": LIMITATIONS,
        "admission_policy": "First returned empirical survivor with exact statement absent from the entire seed atlas; at most one proof target. No post-result target selection.",
        "feedback_policy": "Only review_informed receives frozen relevant feedback. No arm output updates any seed, review context or library."}
    if sources != source_hashes():
        raise RuntimeError("Sources changed during preparation; partial evidence retained")
    atomic_save_json(manifest, directory / "manifest.json")
    return manifest


def check_frozen(directory, manifest):
    if source_hashes() != manifest["source_sha256"]:
        raise RuntimeError("Evaluation source changed after freeze")
    for path, expected in ((directory / "seed_atlas.json", manifest["seed_atlas_sha256"]),
                           (Path(manifest["seed_path"]), manifest["seed_sha256"]),
                           (directory / "review_feedback.json", manifest["review_feedback_sha256"]),
                           (Path(manifest["review_directory"]) / "novelty_reviews.json", manifest["review_sidecar_sha256"])):
        if sha256(path) != expected:
            raise RuntimeError("Frozen input changed: " + str(path))
    if workspace_fingerprint(ROOT / "certified_lean") != manifest["workspace_sha256"]:
        raise RuntimeError("Pinned workspace changed")
    if json.dumps(_configuration(manifest["budget"], manifest.get("model_options")), sort_keys=True) != json.dumps(manifest["model_configuration"], sort_keys=True):
        raise RuntimeError("Configured model/effort/CLI changed")
    atlas = json.loads((directory / "seed_atlas.json").read_text())
    feedback = json.loads((directory / "review_feedback.json").read_text())
    public = get_reviews(atlas, manifest["review_directory"])
    for pair in manifest["pairs"]:
        refreshed = build_review_feedback(dict(atlas, research_family=pair["family"]), public, manifest["review_directory"])
        if refreshed != feedback[pair["family"]]:
            raise RuntimeError("Frozen review/source evidence changed")
    fingerprints = {}
    for binding in manifest["initial_receipt_bindings"]:
        receipt, error = validate_receipt(binding["receipt_path"], binding["id"], fingerprints)
        if (sha256(binding["receipt_path"]) != binding["receipt_sha256"] or not receipt
                or receipt["conjecture"] != binding["conjecture"]):
            raise RuntimeError(f"Frozen receipt changed: {binding['id']}: {error}")


def _ordered_slot(manifest, pair_number, arm):
    order = [(pair["pair"], name) for pair in manifest["pairs"] for name in pair["arm_order"]]
    if (pair_number, arm) not in order:
        raise ValueError("Arm/pair is outside the frozen protocol")
    return order[:order.index((pair_number, arm))]


def run_arm(output_dir, pair_number, arm):
    directory = Path(output_dir).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    started = time.monotonic()
    with writer_lock(directory):
        check_frozen(directory, manifest)
        for previous_pair, previous_arm in _ordered_slot(manifest, pair_number, arm):
            path = directory / f"pair_{previous_pair:02d}" / previous_arm / "results.json"
            if not path.is_file() or json.loads(path.read_text()).get("state") != "completed":
                raise ValueError("Predeclared prior arm has not completed; do not conceal an abort or reorder")
        target = directory / f"pair_{pair_number:02d}" / arm
        if target.exists():
            raise ValueError("Arm already has evidence; do not overwrite or rerun selected results")
        target.mkdir(parents=True)
        pair = next(p for p in manifest["pairs"] if p["pair"] == pair_number)
        atlas = json.loads((directory / "seed_atlas.json").read_text())
        atlas["research_family"] = pair["family"]
        if arm == "review_informed":
            atlas["review_feedback"] = json.loads((directory / "review_feedback.json").read_text())[pair["family"]]
        else:
            atlas.pop("review_feedback", None)
        budget = manifest["budget"]
        wheel = LemmaFlywheel(storage_path=target / "flywheel.json")
        wheel.lemmas = {item["lemma_id"]: FlywheelLemma(**item) for item in manifest["initial_library"]}
        initial = sorted(wheel.lemmas)
        wheel.save()
        synthesizer = CodexProofSynthesizer(workspace_dir=ROOT / "certified_lean", max_rounds=budget["model_rounds"],
                                          timeout_per_request=budget["request_timeout_sec"], **manifest.get("model_options", {}))
        prover = LeanProofSearch(flywheel=wheel, auto_register_flywheel=False, max_attempts=budget["fixed_attempts"],
            timeout_per_attempt=budget["attempt_timeout_sec"], total_timeout_sec=budget["target_timeout_sec"], synthesizer=synthesizer)
        report = {"state": "running", "pair": pair_number, "arm": arm, "family": pair["family"],
            "manifest_sha256": sha256(directory / "manifest.json"), "library_before": initial,
            "proposal": {}, "screens": [], "proofs": [], "budget": budget, "host_seed": pair["host_seed"]}
        atomic_save_json(report, target / "results.json")
        previous_rng = random.getstate()
        try:
            random.seed(pair["host_seed"])
            InstanceDatabase.clear_cache()
            database = InstanceDatabase()
            replay_counterexamples(atlas)
            report["catalog_graph_hashes"] = sorted(g.canonical_hash for g in database._cached_gi)
            if not synthesizer.is_available():
                raise RuntimeError("Configured model CLI unavailable")
            candidates, trace = propose_candidates(synthesizer, atlas, target / "proposal",
                time.monotonic() + budget["request_timeout_sec"], limit=budget["proposal_limit"])
            report["proposal"] = trace
            prior = {proposal_statement_key(Conjecture.from_dict(record["conjecture"])): record.get("status")
                     for record in atlas["theorems"].values() if record.get("conjecture")}
            eligible = []
            for candidate in candidates:
                result = screen(candidate, database)
                key = proposal_statement_key(candidate)
                result["prior_exact_status"] = prior.get(key)
                result["duplicate_seed_statement"] = key in prior
                report["screens"].append(result)
                if result["status"] == "SURVIVED" and key not in prior:
                    eligible.append(candidate)
            proposal_cost = request_costs([], target / "proposal")
            used = proposal_cost["recorded_usage_sums"]
            known_tokens = used.get("input_tokens", 0) + used.get("output_tokens", 0)
            report["token_admission"] = {"known_input_plus_output": known_tokens,
                "missing_usage_requests": proposal_cost["requests_with_missing_usage"],
                "cap": budget["recorded_token_admission_cap"], "hard_cap_enforced": False}
            if eligible and known_tokens < budget["recorded_token_admission_cap"]:
                candidate = eligible[0]
                t0 = time.monotonic()
                result = prover.prove_conjecture(candidate, output_dir=target / "verified", total_timeout_sec=budget["target_timeout_sec"])
                row = {"id": candidate.id, "conjecture": candidate.to_dict(), "statement_key": proposal_statement_key(candidate),
                       **result.to_dict(), "elapsed_sec": time.monotonic() - t0}
                if result.is_proven:
                    receipt, error = validate_receipt(result.receipt_path, candidate.id)
                    if not receipt or receipt["conjecture"] != candidate.to_dict():
                        raise ValueError("Accepted proof failed exact receipt binding: " + str(error))
                    row["receipt_sha256"] = sha256(result.receipt_path)
                    row["source_sha256"] = receipt["source_sha256"]
                elif result.status == "REFUTED":
                    row["counterexample"] = row["counterexample_certificate"]
                    validate_model_refutation(row, candidate)
                if len(row.get("synthesis_attempts", [])) > budget["model_rounds"]:
                    raise RuntimeError("Proof exceeded the frozen request cap")
                report["proofs"].append(row)
            else:
                report["proof_admission_reason"] = "recorded_token_cap_reached" if eligible else "no_nonduplicate_empirical_survivor"
            if sorted(wheel.lemmas) != initial:
                raise RuntimeError("Evaluation result leaked into the frozen library")
            check_frozen(directory, manifest)
            report["state"] = "completed"
        except BaseException as exc:
            report.update(state="interrupted" if isinstance(exc, (KeyboardInterrupt, InterruptedError)) else "aborted", error=str(exc))
            raise
        finally:
            try:
                prover.cancel()
            except BaseException as exc:
                report.update(state="aborted", cleanup_error=str(exc))
                raise
            finally:
                random.setstate(previous_rng)
                InstanceDatabase.clear_cache()
                report.update(elapsed_sec=time.monotonic() - started, library_after=sorted(wheel.lemmas),
                              costs=request_costs(report["proofs"], target))
                atomic_save_json(report, target / "results.json")
    return report


def summarize(output_dir):
    directory = Path(output_dir).resolve()
    manifest = json.loads((directory / "manifest.json").read_text())
    check_frozen(directory, manifest)
    summaries = []
    fingerprints = {}
    initial_ids = sorted(item["lemma_id"] for item in manifest["initial_library"])
    pair_catalogs = {}
    for pair in manifest["pairs"]:
        for arm in pair["arm_order"]:
            target = directory / f"pair_{pair['pair']:02d}" / arm
            path = target / "results.json"
            if not path.is_file():
                summaries.append({"pair": pair["pair"], "arm": arm, "state": "not_run"})
                continue
            report = json.loads(path.read_text())
            if (report["manifest_sha256"] != sha256(directory / "manifest.json")
                    or report["library_before"] != initial_ids or report["library_after"] != initial_ids
                    or report["budget"] != manifest["budget"] or report["pair"] != pair["pair"]
                    or report["arm"] != arm or report["family"] != pair["family"]):
                raise ValueError("Arm manifest or library binding differs")
            hashes = report.get("catalog_graph_hashes")
            if hashes is not None:
                if pair["pair"] in pair_catalogs and hashes != pair_catalogs[pair["pair"]]:
                    raise ValueError("Paired host catalogs differ")
                pair_catalogs[pair["pair"]] = hashes
            for proof in report["proofs"]:
                candidate = Conjecture.from_dict(proof["conjecture"])
                if proof["status"] == "MACHINE_CHECKED_PROVEN":
                    receipt, error = validate_receipt(proof["receipt_path"], candidate.id, fingerprints)
                    if (not receipt or receipt["conjecture"] != candidate.to_dict()
                            or sha256(proof["receipt_path"]) != proof["receipt_sha256"]):
                        raise ValueError("Accepted result binding changed: " + str(error))
                elif proof["status"] == "REFUTED":
                    validate_model_refutation(proof, candidate)
            if len(report["proofs"]) > manifest["budget"]["proof_targets"]:
                raise ValueError("Proof target count exceeds the frozen admission cap")
            screens = report["screens"]
            costs = request_costs(report["proofs"], target)
            summaries.append({"pair": pair["pair"], "arm": arm, "state": report["state"],
                "family": pair["family"], "schema_accepted": len(screens),
                "schema_rejected": len(report["proposal"].get("rejected", [])),
                "unique_nonduplicate_survivors": len({s["statement_key"] for s in screens if s["status"] == "SURVIVED" and not s["duplicate_seed_statement"]}),
                "exact_seed_duplicates": sum(s["duplicate_seed_statement"] for s in screens),
                "host_refuted": len({s["statement_key"] for s in screens if s["status"] == "REFUTED"}),
                "host_inconclusive": sum(s["status"] not in {"REFUTED", "SURVIVED"} for s in screens),
                "unique_certified": len({p["statement_key"] for p in report["proofs"] if p["status"] == "MACHINE_CHECKED_PROVEN"}),
                "proof_refuted": sum(p["status"] == "REFUTED" for p in report["proofs"]),
                "proof_unresolved": sum(p["status"] not in {"MACHINE_CHECKED_PROVEN", "REFUTED"} for p in report["proofs"]),
                "elapsed_sec": report["elapsed_sec"], "costs": costs,
                "results_path": str(path), "results_sha256": sha256(path)})
    aggregate = {}
    for arm in ARMS:
        reports = [json.loads(Path(s["results_path"]).read_text()) for s in summaries
                   if s["arm"] == arm and s.get("results_path")]
        aggregate[arm] = {"unique_certified_statements": len({p["statement_key"] for r in reports for p in r["proofs"]
                                                            if p["status"] == "MACHINE_CHECKED_PROVEN"}),
            "unique_nonduplicate_survivors": len({s["statement_key"] for r in reports for s in r["screens"]
                                                if s["status"] == "SURVIVED" and not s["duplicate_seed_statement"]}),
            "completed_arms": sum(r["state"] == "completed" for r in reports),
            "elapsed_sec": sum(r["elapsed_sec"] for r in reports),
            "recorded_cli_requests": sum(s["costs"]["recorded_cli_requests"] for s in summaries if s["arm"] == arm and s.get("costs")),
            "requests_with_missing_usage": sum(s["costs"]["requests_with_missing_usage"] for s in summaries if s["arm"] == arm and s.get("costs"))}
    result = {"manifest_sha256": sha256(directory / "manifest.json"), "arms": summaries, "aggregate": aggregate,
              "all_arms_completed": all(s["state"] == "completed" for s in summaries), "limitations": LIMITATIONS}
    atomic_save_json(result, directory / "comparison.json")
    return result


def replay(output_dir):
    """Independently compile exact admitted sources; no request, registration or retry."""
    directory = Path(output_dir).resolve()
    comparison = summarize(directory)
    if not comparison["all_arms_completed"]:
        raise ValueError("Finish all arms before extra compiler qualification")
    target = directory / "independent_replay"
    if target.exists():
        raise ValueError("Replay evidence already exists; preserve it")
    target.mkdir()
    toolchain = LeanToolchain(workspace_dir=ROOT / "certified_lean")
    rows, started = [], time.monotonic()
    state, error = "running", None
    try:
        for summary in comparison["arms"]:
            report = json.loads(Path(summary["results_path"]).read_text())
            for proof in report["proofs"]:
                if proof["status"] != "MACHINE_CHECKED_PROVEN":
                    continue
                receipt, error = validate_receipt(proof["receipt_path"], proof["id"])
                if not receipt or receipt["conjecture"] != proof["conjecture"]:
                    raise ValueError("Replay receipt binding invalid: " + str(error))
                name = f"pair_{summary['pair']:02d}_{summary['arm']}_{proof['id']}"
                source = Path(receipt["source_path"]).read_text()
                audit_source = source + f"\n#print axioms {receipt['theorem_name']}\n"
                audit_path = target / (name + ".lean")
                atomic_save_text(audit_source, audit_path)
                t0 = time.monotonic()
                code, stdout, stderr = toolchain.run_lean_code(audit_source, timeout=60)
                axioms, audit_error = _target_axiom_report(stdout, receipt["theorem_name"])
                passed = (code == 0 and audit_error is None and set(axioms) <= ALLOWED_AXIOMS
                          and sha256(receipt["source_path"]) == receipt["source_sha256"]
                          and sha256(proof["receipt_path"]) == proof["receipt_sha256"])
                row = {"pair": summary["pair"], "arm": summary["arm"], "id": proof["id"],
                    "statement_key": proof["statement_key"], "conjecture": proof["conjecture"],
                    "source_sha256": receipt["source_sha256"], "audit_source_path": str(audit_path),
                    "audit_source_sha256": sha256(audit_path), "exit_code": code, "stdout": stdout, "stderr": stderr,
                    "axioms": axioms, "audit_error": audit_error, "passed": passed, "elapsed_sec": time.monotonic() - t0}
                atomic_save_json(row, target / (name + ".json"))
                rows.append(row)
        state = "completed"
    except BaseException as exc:
        state, error = "aborted", str(exc)
        raise
    finally:
        try:
            toolchain.cancel()
        except BaseException as exc:
            state, error = "aborted", str(exc)
            raise
        finally:
            result = {"state": state, "error": error, "rows": rows,
                "all_passed": state == "completed" and all(r["passed"] for r in rows), "checked_artifacts": len(rows),
                "unique_statements": len({r["statement_key"] for r in rows}), "elapsed_sec": time.monotonic() - started,
                "scope": "Extra exact-source genuine-kernel qualification; outside search budgets. No originality assessment."}
            atomic_save_json(result, directory / "independent_replay.json")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("--seed-dir", required=True); p.add_argument("--review-dir", required=True); p.add_argument("--output-dir", required=True)
    p.add_argument("--model", help="Freeze an explicit model override for every arm.")
    p.add_argument("--reasoning-effort", choices=REASONING_EFFORTS)
    for name in ("run-arm", "summarize", "replay"):
        p = sub.add_parser(name); p.add_argument("--output-dir", required=True)
        if name == "run-arm":
            p.add_argument("--pair", type=int, required=True); p.add_argument("--arm", choices=ARMS, required=True)
    args = parser.parse_args()
    if args.command == "prepare": result = prepare(args.seed_dir, args.review_dir, args.output_dir, args.model, args.reasoning_effort)
    elif args.command == "run-arm": result = run_arm(args.output_dir, args.pair, args.arm)
    elif args.command == "replay": result = replay(args.output_dir)
    else: result = summarize(args.output_dir)
    print(json.dumps({key: result[key] for key in ("state", "all_arms_completed", "all_passed") if key in result}, sort_keys=True))


if __name__ == "__main__":
    main()
