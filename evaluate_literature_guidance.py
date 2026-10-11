#!/usr/bin/env python3
"""A bounded before/after literature comparison using each actual source tree.

Review calibration and proof yield have separate denominators. Model candidates,
AI comparisons and finite survivors do not establish new mathematics.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import time

ARMS = ("current", "literature_guided")
BUDGET = {"proposal_requests": 1, "proposal_limit": 4, "proof_targets": 1,
          "model_rounds": 3, "request_timeout_sec": 1200.0,
          "fixed_attempts": 4, "attempt_timeout_sec": 10.0,
          "target_timeout_sec": 3770.0}
MODEL_OPTIONS = {"model": "gpt-6.1-sol", "reasoning_effort": "xhigh"}
LIMITATIONS = [
    "One stochastic pair is a bounded practical comparison, not a general discovery-rate or causal estimate.",
    "The source trees differ intentionally; each arm imports its actual frozen implementation.",
    "No model stochastic seed is controllable. Both arms use the same host seed, atlas and initial checked library.",
    "Read-only CLI access is not a sealed filesystem; inspect retained tool traces before causal interpretation.",
    "A known/routine AI assessment is provisional. A new certified statement is unreviewed until its own literature comparison.",
    "Missing request usage remains unknown. Standard is the requested default CLI tier; absent tier telemetry is not measured tier evidence.",
    "Review backfill, calibration, proposal requests, proof requests and independent kernel replay are reported separately.",
    "Primary text directly treats generation only. The same-target proof pair measures robustness and cost, not a literature-caused proof speedup.",
]


def _read(path):
    return json.loads(Path(path).read_text())


def _hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _save(path, value):
    from autonomous_math.research_state import atomic_save_json
    atomic_save_json(value, Path(path))


def _source_hashes(root):
    root = Path(root)
    paths = [*root.glob("*.py"), root / "pyproject.toml", *sorted((root / "autonomous_math").rglob("*.py"))]
    return {str(p.relative_to(root)): _hash(p) for p in sorted(paths)}


def _worker(directory, arm, action):
    manifest = _read(Path(directory) / "manifest.json")
    root = manifest["source_roots"][arm]
    # Import the evaluator from its saved path, but all engine dependencies from
    # the selected tree. A new evaluator never substitutes its engine for old code.
    code = ("import importlib.util,sys;sys.path.insert(0,sys.argv[1]);"
            "s=importlib.util.spec_from_file_location('literature_worker',sys.argv[2]);"
            "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
            "getattr(m,sys.argv[5])(sys.argv[3],sys.argv[4])")
    subprocess.run([sys.executable, "-B", "-c", code, root, str(Path(__file__).resolve()),
                    str(Path(directory).resolve()), arm, action], cwd=root, check=True)


def _prepare_context(directory, arm):
    from autonomous_math.conjecturing import model_proposals as proposals
    from autonomous_math.novelty.review import get_reviews
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    directory = Path(directory)
    manifest = _read(directory / "manifest.json")
    atlas = _read(directory / "seed_atlas.json")
    atlas["research_family"] = manifest["family"]
    atlas.pop("cached_literature", None)
    atlas.pop("review_feedback", None)
    reviews_dir = manifest["review_directories"][arm]
    reviews = get_reviews(atlas, reviews_dir)
    atlas["review_feedback"] = proposals.build_review_feedback(atlas, reviews, reviews_dir)
    if arm == "literature_guided":
        if not (atlas["review_feedback"].get("cached_literature") or {}).get("sources"):
            raise ValueError("Guided arm needs genuine cached primary statement evidence")
    context = proposals.build_proposal_context(atlas, manifest["workspace_dir"])
    synth = CodexProofSynthesizer(workspace_dir=manifest["workspace_dir"],
        max_rounds=BUDGET["model_rounds"], timeout_per_request=BUDGET["request_timeout_sec"], **MODEL_OPTIONS)
    target = directory / arm
    target.mkdir()
    _save(target / "context_atlas.json", atlas)
    _save(target / "context.json", context)
    _save(target / "reviews.json", reviews)
    _save(target / "configuration.json", synth.configuration())


def prepare(atlas_path, baseline_root, guided_root, baseline_reviews, guided_reviews,
            output_dir, target_id, family="expander_codes", host_seed=5101):
    from autonomous_math.conjecturing.model_proposals import proposal_statement_key
    from autonomous_math.core.ast import Conjecture
    from autonomous_math.prover.trusted_lean import render_challenge
    from autonomous_math.research_state import validate_receipt, workspace_fingerprint
    from run_research import _flywheel, _snapshot
    directory = Path(output_dir).resolve()
    if directory.exists():
        raise ValueError("Evaluation evidence already exists; preserve it")
    directory.mkdir(parents=True)
    atlas = _read(atlas_path)
    fixed = atlas.get("theorems", {}).get(target_id, {})
    if fixed.get("status") != "EMPIRICAL_SURVIVOR" or fixed.get("id") != target_id:
        raise ValueError("Fixed target must be an empirical survivor in the frozen starting atlas")
    candidate = Conjecture.from_dict(fixed["conjecture"])
    render_challenge(candidate)
    _save(directory / "seed_atlas.json", atlas)
    root = Path(guided_root).resolve()
    workspace = (root / "certified_lean").resolve()
    wheel = _flywheel(_snapshot(atlas), directory / "initial_library")
    bindings, fingerprints = [], {}
    for identifier, record in sorted(atlas.get("theorems", {}).items()):
        if record.get("status") != "LEAN_CERTIFIED":
            continue
        path = (record.get("lean_proof") or {}).get("receipt_path", "")
        receipt, error = validate_receipt(path, identifier, fingerprints)
        if not receipt or receipt["conjecture"] != record["conjecture"]:
            raise ValueError(f"Invalid starting receipt {identifier}: {error}")
        bindings.append({"id": identifier, "receipt_path": path, "receipt_sha256": _hash(path),
                         "conjecture": record["conjecture"]})
    if sorted(wheel.lemmas) != sorted(b["id"] for b in bindings):
        raise ValueError("Initial checked library differs from the frozen certified atlas")
    manifest = {"schema_version": 1, "state": "preparing", "arms": list(ARMS),
        "source_roots": {"current": str(Path(baseline_root).resolve()), "literature_guided": str(root)},
        "review_directories": {"current": str(Path(baseline_reviews).resolve()),
                               "literature_guided": str(Path(guided_reviews).resolve())},
        "source_sha256": {}, "frozen_file_sha256": {}, "family": family, "host_seed": host_seed,
        "budget": BUDGET, "model_options": MODEL_OPTIONS, "requested_service_tier": "Standard",
        "workspace_dir": str(workspace), "workspace_sha256": workspace_fingerprint(workspace),
        "initial_library": [lemma.to_dict() for lemma in wheel.lemmas.values()],
        "initial_receipt_bindings": bindings, "limitations": LIMITATIONS,
        "fixed_target": {"id": target_id, "conjecture": candidate.to_dict(),
                         "statement_key": proposal_statement_key(candidate)},
        "admission_policy": "The same predeclared empirical target in both arms. Generated candidates are screened separately and never enter the proof comparison or checked library.",
        "proof_treatment": "Each actual engine searches the same fixed target; cached literature enters the guided proposal request only."}
    _save(directory / "manifest.json", manifest)
    for arm in ARMS:
        _worker(directory, arm, "_prepare_context")
    manifest["source_sha256"] = {arm: _source_hashes(path) for arm, path in manifest["source_roots"].items()}
    paths = [directory / "seed_atlas.json", *(directory / arm / name for arm in ARMS
        for name in ("context_atlas.json", "context.json", "reviews.json", "configuration.json"))]
    manifest["frozen_file_sha256"] = {str(p.relative_to(directory)): _hash(p) for p in paths}
    manifest["evaluator_sha256"] = _hash(__file__)
    manifest["state"] = "frozen"
    _save(directory / "manifest.json", manifest)
    return manifest


def check_frozen(directory, manifest):
    from autonomous_math.research_state import validate_receipt, workspace_fingerprint
    directory = Path(directory)
    if manifest.get("state") != "frozen" or _hash(__file__) != manifest["evaluator_sha256"]:
        raise ValueError("Evaluation code/protocol is not frozen")
    for arm, root in manifest["source_roots"].items():
        if _source_hashes(root) != manifest["source_sha256"][arm]:
            raise ValueError("Frozen engine source changed: " + arm)
    for path, expected in manifest["frozen_file_sha256"].items():
        if _hash(directory / path) != expected:
            raise ValueError("Frozen comparison input changed: " + path)
    if workspace_fingerprint(manifest["workspace_dir"]) != manifest["workspace_sha256"]:
        raise ValueError("Pinned Mathlib workspace changed")
    fingerprints = {}
    for binding in manifest["initial_receipt_bindings"]:
        receipt, error = validate_receipt(binding["receipt_path"], binding["id"], fingerprints)
        if (not receipt or receipt["conjecture"] != binding["conjecture"]
                or _hash(binding["receipt_path"]) != binding["receipt_sha256"]):
            raise ValueError("Frozen proof binding changed: " + str(error))


def run_arm(output_dir, arm):
    directory = Path(output_dir).resolve()
    manifest = _read(directory / "manifest.json")
    check_frozen(directory, manifest)
    if arm not in ARMS:
        raise ValueError("Unknown comparison arm")
    if arm == "literature_guided":
        before = directory / "current" / "results.json"
        if not before.is_file() or _read(before).get("state") != "completed":
            raise ValueError("Current arm must finish first; preserve any abort")
    if (directory / arm / "results.json").exists():
        raise ValueError("Arm results already exist; preserve them")
    _worker(directory, arm, "_run_arm")
    return _read(directory / arm / "results.json")


def _run_arm(output_dir, arm):
    from autonomous_math.conjecturing import model_proposals as proposals
    from autonomous_math.core.ast import Conjecture
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    from autonomous_math.prover.flywheel import FlywheelLemma, LemmaFlywheel
    from autonomous_math.prover.lean_prover import LeanProofSearch
    from autonomous_math.research_state import validate_receipt
    from autonomous_math.sieve.instance_db import InstanceDatabase
    from evaluate_generative import request_costs, screen, validate_model_refutation
    from run_research import replay_counterexamples
    directory = Path(output_dir)
    manifest = _read(directory / "manifest.json")
    check_frozen(directory, manifest)
    target = directory / arm
    atlas = _read(target / "context_atlas.json")
    context = proposals.build_proposal_context(atlas, manifest["workspace_dir"])
    if context != _read(target / "context.json"):
        raise ValueError("Actual arm context differs from its frozen context")
    budget = manifest["budget"]
    synth = CodexProofSynthesizer(workspace_dir=manifest["workspace_dir"], max_rounds=budget["model_rounds"],
        timeout_per_request=budget["request_timeout_sec"], **manifest["model_options"])
    if json.dumps(synth.configuration(), sort_keys=True) != json.dumps(_read(target / "configuration.json"), sort_keys=True):
        raise ValueError("Model configuration changed after freeze")
    wheel = LemmaFlywheel(storage_path=target / "flywheel.json")
    wheel.lemmas = {item["lemma_id"]: FlywheelLemma(**item) for item in manifest["initial_library"]}
    initial = sorted(wheel.lemmas)
    prover = LeanProofSearch(flywheel=wheel, auto_register_flywheel=False, synthesizer=synth,
        max_attempts=budget["fixed_attempts"], timeout_per_attempt=budget["attempt_timeout_sec"],
        total_timeout_sec=budget["target_timeout_sec"])
    report = {"state": "running", "arm": arm, "manifest_sha256": _hash(directory / "manifest.json"),
              "library_before": initial, "proposal": {}, "screens": [], "proofs": [], "budget": budget,
              "fixed_target": manifest["fixed_target"]}
    _save(target / "results.json", report)
    rng, started = random.getstate(), time.monotonic()
    try:
        random.seed(manifest["host_seed"])
        InstanceDatabase.clear_cache()
        database = InstanceDatabase()
        replay_counterexamples(atlas)
        report["catalog_graph_hashes"] = sorted(g.canonical_hash for g in database._cached_gi)
        candidates, report["proposal"] = proposals.propose_candidates(synth, atlas, target / "proposal",
            time.monotonic() + budget["request_timeout_sec"], limit=budget["proposal_limit"])
        prior = {proposals.proposal_statement_key(Conjecture.from_dict(r["conjecture"])): r
                 for r in atlas["theorems"].values() if r.get("conjecture")}
        reviews = {r["id"]: r for r in _read(target / "reviews.json").get("records", [])}
        for candidate in candidates:
            row = screen(candidate, database)
            previous = prior.get(row["statement_key"], {})
            comparison = reviews.get(previous.get("id"), {})
            row.update(duplicate_seed_statement=row["statement_key"] in prior,
                       prior_exact_status=previous.get("status"),
                       prior_review_outcome=(comparison.get("ai_review") or {}).get("outcome")
                           or comparison.get("automatic_status"),
                       proposal_literature_comparison=candidate.metadata.get("literature_comparison"))
            report["screens"].append(row)
        candidate = Conjecture.from_dict(manifest["fixed_target"]["conjecture"])
        report["fixed_target_screen"] = screen(candidate, database)
        if report["fixed_target_screen"]["status"] == "SURVIVED":
            t0 = time.monotonic()
            result = prover.prove_conjecture(candidate, output_dir=target / "verified",
                                            total_timeout_sec=budget["target_timeout_sec"])
            row = {"id": candidate.id, "conjecture": candidate.to_dict(),
                   "statement_key": proposals.proposal_statement_key(candidate),
                   **result.to_dict(), "elapsed_sec": time.monotonic() - t0}
            if result.is_proven:
                receipt, error = validate_receipt(result.receipt_path, candidate.id)
                if not receipt or receipt["conjecture"] != candidate.to_dict():
                    raise ValueError("Accepted proof exact binding failed: " + str(error))
                row.update(receipt_sha256=_hash(result.receipt_path), source_sha256=receipt["source_sha256"],
                           literature_status="UNREVIEWED_NEW_CERTIFIED_STATEMENT")
            elif result.status == "REFUTED":
                row["counterexample"] = row["counterexample_certificate"]
                validate_model_refutation(row, candidate)
            if len(row.get("synthesis_attempts", [])) > budget["model_rounds"]:
                raise ValueError("Frozen proof request cap exceeded")
            report["proofs"].append(row)
        else:
            report["proof_admission_reason"] = "fixed_target_host_check_did_not_survive"
        if sorted(wheel.lemmas) != initial:
            raise ValueError("Result leaked into the frozen checked library")
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
            random.setstate(rng)
            InstanceDatabase.clear_cache()
            report.update(elapsed_sec=time.monotonic() - started, library_after=sorted(wheel.lemmas),
                          costs=request_costs(report["proofs"], target))
            _save(target / "results.json", report)


def summarize(output_dir):
    from autonomous_math.research_state import validate_receipt
    from evaluate_generative import request_costs, validate_model_refutation
    from autonomous_math.core.ast import Conjecture
    directory = Path(output_dir)
    manifest = _read(directory / "manifest.json")
    check_frozen(directory, manifest)
    rows, catalogs = [], []
    initial = sorted(item["lemma_id"] for item in manifest["initial_library"])
    for arm in ARMS:
        path = directory / arm / "results.json"
        if not path.is_file():
            rows.append({"arm": arm, "state": "not_run"})
            continue
        report = _read(path)
        if (report["manifest_sha256"] != _hash(directory / "manifest.json") or report["arm"] != arm
                or report["library_before"] != initial or report["library_after"] != initial
                or report["budget"] != manifest["budget"] or report["fixed_target"] != manifest["fixed_target"]
                or len(report["proofs"]) > manifest["budget"]["proof_targets"]):
            raise ValueError("Arm manifest/library/admission binding differs")
        if report.get("catalog_graph_hashes") is not None:
            catalogs.append(report["catalog_graph_hashes"])
        for proof in report["proofs"]:
            if (proof["conjecture"] != manifest["fixed_target"]["conjecture"]
                    or proof["statement_key"] != manifest["fixed_target"]["statement_key"]):
                raise ValueError("Proof comparison target differs from the predeclared target")
            if proof["status"] == "MACHINE_CHECKED_PROVEN":
                receipt, error = validate_receipt(proof["receipt_path"], proof["id"])
                if not receipt or receipt["conjecture"] != proof["conjecture"] or _hash(proof["receipt_path"]) != proof["receipt_sha256"]:
                    raise ValueError("Certified result binding changed: " + str(error))
            elif proof["status"] == "REFUTED":
                validate_model_refutation(proof, Conjecture.from_dict(proof["conjecture"]))
        screens, proofs = report["screens"], report["proofs"]
        rows.append({"arm": arm, "state": report["state"], "schema_accepted_candidates": len(screens),
            "schema_rejected_candidates": len(report["proposal"].get("rejected", [])),
            "exact_seed_duplicates": sum(s["duplicate_seed_statement"] for s in screens),
            "exact_seed_rediscoveries": sum(s["prior_exact_status"] == "LEAN_CERTIFIED" for s in screens),
            "rediscovery_review_outcomes": dict(Counter(s["prior_review_outcome"] or "unreviewed"
                for s in screens if s["prior_exact_status"] == "LEAN_CERTIFIED")),
            "host_refutations": sum(s["status"] == "REFUTED" for s in screens),
            "host_inconclusive": sum(s["status"] not in {"REFUTED", "SURVIVED"} for s in screens),
            "nonduplicate_survivors": len({s["statement_key"] for s in screens if s["status"] == "SURVIVED" and not s["duplicate_seed_statement"]}),
            "unique_new_certified_statements": len({p["statement_key"] for p in proofs if p["status"] == "MACHINE_CHECKED_PROVEN"}),
            "proved_original_results": None,
            "proof_refuted": sum(p["status"] == "REFUTED" for p in proofs),
            "proof_unresolved": sum(p["status"] not in {"MACHINE_CHECKED_PROVEN", "REFUTED"} for p in proofs),
            "fixed_target_screen_status": report.get("fixed_target_screen", {}).get("status"),
            "elapsed_sec": report["elapsed_sec"], "costs": request_costs(proofs, path.parent),
            "results_path": str(path), "results_sha256": _hash(path)})
    if any(c != catalogs[0] for c in catalogs[1:]):
        raise ValueError("Paired host catalogs differ")
    result = {"manifest_sha256": _hash(directory / "manifest.json"), "fixed_target": manifest["fixed_target"], "arms": rows,
              "all_arms_completed": all(r["state"] == "completed" for r in rows), "limitations": LIMITATIONS}
    _save(directory / "comparison.json", result)
    return result


def compare_reviews(atlas, before, after, identifiers, review_dir, review_attempt_dirs=()):
    """Compare the fixed receipt identities; never turn absent assessments into success."""
    from autonomous_math.novelty.model_review import validate_completed_review
    from autonomous_math.novelty.review import _fingerprint
    from autonomous_math.research_state import validate_receipt
    from evaluate_generative import request_costs
    if len(set(identifiers)) != len(identifiers):
        raise ValueError("Review target identities repeat")
    records = [{r["id"]: r for r in sidecar.get("records", [])} for sidecar in (before, after)]
    rows, fingerprints = [], {}
    for identifier in identifiers:
        theorem = atlas["theorems"][identifier]
        receipt, error = validate_receipt((theorem.get("lean_proof") or {}).get("receipt_path", ""), identifier, fingerprints)
        if not receipt or receipt["conjecture"] != theorem["conjecture"]:
            raise ValueError("Frozen review target receipt invalid: " + str(error))
        fingerprint = _fingerprint(theorem, receipt, theorem["lean_proof"]["receipt_path"])
        row = {"id": identifier, "proof_fingerprint": fingerprint, "certification_preserved": True}
        for label, mapping in zip(("before", "after"), records):
            review = mapping.get(identifier, {})
            if review and review.get("fingerprint") != fingerprint:
                raise ValueError("Review refers to another proof: " + identifier)
            ai = review.get("ai_review") or {}
            item = {"sidecar_status": review.get("status"), "ai_status": ai.get("status"),
                    "ai_outcome": ai.get("outcome"), "source_coverage": ai.get("source_coverage", {}),
                    "assessment_current": None, "assessment_validation_error": None}
            if label == "after" and ai.get("status") == "complete":
                try:
                    validate_completed_review(review, atlas, review_dir, fingerprints)
                    item["assessment_current"] = True
                except (ValueError, OSError) as exc:
                    item.update(assessment_current=False, assessment_validation_error=str(exc))
            row[label] = item
        rows.append(row)
    result = {"fixed_targets": len(rows), "rows": rows,
        "before_ai_outcomes": dict(Counter(r["before"]["ai_outcome"] or "missing" for r in rows)),
        "after_current_ai_outcomes": dict(Counter(r["after"]["ai_outcome"] or "missing" for r in rows if r["after"]["assessment_current"])),
        "after_missing_failed_or_stale": sum(not r["after"]["assessment_current"] for r in rows),
        "all_certifications_preserved": all(r["certification_preserved"] for r in rows),
        "review_costs": request_costs([{"id": f"review_request_{i}",
            "synthesis_attempts": [{"artifact_path": str(Path(path).resolve())}]}
            for i, path in enumerate(review_attempt_dirs)]) if review_attempt_dirs else None,
        "review_usage_scope": "Only explicitly supplied trial request directories, including failed attempts; absent directory accounting is unknown.",
        "interpretation": "Current source-bound AI comparisons, separate from proof yield; no originality or expert endorsement."}
    return result


def calibration_results(review_comparison, expected):
    """Score explicitly chosen live controls; missing/invalid assessments are inconclusive.

    expected maps theorem IDs to allowed provisional outcomes. This does not turn
    unit fixtures or asserted labels into independent mathematical evidence.
    """
    rows = {row["id"]: row for row in review_comparison["rows"]}
    results = []
    for identifier, outcomes in expected.items():
        after = rows.get(identifier, {}).get("after", {})
        current = after.get("assessment_current")
        actual = after.get("ai_outcome")
        results.append({"id": identifier, "expected_outcomes": list(outcomes), "actual_outcome": actual,
            "status": "inconclusive" if not current else "pass" if actual in outcomes else "fail",
            "assessment_validation_error": after.get("assessment_validation_error")})
    return {"controls": results, "counts": dict(Counter(r["status"] for r in results)),
            "interpretation": "Predeclared AI comparison calibration, separate from certified proof yield."}


def replay(output_dir):
    from autonomous_math.prover.lean_prover import LeanToolchain, _target_axiom_report
    from autonomous_math.research_state import ALLOWED_AXIOMS, atomic_save_text, validate_receipt
    directory = Path(output_dir)
    comparison = summarize(directory)
    if not comparison["all_arms_completed"]:
        raise ValueError("Finish both arms before independent proof qualification")
    target = directory / "independent_replay"
    if target.exists():
        raise ValueError("Independent replay evidence already exists; preserve it")
    target.mkdir()
    manifest = _read(directory / "manifest.json")
    toolchain = LeanToolchain(workspace_dir=manifest["workspace_dir"])
    rows, started, state, error = [], time.monotonic(), "running", None
    try:
        for summary in comparison["arms"]:
            report = _read(summary["results_path"])
            for proof in report["proofs"]:
                if proof["status"] != "MACHINE_CHECKED_PROVEN":
                    continue
                receipt, problem = validate_receipt(proof["receipt_path"], proof["id"])
                if not receipt or receipt["conjecture"] != proof["conjecture"]:
                    raise ValueError("Replay exact binding invalid: " + str(problem))
                source = Path(receipt["source_path"]).read_text() + f"\n#print axioms {receipt['theorem_name']}\n"
                path = target / f"{summary['arm']}_{proof['id']}.lean"
                atomic_save_text(source, path)
                code, stdout, stderr = toolchain.run_lean_code(source, timeout=60)
                axioms, problem = _target_axiom_report(stdout, receipt["theorem_name"])
                rows.append({"arm": summary["arm"], "id": proof["id"], "statement_key": proof["statement_key"],
                    "source_path": str(path), "source_sha256": _hash(path), "exit_code": code,
                    "stdout": stdout, "stderr": stderr, "axioms": axioms, "axiom_error": problem,
                    "passed": code == 0 and problem is None and set(axioms) <= ALLOWED_AXIOMS
                        and _hash(receipt["source_path"]) == receipt["source_sha256"]
                        and _hash(proof["receipt_path"]) == proof["receipt_sha256"]})
                _save(path.with_suffix(".json"), rows[-1])
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
            result = {"state": state, "error": error, "rows": rows, "checked_artifacts": len(rows),
                "all_passed": state == "completed" and all(r["passed"] for r in rows),
                "elapsed_sec": time.monotonic() - started,
                "interpretation": "Additional exact-source kernel and axiom replay, outside model-search costs; no originality claim."}
            _save(directory / "independent_replay.json", result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    for name in ("atlas-path", "baseline-root", "guided-root", "baseline-reviews", "guided-reviews", "output-dir", "target-id"):
        p.add_argument("--" + name, required=True)
    p.add_argument("--family", default="expander_codes"); p.add_argument("--host-seed", type=int, default=5101)
    for name in ("run-arm", "summarize", "replay"):
        p = sub.add_parser(name); p.add_argument("--output-dir", required=True)
        if name == "run-arm": p.add_argument("--arm", choices=ARMS, required=True)
    args = vars(parser.parse_args()); command = args.pop("command")
    result = {"prepare": prepare, "run-arm": run_arm, "summarize": summarize, "replay": replay}[command](**args)
    print(json.dumps({key: result[key] for key in ("state", "all_arms_completed", "all_passed") if key in result}, sort_keys=True))


if __name__ == "__main__":
    main()
