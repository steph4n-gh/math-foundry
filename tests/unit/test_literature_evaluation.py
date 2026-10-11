"""Frozen protocol regressions; fixtures are never live proof-yield evidence."""
import copy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

import evaluate_literature_guidance as evaluation
from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.novelty import model_review, review
from autonomous_math.prover.flywheel import FlywheelLemma
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math import research_state
import run_research


def candidate(identifier, bound):
    return Conjecture.create(id=identifier, lhs=InvariantNode("max_degree"), rel="<=", rhs=ConstantNode(bound))


def test_worker_imports_actual_selected_source_tree(tmp_path, monkeypatch):
    roots = {arm: tmp_path / arm for arm in evaluation.ARMS}
    for arm, root in roots.items():
        root.mkdir()
        (root / "engine_identity.py").write_text(f"VALUE = {arm!r}\n")
    helper = tmp_path / "worker.py"
    helper.write_text("from pathlib import Path\nimport engine_identity\n"
        "def _run_arm(directory, arm):\n Path(directory, arm + '.txt').write_text(engine_identity.VALUE)\n")
    (tmp_path / "manifest.json").write_text(json.dumps({"source_roots": {k: str(v) for k, v in roots.items()}}))
    monkeypatch.setattr(evaluation, "__file__", str(helper))
    for arm in evaluation.ARMS:
        evaluation._worker(tmp_path, arm, "_run_arm")
        assert (tmp_path / (arm + ".txt")).read_text() == arm


def test_prepare_requires_a_fixed_empirical_target_before_any_model_request(tmp_path):
    path = tmp_path / "atlas.json"
    path.write_text('{"theorems": {}}')
    with pytest.raises(ValueError, match="empirical survivor"):
        evaluation.prepare(path, tmp_path, tmp_path, tmp_path, tmp_path,
                           tmp_path / "comparison", "missing_target")


def test_frozen_input_and_engine_mutation_abort(tmp_path, monkeypatch):
    root = tmp_path / "engine"; root.mkdir()
    code = root / "run.py"; code.write_text("# frozen\n")
    (root / "pyproject.toml").write_text("# frozen\n")
    seed = tmp_path / "seed_atlas.json"; seed.write_text("{}")
    monkeypatch.setattr(research_state, "workspace_fingerprint", lambda *_: "workspace")
    manifest = {"state": "frozen", "evaluator_sha256": evaluation._hash(evaluation.__file__),
        "source_roots": {"current": str(root)},
        "source_sha256": {"current": evaluation._source_hashes(root)},
        "frozen_file_sha256": {"seed_atlas.json": evaluation._hash(seed)},
        "workspace_dir": str(root), "workspace_sha256": "workspace", "initial_receipt_bindings": []}
    evaluation.check_frozen(tmp_path, manifest)
    seed.write_text('{"mutated": true}')
    with pytest.raises(ValueError, match="input changed"):
        evaluation.check_frozen(tmp_path, manifest)
    seed.write_text("{}")
    code.write_text("# changed\n")
    with pytest.raises(ValueError, match="engine source changed"):
        evaluation.check_frozen(tmp_path, manifest)


@pytest.fixture
def arms(tmp_path, monkeypatch):
    seed = candidate("seed", 123)
    fixed_target = candidate("fixed_target", 456)
    lemma = FlywheelLemma(lemma_id="seed", statement=seed.statement, lean_name="seed", lean_prop="True", tactic="trivial")
    manifest = {"budget": evaluation.BUDGET, "model_options": evaluation.MODEL_OPTIONS,
        "initial_library": [lemma.to_dict()], "workspace_dir": str(tmp_path), "host_seed": 5101,
        "fixed_target": {"id": fixed_target.id, "conjecture": fixed_target.to_dict(),
                         "statement_key": proposals.proposal_statement_key(fixed_target)}}
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    atlas = {"theorems": {"seed": {"id": "seed", "conjecture": seed.to_dict(), "status": "LEAN_CERTIFIED"}}}
    context = {"checked": "same"}
    for arm in evaluation.ARMS:
        target = tmp_path / arm; target.mkdir()
        (target / "context_atlas.json").write_text(json.dumps(atlas))
        (target / "context.json").write_text(json.dumps(context))
        (target / "configuration.json").write_text("{}")
        (target / "reviews.json").write_text('{"records": []}')
    monkeypatch.setattr(evaluation, "check_frozen", lambda *args: None)
    monkeypatch.setattr(proposals, "build_proposal_context", lambda *args: copy.deepcopy(context))
    monkeypatch.setattr(run_research, "replay_counterexamples", lambda *args: None)
    from autonomous_math.sieve import instance_db
    class DB:
        _cached_gi = [SimpleNamespace(canonical_hash="same_graph")]
        @classmethod
        def clear_cache(cls): pass
    monkeypatch.setattr(instance_db, "InstanceDatabase", DB)
    from autonomous_math.prover import codex_synthesis, lean_prover
    class Synth:
        def __init__(self, **kwargs):
            assert kwargs["model"] == "gpt-6.1-sol" and kwargs["reasoning_effort"] == "xhigh"
            assert kwargs["max_rounds"] == 3 and kwargs["timeout_per_request"] == 1200
        def configuration(self): return {}
    monkeypatch.setattr(codex_synthesis, "CodexProofSynthesizer", Synth)
    import evaluate_generative
    monkeypatch.setattr(evaluate_generative, "screen", lambda c, db: {"id": c.id, "conjecture": c.to_dict(),
        "statement_key": proposals.proposal_statement_key(c), "status": "SURVIVED"})
    calls = []
    def propose(synth, current, directory, deadline, limit):
        assert limit == 4
        directory.mkdir()
        (directory / "trace.json").write_text(json.dumps({"command": ["codex"], "status": "RESPONSE_VALIDATED", "usage": {}}))
        return [seed, candidate("first", 321), candidate("second", 322)], {"status": "VALIDATED"}
    monkeypatch.setattr(proposals, "propose_candidates", propose)
    class Prover:
        def __init__(self, **kwargs):
            assert kwargs["auto_register_flywheel"] is False
            assert kwargs["total_timeout_sec"] == 3770
            self.wheel = kwargs["flywheel"]
        def prove_conjecture(self, c, output_dir, total_timeout_sec):
            assert sorted(self.wheel.lemmas) == ["seed"] and total_timeout_sec == 3770
            calls.append(c.id)
            return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                theorem_name=c.id, conjecture_id=c.id)
        def cancel(self): pass
    monkeypatch.setattr(lean_prover, "LeanProofSearch", Prover)
    return tmp_path, calls


def test_fixed_target_is_independent_of_proposals_and_negative_usage_remains_explicit(arms):
    directory, calls = arms
    frozen = {str(p): p.read_bytes() for p in directory.rglob("context*.json")}
    for arm in evaluation.ARMS:
        evaluation._run_arm(directory, arm)
    assert calls == ["fixed_target", "fixed_target"]
    assert all(Path(p).read_bytes() == data for p, data in frozen.items())
    summary = evaluation.summarize(directory)
    assert summary["all_arms_completed"]
    for arm in summary["arms"]:
        assert arm["unique_new_certified_statements"] == 0 and arm["proof_unresolved"] == 1
        assert arm["exact_seed_rediscoveries"] == 1 and arm["schema_accepted_candidates"] == 3
        assert arm["proved_original_results"] is None
        assert arm["costs"]["recorded_cli_requests"] == 1
        assert arm["costs"]["requests_with_missing_usage"] == 1
        assert arm["costs"]["total_input_plus_output_tokens_if_complete"] is None


def test_protocol_refuses_reorder_rerun_and_catalog_change(arms, monkeypatch):
    directory, calls = arms
    with pytest.raises(ValueError, match="must finish first"):
        evaluation.run_arm(directory, "literature_guided")
    evaluation._run_arm(directory, "current")
    with pytest.raises(ValueError, match="already exist"):
        evaluation.run_arm(directory, "current")
    evaluation._run_arm(directory, "literature_guided")
    path = directory / "literature_guided/results.json"
    changed = json.loads(path.read_text()); changed["catalog_graph_hashes"] = ["other_graph"]
    path.write_text(json.dumps(changed))
    with pytest.raises(ValueError, match="catalogs differ"):
        evaluation.summarize(directory)


def test_aborted_request_is_retained_without_claiming_completed_yield(arms, monkeypatch):
    directory, calls = arms
    def fail(*args, **kwargs): raise RuntimeError("real operational failure")
    monkeypatch.setattr(proposals, "propose_candidates", fail)
    with pytest.raises(RuntimeError, match="operational failure"):
        evaluation._run_arm(directory, "current")
    saved = json.loads((directory / "current/results.json").read_text())
    assert saved["state"] == "aborted" and saved["proofs"] == []
    assert not evaluation.summarize(directory)["all_arms_completed"]


def test_fixed_review_identities_and_calibration_keep_missing_stale_and_losses(tmp_path, monkeypatch):
    atlas, before, after = {"theorems": {}}, {"records": []}, {"records": []}
    receipts = {}
    for identifier in ("griesmer", "zero_forcing", "uncertain"):
        c = candidate(identifier, 123)
        path = tmp_path / (identifier + ".receipt.json"); path.write_text("{}")
        theorem = {"id": identifier, "conjecture": c.to_dict(), "status": "LEAN_CERTIFIED", "lean_proof": {"receipt_path": str(path)}}
        receipt = {"schema_version": 2, "conjecture": c.to_dict(), "source_sha256": "a" * 64,
                   "challenge_sha256": "b" * 64, "workspace_sha256": "c" * 64}
        atlas["theorems"][identifier] = theorem; receipts[str(path)] = receipt
        fingerprint = review._fingerprint(theorem, receipt, path)
        before["records"].append({"id": identifier, "fingerprint": fingerprint,
            "status": "awaiting_review", "ai_review": {"status": "complete", "outcome": "unresolved"}})
        after["records"].append({"id": identifier, "fingerprint": fingerprint,
            "status": "awaiting_review", "ai_review": {"status": "complete", "outcome": "routine_consequence"}})
    monkeypatch.setattr(research_state, "validate_receipt", lambda p, *args: (receipts.get(str(p)), None))
    def validate(record, *args):
        if record["id"] == "uncertain": raise ValueError("Unsafe or changed source quotation")
        return {"assessment": record["ai_review"]}
    monkeypatch.setattr(model_review, "validate_completed_review", validate)
    result = evaluation.compare_reviews(atlas, before, after, list(atlas["theorems"]), tmp_path)
    assert result["fixed_targets"] == 3 and result["all_certifications_preserved"]
    assert result["before_ai_outcomes"] == {"unresolved": 3}
    assert result["after_current_ai_outcomes"] == {"routine_consequence": 2}
    assert result["after_missing_failed_or_stale"] == 1
    controls = evaluation.calibration_results(result, {"griesmer": ["routine_consequence"],
        "zero_forcing": ["known_result"], "uncertain": ["unresolved"], "absent": ["known_result"]})
    assert controls["counts"] == {"pass": 1, "fail": 1, "inconclusive": 2}
    after["records"][0]["fingerprint"] = "other-proof"
    with pytest.raises(ValueError, match="another proof"):
        evaluation.compare_reviews(atlas, before, after, list(atlas["theorems"]), tmp_path)
