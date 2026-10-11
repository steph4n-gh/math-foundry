"""Evaluator isolation and accounting checks; no service calls or Lean launches."""
import json
from pathlib import Path

import networkx as nx
import pytest

import evaluate_generative as evaluation
from autonomous_math.core.ast import Conjecture
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.prover.flywheel import FlywheelLemma
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math.sieve.certificates import CounterexampleCertificate, SieveResult


def test_portfolio_is_formalizable_distinct_and_not_initial():
    rows = evaluation.portfolio()
    assert [row["phase"] for row in rows] == ["training", "training", "evaluation", "evaluation"]
    assert len({row["statement_key"] for row in rows}) == 4
    initial = json.loads((evaluation.ROOT / "library/catalog.json").read_text())["theorems"]
    assert not {row["statement_key"] for row in rows} & {evaluation.statement_key(Conjecture.from_dict(item["conjecture"])) for item in initial}
    assert rows[-1]["classification"] == "predeclared_known_composition"


def test_false_control_replays_host_counterexample():
    candidate = evaluation.false_control()
    graph = GraphInstance.from_networkx(nx.empty_graph(1))
    certificate = CounterexampleCertificate.from_counterexample_graph(graph, candidate)

    class Database:
        def sieve_conjecture(self, conjecture):
            return SieveResult(status="REFUTED", conjecture=conjecture, tested_instances_count=1,
                               checked_instances_count=1, counterexample_certificate=certificate)

    result = evaluation.screen(candidate, Database())
    assert result["status"] == "REFUTED"
    assert result["counterexample_replayed"] is True
    assert result["holdout"] is None


def test_request_costs_include_failed_and_unfinished_without_double_count(tmp_path):
    paths = [tmp_path / name for name in ("accepted", "timeout", "unfinished")]
    for index, path in enumerate(paths):
        path.mkdir()
        usage = {"input_tokens": 10, "cached_input_tokens": 8, "output_tokens": 3} if index != 1 else {}
        (path / "trace.json").write_text(json.dumps({"status": "KERNEL_ACCEPTED" if index == 0 else "TIMEOUT",
            "command": ["codex"], "usage": usage, "actual_model": "configured-model"}))
    rows = [{"id": "target", "synthesis_attempts": [{"artifact_path": str(path)} for path in paths[:2]]}]
    costs = evaluation.request_costs(rows, tmp_path)
    assert costs["host_request_attempts"] == costs["recorded_cli_requests"] == 3
    assert costs["requests_with_missing_usage"] == 1
    assert costs["recorded_usage_sums"] == {"input_tokens": 20, "cached_input_tokens": 16, "output_tokens": 6}
    assert costs["total_input_plus_output_tokens_if_complete"] is None
    assert costs["traces"][-1]["assignment"] == "unfinished_target"
    with pytest.raises(ValueError, match="multiple results"):
        evaluation.request_costs(rows + rows)


def test_initial_library_copies_only_catalog_foundations(tmp_path, monkeypatch):
    catalog = json.loads((evaluation.ROOT / "library/catalog.json").read_text())["theorems"]
    original, records = {}, {}
    for item in catalog:
        receipt_path = tmp_path / f"original-{item['id']}.receipt.json"
        receipt = {"conjecture": item["conjecture"], "source_sha256": item["source_sha256"],
            "source_path": str(evaluation.ROOT / item["source"]), "challenge_path": str(evaluation.ROOT / item["challenge"]),
            "challenge_sha256": evaluation.sha256(evaluation.ROOT / item["challenge"]), "tactic": "checked"}
        receipt_path.write_text(json.dumps(receipt))
        original[str(receipt_path)] = receipt
        records[item["id"]] = {"status": "LEAN_CERTIFIED", "lean_proof": {"receipt_path": str(receipt_path)}}
    records["later_discovery"] = {"status": "LEAN_CERTIFIED", "lean_proof": {"receipt_path": "do-not-read"}}
    monkeypatch.setattr(evaluation, "load_snapshot", lambda *args: {"theorems": records})
    monkeypatch.setattr(evaluation, "validate_receipt", lambda path, *args: (original.get(str(path)) or json.loads(Path(path).read_text()), None))

    def register(wheel, candidate, tactic, receipt_path):
        wheel.lemmas[candidate.id] = FlywheelLemma(lemma_id=candidate.id, statement=candidate.statement,
            lean_name=candidate.id, lean_prop="True", tactic=tactic, receipt_path=str(receipt_path))

    monkeypatch.setattr(evaluation.LemmaFlywheel, "register_lemma", register)
    copied_dir = tmp_path / "new" / "initial"
    initial, bindings = evaluation.initial_library(tmp_path, copied_dir)
    assert len(initial) == len(bindings) == 7
    assert {item["lemma_id"] for item in initial} == {item["id"] for item in catalog}
    assert all(Path(item["receipt_path"]).parent == copied_dir for item in initial)
    assert len(list(copied_dir.glob("*.receipt.json"))) == 7


@pytest.mark.parametrize("arm", evaluation.ARMS)
@pytest.mark.parametrize("profile", ("legacy", "focused"))
def test_only_learning_training_proofs_enter_library(tmp_path, monkeypatch, arm, profile):
    initial = [FlywheelLemma(lemma_id=f"foundation_{i}", statement="foundation", lean_name=f"foundation_{i}",
        lean_prop="True", tactic="trivial").to_dict() for i in range(7)]
    budget = evaluation.BUDGET if profile == "legacy" else evaluation.FOCUSED_BUDGET
    portfolio = evaluation.portfolio() if profile == "legacy" else evaluation.focused_portfolio()
    manifest = {"portfolio": portfolio, "initial_library": initial, "budget": budget, "repetitions": 2}
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    (tmp_path / "host_screening.json").write_text(json.dumps({"targets": {row["conjecture"]["id"]: {"status": "SURVIVED"} for row in manifest["portfolio"]}}))
    monkeypatch.setattr(evaluation, "check_frozen", lambda *args: None)
    monkeypatch.setattr(evaluation, "validate_receipt", lambda *args: ({"source_path": "unused"}, None))
    monkeypatch.setattr(evaluation, "_direct_library_references", lambda *args: [])

    def register(wheel, candidate, tactic, receipt_path):
        wheel.lemmas[candidate.id] = FlywheelLemma(lemma_id=candidate.id, statement=candidate.statement,
            lean_name=candidate.id, lean_prop="True", tactic=tactic)

    monkeypatch.setattr(evaluation.LemmaFlywheel, "register_lemma", register)

    class Synthesizer:
        def __init__(self, **kwargs):
            assert kwargs == {"max_rounds": budget["model_rounds"], "timeout_per_request": budget["request_timeout_sec"]}
        def is_available(self):
            return True

    class Prover:
        def __init__(self, **kwargs):
            assert kwargs["auto_register_flywheel"] is False
            assert kwargs["max_attempts"] == 4 and kwargs["timeout_per_attempt"] == 10
            assert kwargs["total_timeout_sec"] == budget["target_timeout_sec"]
            self.wheel = kwargs["flywheel"]
            self.calls = 0
        def prove_conjecture(self, candidate, output_dir, total_timeout_sec):
            assert total_timeout_sec == budget["target_timeout_sec"]
            expected_extra = min(self.calls, 2) if arm == "model_learning" else 0
            assert len(self.wheel.lemmas) == 7 + expected_extra
            # A previous evaluation success must never be visible here.
            assert "portfolio_independent_set_capacity" not in self.wheel.lemmas
            assert not {r["conjecture"]["id"] for r in portfolio if r["phase"] == "evaluation"} & set(self.wheel.lemmas)
            self.calls += 1
            output_dir.mkdir(parents=True, exist_ok=True)
            receipt = output_dir / f"{candidate.id}.receipt.json"
            receipt.write_text("{}")
            return LeanVerificationResult(status="MACHINE_CHECKED_PROVEN", is_machine_checked=True,
                theorem_name=candidate.id, conjecture_id=candidate.id, successful_tactic="trivial", receipt_path=receipt)
        def cancel(self):
            pass

    monkeypatch.setattr(evaluation, "CodexProofSynthesizer", Synthesizer)
    monkeypatch.setattr(evaluation, "LeanProofSearch", Prover)
    for repetition in (1, 2):
        report = evaluation.run_arm(tmp_path, arm, repetition)
        assert report["state"] == "completed"
        assert report["counts"] == {"certified": len(portfolio), "refuted": 0, "unresolved": 0}
        assert report["trained_library_count"] == (9 if arm == "model_learning" else 7)
        assert report["costs"]["host_request_attempts"] == 0
    with pytest.raises(ValueError, match="already has evidence"):
        evaluation.run_arm(tmp_path, arm)


def test_focused_targets_have_distinct_heldout_families_and_explicit_guard():
    rows = evaluation.focused_portfolio()
    assert len(rows) == len({r["statement_key"] for r in rows}) == 5
    assert [r["phase"] for r in rows] == ["training"] * 2 + ["evaluation"] * 3
    training = {r["family"] for r in rows if r["phase"] == "training"}
    control = rows[-1]
    assert control["family"] not in training
    assert control["classification"] == "unrelated_family_control"
    assert control["conjecture"]["guard_predicate"]["property_name"] == "is_triangle_free"
    initial = json.loads((evaluation.ROOT / "library/catalog.json").read_text())["theorems"]
    assert not {r["statement_key"] for r in rows} & {evaluation.statement_key(Conjecture.from_dict(r["conjecture"])) for r in initial}


def test_paired_metrics_keep_losses_timeouts_and_only_compare_success_times():
    def row(key, proven, seconds):
        return {"id": key, "statement_key": key, "phase": "evaluation", "family": key,
            "classification": "known_result", "status": "MACHINE_CHECKED_PROVEN" if proven else "UNRESOLVED",
            "elapsed_sec": seconds, "synthesis_attempts": []}
    frozen = {"rows": [row("both", True, 10), row("gain", False, 20), row("loss", True, 5), row("timeout", False, 30)]}
    learning = {"rows": [row("both", True, 7), row("gain", True, 50), row("loss", False, 90), row("timeout", False, 30)]}
    learning["rows"][1]["training_lemma_references"] = ["trained"]
    result = evaluation.paired_outcomes(frozen, learning)
    assert result["net_additional_certified_targets"] == 0
    assert all(result[k] == 1 for k in ("both", "learning_only", "frozen_only", "neither"))
    assert result["certified_targets_referencing_training"] == 1
    pairs = {r["id"]: r for r in result["pairs"]}
    assert pairs["both"]["seconds_saved_if_both_certified"] == 3
    assert pairs["gain"]["seconds_saved_if_both_certified"] is None
    assert pairs["loss"]["seconds_saved_if_both_certified"] is None
    assert evaluation.paired_outcomes(frozen, {"rows": []})["unpaired_targets"] == 4


def test_repetition_paths_cannot_cross_protocol_bounds(tmp_path):
    assert evaluation.arm_directory(tmp_path, {}, "fixed") == tmp_path / "fixed"
    assert evaluation.arm_directory(tmp_path, {"repetitions": 2}, "fixed", 2) == tmp_path / "trial_02" / "fixed"
    for repetition in (0, 3, True):
        with pytest.raises(ValueError, match="Repetition"):
            evaluation.arm_directory(tmp_path, {"repetitions": 2}, "fixed", repetition)


def test_summary_rejects_omitted_target_in_completed_arm(tmp_path, monkeypatch):
    manifest = {"portfolio": evaluation.portfolio(), "setup_elapsed_sec": 0, "limitations": []}
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    (tmp_path / "host_screening.json").write_text(json.dumps({"targets": {}}))
    (tmp_path / "fixed").mkdir()
    (tmp_path / "fixed/results.json").write_text(json.dumps({"state": "completed", "arm": "fixed",
        "manifest_sha256": evaluation.sha256(tmp_path / "manifest.json"), "rows": []}))
    monkeypatch.setattr(evaluation, "check_frozen", lambda *args: None)
    with pytest.raises(ValueError, match="every frozen target"):
        evaluation.summarize(tmp_path)


def _unresolved_report(tmp_path, monkeypatch):
    manifest = {"portfolio": evaluation.focused_portfolio(), "setup_elapsed_sec": 0, "limitations": [],
                "initial_library": [{"lemma_id": "foundation", "lean_name": "foundation"}]}
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    targets = {r["conjecture"]["id"]: {"status": "SURVIVED"} for r in manifest["portfolio"]}
    (tmp_path / "host_screening.json").write_text(json.dumps({"targets": targets}))
    rows = [{**r, "id": r["conjecture"]["id"], "status": "UNRESOLVED", "elapsed_sec": 1,
             "library_before": ["foundation"], "library_after": ["foundation"], "synthesis_attempts": [],
             "training_lemma_references": ["forged_unused_training_reference"]} for r in manifest["portfolio"]]
    report = {"state": "completed", "arm": "model_learning", "manifest_sha256": evaluation.sha256(tmp_path / "manifest.json"),
              "rows": rows, "counts": evaluation.counts(rows),
              "training_counts": evaluation.counts(rows[:2]), "evaluation_counts": evaluation.counts(rows[2:]),
              "trained_library_count": 1, "targets_without_final_verdict": 0, "elapsed_sec": 5}
    path = tmp_path / "model_learning/results.json"
    path.parent.mkdir()
    path.write_text(json.dumps(report))
    monkeypatch.setattr(evaluation, "check_frozen", lambda *args: None)
    return path, report


def test_summary_derives_reference_metrics_and_reports_missing_arms(tmp_path, monkeypatch):
    _unresolved_report(tmp_path, monkeypatch)
    result = evaluation.summarize(tmp_path)
    assert result["all_arms_completed"] is False
    assert result["arms"]["model_learning"]["observed_training_reference_targets"] == 0
    assert result["arms"]["model_learning"]["evaluation_counts"]["unresolved"] == 3
    assert result["aggregate_paired_learning"]["paired_targets"] == 0


@pytest.mark.parametrize("field,value", [("training_counts", {}), ("evaluation_counts", {}),
                                        ("trained_library_count", 99), ("targets_without_final_verdict", 9)])
def test_summary_rejects_inconsistent_phase_and_library_totals(tmp_path, monkeypatch, field, value):
    path, report = _unresolved_report(tmp_path, monkeypatch)
    report[field] = value
    path.write_text(json.dumps(report))
    with pytest.raises(ValueError, match="disagree"):
        evaluation.summarize(tmp_path)


def test_summary_rejects_refutation_not_in_frozen_host_screen(tmp_path, monkeypatch):
    path, report = _unresolved_report(tmp_path, monkeypatch)
    report["rows"][0]["status"] = "REFUTED"
    report["rows"][0]["counterexample"] = {"fake": True}
    path.write_text(json.dumps(report))
    with pytest.raises(ValueError, match="consistent non-proof certificate"):
        evaluation.summarize(tmp_path)


def test_model_refutation_surviving_screen_is_replayed_without_library_growth(tmp_path, monkeypatch):
    candidate = evaluation.false_control()
    initial = [FlywheelLemma(lemma_id=f"foundation_{i}", statement="foundation", lean_name=f"foundation_{i}",
        lean_prop="True", tactic="trivial").to_dict() for i in range(7)]
    spec = {**evaluation.portfolio()[0], "conjecture": candidate.to_dict(),
            "statement_key": evaluation.statement_key(candidate)}
    manifest = {"portfolio": [spec], "initial_library": initial, "budget": evaluation.BUDGET,
                "setup_elapsed_sec": 0, "limitations": []}
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    (tmp_path / "host_screening.json").write_text(json.dumps({"targets": {candidate.id: {"status": "SURVIVED"}}}))
    monkeypatch.setattr(evaluation, "check_frozen", lambda *args: None)
    from autonomous_math.sieve.model_counterexamples import verify_model_counterexample
    certificate = verify_model_counterexample({"order": 1, "edges": []}, candidate).to_dict()

    class Synthesizer:
        def __init__(self, **kwargs):
            pass
        def is_available(self):
            return True

    class Prover:
        def __init__(self, **kwargs):
            pass
        def prove_conjecture(self, candidate, **kwargs):
            return LeanVerificationResult(status="REFUTED", is_machine_checked=False,
                theorem_name="main_theorem", conjecture_id=candidate.id, counterexample_certificate=certificate)
        def cancel(self):
            pass

    monkeypatch.setattr(evaluation, "CodexProofSynthesizer", Synthesizer)
    monkeypatch.setattr(evaluation, "LeanProofSearch", Prover)
    report = evaluation.run_arm(tmp_path, "model_learning")
    assert report["counts"] == {"certified": 0, "refuted": 1, "unresolved": 0}
    assert report["trained_library_count"] == 7
    comparison = evaluation.summarize(tmp_path)
    assert comparison["arms"]["model_learning"]["training_counts"]["refuted"] == 1
    path = tmp_path / "model_learning/results.json"
    saved = json.loads(path.read_text())
    saved["rows"][0]["counterexample"]["adjacency_matrix"] = [[1]]
    saved["rows"][0]["counterexample_certificate"] = saved["rows"][0]["counterexample"]
    path.write_text(json.dumps(saved))
    with pytest.raises(ValueError):
        evaluation.summarize(tmp_path)


@pytest.mark.parametrize("field,value", [("is_machine_checked", True), ("receipt_path", "fake.receipt.json"),
                                        ("verified_file_path", "fake.lean"), ("successful_tactic", "trivial"),
                                        ("proof_origin", "model_generated"),
                                        ("counterexample_certificate", None)])
def test_model_refutation_cannot_claim_proof_or_detach_its_certificate(field, value):
    candidate = evaluation.false_control()
    from autonomous_math.sieve.model_counterexamples import verify_model_counterexample
    certificate = verify_model_counterexample({"order": 1, "edges": []}, candidate).to_dict()
    row = {"status": "REFUTED", "is_machine_checked": False,
           "counterexample": certificate, "counterexample_certificate": certificate}
    row[field] = value
    with pytest.raises(ValueError, match="consistent non-proof certificate"):
        evaluation.validate_model_refutation(row, candidate)


@pytest.mark.parametrize("field", ["counterexample", "counterexample_certificate"])
def test_summary_rejects_counterexample_attached_to_nonrefuted_outcome(tmp_path, monkeypatch, field):
    path, report = _unresolved_report(tmp_path, monkeypatch)
    report["rows"][0][field] = {"unsupported": True}
    path.write_text(json.dumps(report))
    with pytest.raises(ValueError, match="Counterexample attached"):
        evaluation.summarize(tmp_path)
