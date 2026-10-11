import copy
import itertools
from types import SimpleNamespace

import networkx as nx
import pytest

import run_research as runner
from autonomous_math.core.ast import Conjecture, InvariantNode, ConstantNode
from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.novelty.frontier import coding_frontier, progress_view, review_route
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.novelty import model_review
from tests.unit.test_review_feedback import reviews_fixture, validated_guidance


def test_missing_evidence_never_gets_extension_priority(reviews_fixture, monkeypatch, tmp_path):
    records, reviews = {}, []
    for identifier in ("a_missing", "z_challenged"):
        record, review, _ = reviews_fixture(identifier)
        records[identifier] = record
        reviews.append(review)
    def validate(row, *args):
        result = copy.deepcopy(validated_guidance())
        if row["id"] == "a_missing":
            result["assessment"].update(outcome="unresolved", challenge={},
                                         uncertainties=["Need the standard forest rank theorem."])
        return result
    monkeypatch.setattr(model_review, "validate_completed_review", validate)
    block = proposals.build_review_feedback({"research_family": "degree_and_structural_classes",
                                            "theorems": records}, {"records": reviews}, tmp_path)
    assert [(x["id"], x["route"]) for x in block["entries"]] == [
        ("z_challenged", "extension_opportunity"), ("a_missing", "evidence_gap")]
    assert block["routing_counts"]["evidence_gap"] == 1
    assert review_route({"outcome": "possible_extension"}) == "evidence_gap"
    assert review_route({"outcome": "possible_extension", "challenge": {"verdict": "evidence_gap"}}) == "evidence_gap"


def test_frontier_witness_independent_exhaustive_check():
    witness = coding_frontier()["witness"]
    graph = nx.Graph(witness["edges"])
    words, stopping = [], []
    for weight in range(1, 8):
        for selection in itertools.combinations(range(7), weight):
            counts = [len(set(graph.neighbors(v)) & set(selection)) for v in range(7)]
            if all(count % 2 == 0 for count in counts): words.append(selection)
            if all(count != 1 for count in counts): stopping.append(selection)
    assert len(words) == 1 and min(map(len, words)) == 4
    assert min(map(len, stopping)) == 3
    assert graph.number_of_edges()-graph.number_of_nodes()+1 == 2


def test_routine_helper_worker_cannot_launch_ai(monkeypatch, tmp_path):
    candidate = Conjecture.create(id="helper", lhs=InvariantNode("order"), rel="<=", rhs=ConstantNode(4))
    observed = {}
    def prove(target, **kwargs):
        observed.update(kwargs)
        return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                                      conjecture_id=target.id, theorem_name=target.id)
    def prover(snapshot, directory, options):
        assert options["proof_backend"] == "none"
        return SimpleNamespace(prove_conjecture=prove)
    monkeypatch.setattr(runner, "_prover", prover)
    options = runner._options(proof_backend="codex", model_request_timeout=1200)
    job = {"job_id": "proof-00", "kind": "proof", "local_only": True, "directory": str(tmp_path),
           "candidates": [candidate.to_dict()], "search_keys": {candidate.id: "local-key"}}
    runner._run_job(job, {}, options, runner.time.monotonic()+100, [], lambda: None)
    assert observed["total_timeout_sec"] <= 50
    assert options["proof_backend"] == "codex"


def test_progress_excludes_running_and_keeps_missing_usage_unknown(tmp_path):
    import json
    for name, trace in {"done": {"status": "COMPLETE", "usage": {"input_tokens": 10, "output_tokens": 2}},
                        "running": {"status": "RUNNING"}}.items():
        directory = tmp_path/name
        directory.mkdir()
        (directory/"trace.json").write_text(json.dumps(trace))
    usage = DashboardDataService(data_dir=tmp_path).get_token_usage()
    row = {"id": "new", "ai_review": {"status": "complete", "outcome": "possible_extension",
                                        "challenge": {"verdict": "cleared_relative_advance"}}}
    report = progress_view([row], usage, {"started_at": 0, "starting_checkpoint": 205,
                                         "starting_certified_ids": ["old"]}, 3600)
    assert report["token_accounting_complete"]
    assert report["cleared_candidates_per_million_recorded_tokens"] == pytest.approx(1_000_000/12)
    assert report["settings_period"]["new_cleared_candidates_per_hour"] == 1
    (tmp_path/"done"/"trace.json").write_text(json.dumps({"status": "TIMEOUT"}))
    report = progress_view([row], DashboardDataService(data_dir=tmp_path).get_token_usage())
    assert not report["token_accounting_complete"]
    assert report["cleared_candidates_per_million_recorded_tokens"] is None


def test_deterministic_routine_comparison_overrides_old_ai_extension():
    row = {"id": "routine", "automatic_status": "routine_consequence",
           "ai_review": {"status": "complete", "outcome": "possible_extension",
                         "challenge": {"verdict": "cleared_relative_advance"}}}
    report = progress_view([row])
    assert report["routes"] == {"routine": 1}
    assert report["cleared_candidate_ids"] == []


def test_dashboard_shows_new_period_before_first_new_checkpoint(monkeypatch, tmp_path):
    import time
    service = DashboardDataService(data_dir=tmp_path)
    period = {"started_at": time.time()-3600, "starting_checkpoint": 207,
              "starting_certified_ids": ["preserved"]}
    monkeypatch.setattr(service, "load_atlas", lambda: {"configuration": {}, "batch_metrics": {}})
    monkeypatch.setattr(service, "get_telemetry", lambda atlas: {"runner": {"frontier_period": period}})
    monkeypatch.setattr(service, "get_novelty_reviews", lambda atlas: {"records": [{"id": "preserved"}]})
    for name in ("get_theorems", "get_counterexamples", "get_flywheel_status"):
        monkeypatch.setattr(service, name, lambda *args, **kwargs: [])
    report = service.get_snapshot()["research_frontier"]["settings_period"]
    assert report["starting_checkpoint"] == 207
    assert report["new_certified_ids"] == []


from tests.unit.test_parallel_research import fake_engine


def test_coordinator_routine_admission_uses_current_receipt_and_retains_helper_jobs(fake_engine, monkeypatch, tmp_path):
    """One real checked foundation; all admission workers are controlled local stubs."""
    import hashlib
    import json
    from autonomous_math.core.ast import BinaryOpNode, GuardPredicate
    from autonomous_math.prover.lean_prover import LeanProofSearch
    from autonomous_math.prover.trusted_lean import expander_code_candidates
    from autonomous_math.research_state import atomic_save_json, load_snapshot, validate_receipt
    from tests.unit.test_parallel_research import empty_atlas

    parent = expander_code_candidates()[2]  # d <= n under the indispensable k >= 1 premise.
    proof = LeanProofSearch(workspace_dir=runner.REPO_ROOT / "certified_lean", max_attempts=1,
                           timeout_per_attempt=30, synthesizer=None).prove_conjecture(
                               parent, output_dir=tmp_path / "checked_foundation")
    assert proof.is_proven, proof.diagnostics
    receipt, error = validate_receipt(proof.receipt_path, parent.id)
    assert not error and receipt["conjecture"] == parent.to_dict()
    parent_row = {"id": parent.id, "status": "LEAN_CERTIFIED", "conjecture": parent.to_dict(),
                  "lean_proof": {"receipt_path": str(proof.receipt_path)}, "discovered_iteration": 0}
    _, search = fake_engine
    observed_jobs, observed_backends = [], []
    dispatch = runner._dispatch_jobs

    def observe_jobs(jobs, *args, **kwargs):
        observed_jobs.extend(copy.deepcopy(job) for job in jobs if job["kind"] == "proof")
        return dispatch(jobs, *args, **kwargs)

    def controlled_prover(snapshot, directory, options):
        observed_backends.append(options["proof_backend"])
        return search()

    monkeypatch.setattr(runner, "_dispatch_jobs", observe_jobs)
    monkeypatch.setattr(runner, "_prover", controlled_prover)
    monkeypatch.setattr(runner, "_synthesizer", lambda *_: pytest.fail("No model may be launched by admission tests"))
    stronger_guard = GuardPredicate(predicate_type="comparison", invariant="parity_code_dimension", op=">=", threshold=2)
    helper_guard = GuardPredicate(predicate_type="comparison", invariant="parity_code_dimension", op=">=", threshold=3)
    cases = [
        ("specialization", Conjecture.create(id="specialization", lhs=parent.lhs_expr, rel=parent.rel,
            rhs=parent.rhs_expr, guard=stronger_guard), "suppressed"),
        ("missing_parent_guard", Conjecture.create(id="missing_parent_guard", lhs=parent.lhs_expr, rel=parent.rel,
            rhs=parent.rhs_expr), "eligible"),
        ("weakening", Conjecture.create(id="weakening", lhs=parent.lhs_expr, rel=parent.rel,
            rhs=BinaryOpNode("+", parent.rhs_expr, ConstantNode(1)), guard=stronger_guard), "suppressed"),
        ("unmatched", Conjecture.create(id="unmatched", lhs=parent.lhs_expr, rel=parent.rel,
            rhs=BinaryOpNode("-", parent.rhs_expr, ConstantNode(1)), guard=stronger_guard), "eligible"),
        ("helper", Conjecture.create(id="helper", lhs=parent.lhs_expr, rel=parent.rel,
            rhs=parent.rhs_expr, guard=helper_guard, metadata={"helper_for": ["missing_parent_guard"]}), "local_helper"),
    ]
    options = dict(runner._options(workers=1, proof_backend="codex", model_request_timeout=1200), replay_boundary=False)
    for name, candidate, expected in cases:
        observed_jobs.clear(); observed_backends.clear(); search.calls.clear()
        atlas = empty_atlas(); atlas["theorems"][parent.id] = copy.deepcopy(parent_row)
        directory = tmp_path / name
        runner._coordinate_candidates([candidate], atlas, directory, 1, runner.GracefulDaemonInterrupt(),
                                     runner.time.monotonic() + 30, {}, options, synchronous=True,
                                     screen_key="controlled-surviving-catalog")
        row = atlas["theorems"][candidate.id]
        assert row["status"] == "EMPIRICAL_SURVIVOR" and row.get("lean_proof") is None
        assert atlas["total_lean_certified"] == 1  # Only the pre-existing foundation is certified.
        if expected == "eligible":
            assert [job["candidates"][0]["id"] for job in observed_jobs] == [candidate.id]
            assert not observed_jobs[0].get("local_only")
            assert search.calls == [candidate.id] and "routine_variant" not in row
            assert atlas["batch_metrics"]["routine_variants_suppressed"] == 0
        else:
            audit = row["routine_variant"]
            binding = {"parent_id": parent.id, "target": candidate.to_dict(), "parent": parent.to_dict()}
            assert audit["parent_ids"] == [parent.id]
            assert audit["relationship"] == ("weakening" if name == "weakening" else "specialization")
            bound = audit["parent_bindings"][parent.id]
            assert bound["receipt_sha256"] == hashlib.sha256(proof.receipt_path.read_bytes()).hexdigest()
            assert bound["conjecture_sha256"] == hashlib.sha256(json.dumps(parent.to_dict(), sort_keys=True).encode()).hexdigest()
            assert all(bound[key] == receipt[key] for key in ("source_sha256", "challenge_sha256",
                "workspace_sha256", "lean_binary_sha256", "axioms"))
            assert audit["binding_sha256"] == hashlib.sha256(json.dumps(binding, sort_keys=True).encode()).hexdigest()
            assert audit["certifies_target"] is False
            atomic_save_json(atlas, directory / "cumulative_discovery_atlas.json")
            persisted = load_snapshot(directory)["theorems"][candidate.id]
            assert persisted["routine_variant"] == audit and persisted["status"] == "EMPIRICAL_SURVIVOR"
            if expected == "suppressed":
                assert observed_jobs == [] and search.calls == [] and observed_backends == []
                assert row["proof_search_skipped"] and "proof_attempt" not in row
                assert atlas["batch_metrics"]["routine_variants_suppressed"] == 1
            else:
                assert len(observed_jobs) == 1 and observed_jobs[0]["local_only"] is True
                assert search.calls == [candidate.id] and observed_backends == ["codex", "none"]
                assert row["proof_search_key"].startswith("local_routine_helper:")
                assert atlas["batch_metrics"]["routine_helpers_local_only"] == 1
