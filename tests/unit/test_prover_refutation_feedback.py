"""Verified prover refutations enter the same persistent boundary feedback as the sieve."""
import copy
import json
import random
import time

import networkx as nx
import pytest

import run_research as runner
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math.sieve.certificates import CounterexampleCertificate
from tests.unit.test_parallel_research import claim, empty_atlas, fake_engine


def refutation(candidate, graph=None):
    graph = nx.empty_graph(1) if graph is None else graph
    _, lhs, rhs = candidate.evaluate(graph)
    certificate = CounterexampleCertificate.from_counterexample_graph(
        graph, candidate, witness={"type": "direct_evaluation", "details": {
            "lhs_value": lhs, "rel": candidate.rel, "rhs_value": rhs}})
    return LeanVerificationResult(status="REFUTED", is_machine_checked=False,
        theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=1,
        counterexample_certificate=certificate.to_dict(),
        diagnostics=[{"exit_code": 1, "stage": "model_counterexample"}],
        synthesis_attempts=[{"status": "COUNTEREXAMPLE_VERIFIED", "usage": {"input_tokens": 8},
                             "response": {"outcome": "counterexample", "explanation": "One vertex refutes it"}}])


def packet(candidate, directory):
    jobs = runner._jobs("proof", [candidate], directory, 1, {candidate.id: "frozen"})
    attempt = refutation(candidate).to_dict()
    record = {"id": candidate.id, "conjecture": candidate.to_dict(), "proof_search_key": "frozen",
              "proof_attempt": attempt, "counterexample": copy.deepcopy(attempt["counterexample_certificate"])}
    return jobs, [{"job_id": jobs[0]["job_id"], "kind": "proof", "records": [record]}]


def test_worker_emits_attached_verified_certificate_and_serialized_trace(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    candidate = claim("one_vertex_refutation", 2)
    monkeypatch.setattr(search, "prove_conjecture", lambda self, candidate, **kwargs: refutation(candidate))
    job = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "frozen"})[0]
    delta = runner._run_job(job, runner._snapshot(empty_atlas()), runner._options(),
                           time.monotonic()+30, [], lambda: None)
    # Actual JSON transport/checkpoint encoding must preserve both certificate copies and the model trace.
    transported = json.loads(json.dumps(delta))
    record = runner._validated_delta_records([transported], [job])[0]
    assert record["counterexample"] == record["proof_attempt"]["counterexample_certificate"]
    assert record["proof_attempt"]["synthesis_attempts"][0]["usage"]["input_tokens"] == 8
    assert record["proof_attempt"]["diagnostics"][0]["exit_code"] == 1
    assert "lean_proof" not in record


@pytest.mark.parametrize("tamper", ["wrong_id", "wrong_hash", "bad_matrix", "not_false", "invalid_guard", "undefined_value"])
def test_parent_independently_rejects_false_or_tampered_certificates(tmp_path, tamper):
    candidate = claim("assigned", 2)
    if tamper == "not_false":
        candidate = claim("assigned", 0)
    elif tamper == "invalid_guard":
        candidate = claim("assigned", 4, guard="is_bipartite")
    elif tamper == "undefined_value":
        candidate = Conjecture.create(id="assigned", lhs=InvariantNode("diameter"), rel="<=", rhs=ConstantNode(0))
    jobs, deltas = packet(candidate, tmp_path)
    record = deltas[0]["records"][0]
    certificate = record["counterexample"]
    if tamper == "wrong_id":
        certificate["conjecture_id"] = "another_claim"
        parsed = CounterexampleCertificate.from_dict(certificate)
        certificate["verification_hash"] = parsed.compute_hash()
    elif tamper == "wrong_hash":
        certificate["verification_hash"] = "0"*64
    elif tamper == "bad_matrix":
        certificate["adjacency_matrix"][0][0] = 1
    elif tamper == "invalid_guard":
        certificate = refutation(candidate, nx.complete_graph(3)).counterexample_certificate
        record["counterexample"] = certificate
    elif tamper == "undefined_value":
        certificate = refutation(candidate, nx.empty_graph(2)).counterexample_certificate
        certificate["refutation_witness"]["details"]["lhs_value"] = 1.0
        certificate["verification_hash"] = CounterexampleCertificate.from_dict(certificate).compute_hash()
        record["counterexample"] = certificate
    record["proof_attempt"]["counterexample_certificate"] = copy.deepcopy(certificate)
    reason = {"invalid_guard": "premise guard", "undefined_value": "nonfinite"}.get(tamper)
    with pytest.raises(ValueError, match=reason):
        runner._validated_delta_records(deltas, jobs)


@pytest.mark.parametrize("contradiction", [
    "missing", "unattached", "different", "unresolved", "machine_checked", "proof", "receipt", "successful_tactic"])
def test_parent_rejects_unattached_or_contradictory_refutation(tmp_path, contradiction):
    candidate = claim("assigned", 2)
    jobs, deltas = packet(candidate, tmp_path)
    record = deltas[0]["records"][0]
    attempt = record["proof_attempt"]
    if contradiction == "missing":
        record.pop("counterexample")
        attempt["counterexample_certificate"] = None
    elif contradiction == "unattached":
        record.pop("counterexample")
    elif contradiction == "different":
        attempt["counterexample_certificate"]["created_at"] = "changed"
    elif contradiction == "unresolved":
        attempt["status"] = "UNRESOLVED"
    elif contradiction == "machine_checked":
        attempt["is_machine_checked"] = True
    elif contradiction == "proof":
        record["lean_proof"] = {"receipt_path": str(tmp_path / "never_read.receipt.json")}
    elif contradiction == "receipt":
        attempt["receipt_path"] = str(tmp_path / "never_read.receipt.json")
    else:
        attempt["successful_tactic"] = "exact impossible"
    with pytest.raises(ValueError):
        runner._validated_delta_records(deltas, jobs)


def install_bounded_fixture(fake_engine, monkeypatch, candidate):
    database, search = fake_engine
    calls = []
    def prove(self, candidate, **kwargs):
        calls.append(candidate.id)
        return refutation(candidate)
    monkeypatch.setattr(search, "prove_conjecture", prove)
    def generate(*args):
        random.random()
        return [candidate]
    monkeypatch.setattr(runner, "_generate", generate)
    monkeypatch.setattr(database, "add_instance", lambda self, graph: database._cached_gi.append(graph), raising=False)
    dispatch = runner._dispatch_jobs
    def inline(*args, **kwargs):
        if len(args) > 6:
            args = (*args[:6], True, *args[7:])
        else:
            kwargs["synchronous"] = True
        return dispatch(*args, **kwargs)
    monkeypatch.setattr(runner, "_dispatch_jobs", inline)
    return database, search, calls


def test_refutation_merges_once_replays_next_plan_and_never_reschedules(fake_engine, monkeypatch, tmp_path):
    candidate = claim("learned_boundary", 2)
    database, search, calls = install_bounded_fixture(fake_engine, monkeypatch, candidate)
    from autonomous_math.prover.flywheel import FlywheelFeedback
    feedback = []
    original = FlywheelFeedback.record_refutation
    def observe(self, candidate, certificate=None):
        feedback.append((candidate.id, certificate.verification_hash))
        return original(self, candidate, certificate)
    monkeypatch.setattr(FlywheelFeedback, "record_refutation", observe)
    initial_rng = random.getstate()
    atlas = empty_atlas()
    atlas["theorems"][candidate.id] = {"id": candidate.id, "statement": candidate.statement,
        "conjecture": candidate.to_dict(), "status": "EMPIRICAL_SURVIVOR",
        "proof_search_key": "obsolete-context", "proof_search_skipped": True,
        "next_retry_at": time.time()+3600,
        "proof_attempt": {"status": "UNRESOLVED", "diagnostics": [{"exit_code": 124}]}}
    before = copy.deepcopy(atlas)
    try:
        working = runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, 1,
            runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options=runner._options())
        record = working["theorems"][candidate.id]
        assert atlas == before  # Only the parent may commit this returned working copy.
        assert record["status"] == "REFUTED" and record["lean_proof"] is None
        assert record["proof_attempt"]["status"] == "REFUTED"
        assert "next_retry_at" not in record and "proof_search_skipped" not in record
        assert working["total_refuted"] == working["total_current_refuted"] == 1
        assert len(working["recent_refutations"]) == len(feedback) == 1
        assert working["batch_metrics"]["proof_targets"] == working["proof_schedule_sequence"] == 1
        working["total_iterations"] = 1
        runner.atomic_save_json(working, tmp_path / "cumulative_discovery_atlas.json")
        loaded = runner.load_snapshot(tmp_path)
        assert loaded["theorems"][candidate.id]["proof_attempt"]["synthesis_attempts"][0]["status"] == "COUNTEREXAMPLE_VERIFIED"
        def reject_unbounded_replay(*args, **kwargs):
            raise AssertionError("Model certificates must use the bounded replay gate")
        monkeypatch.setattr(runner.CounterexampleCertificateVerifier, "verify_with_details", reject_unbounded_replay)
        # A new library/search key cannot revive a genuinely refuted target.
        search.context = "changed-library-after-restart"
        next_batch = runner._bounded_batch({"pairs": [], "triads": []}, loaded, tmp_path, 0, 0, 1,
            runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options=runner._options())
        assert calls == [candidate.id]
        assert next_batch["batch_metrics"]["proof_targets"] == 0
        assert next_batch["total_refuted"] == len(next_batch["recent_refutations"]) == len(feedback) == 1
        assert next_batch["replayed_boundary_graphs"] == 1
        assert database._cached_gi[0].order == 1 and database._cached_gi[0].edges == ()
        assert next_batch["theorems"][candidate.id]["status"] == "REFUTED"
    finally:
        random.setstate(initial_rng)


def test_cancel_after_refutation_merge_rolls_back_checkpoint_rng_and_knowledge(fake_engine, monkeypatch, tmp_path):
    candidate = claim("cancelled_refutation", 2)
    install_bounded_fixture(fake_engine, monkeypatch, candidate)
    from autonomous_math.prover.flywheel import FlywheelFeedback
    stop = runner.GracefulDaemonInterrupt()
    original = FlywheelFeedback.record_refutation
    entered = []
    def interrupt_after_merge(self, candidate, certificate=None):
        entered.append(candidate.id)
        original(self, candidate, certificate)
        stop.stop_requested = True
    monkeypatch.setattr(FlywheelFeedback, "record_refutation", interrupt_after_merge)
    atlas = empty_atlas()
    runner.atomic_save_json(atlas, tmp_path / "cumulative_discovery_atlas.json")
    checkpoint = (tmp_path / "cumulative_discovery_atlas.json").read_bytes()
    initial_rng = random.getstate()
    with pytest.raises(InterruptedError):
        runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, 1, stop,
                              time.monotonic()+30, {}, options=runner._options())
    assert entered == [candidate.id]
    assert atlas == empty_atlas()
    assert random.getstate() == initial_rng
    assert (tmp_path / "cumulative_discovery_atlas.json").read_bytes() == checkpoint


def test_commit_log_counts_empirical_survivors_separately_from_checked(fake_engine, monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(runner, "load_snapshot", lambda directory: empty_atlas())
    def completed(*args, **kwargs):
        atlas = copy.deepcopy(args[1])
        atlas.update(theorems={"checked_a": {"status": "LEAN_CERTIFIED"},
                               "checked_b": {"status": "LEAN_CERTIFIED"},
                               "survivor": {"status": "EMPIRICAL_SURVIVOR"}},
                     total_lean_certified=2, total_survived=3, random_state=random.getstate())
        return atlas
    monkeypatch.setattr(runner, "_bounded_batch", completed)
    initial_rng = random.getstate()
    try:
        runner._execute(tmp_path, [{"pairs": [], "triads": []}], 1, 10, 0, 0, 0, 7,
                        proof_backend="none", model_candidates=0)
    finally:
        random.setstate(initial_rng)
    assert "2 certified, 1 empirical survivors" in capsys.readouterr().out
