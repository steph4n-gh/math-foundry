"""A bounded proof-certificate replay failure preserves evidence without learning it."""
import copy
import hashlib
import json
import time

import networkx as nx
import pytest

import run_research as runner
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.prover.flywheel import FlywheelFeedback
from autonomous_math.sieve.certificates import CounterexampleCertificate
from autonomous_math.sieve import model_counterexamples
from tests.unit.test_parallel_research import claim, empty_atlas, fake_engine, synchronous
from tests.unit.test_prover_refutation_feedback import packet, refutation


def replay_timeout(monkeypatch, candidate_id, interrupted=None):
    """Fail bounded host evaluation only after real certificate structure checks."""
    original = model_counterexamples._refutation_values

    def evaluate(graph, candidate):
        if candidate.id == candidate_id:
            if interrupted is not None:
                interrupted.append(True)
            raise TimeoutError("Z3 timed out solving chromatic number for k=7")
        return original(graph, candidate)

    monkeypatch.setattr(model_counterexamples, "_refutation_values", evaluate)


def assert_deferred(record, original_attempt, replay_stage):
    attempt = record["proof_attempt"]
    assert attempt["status"] == "UNRESOLVED"
    assert attempt["is_machine_checked"] is False
    assert attempt["counterexample_certificate"] is None
    assert attempt["deferred_counterexample_certificate"] == original_attempt["counterexample_certificate"]
    assert attempt["synthesis_attempts"] == original_attempt["synthesis_attempts"]
    assert attempt["attempts_count"] == original_attempt["attempts_count"]
    assert attempt["diagnostics"][:-1] == original_attempt["diagnostics"]
    diagnostic = attempt["diagnostics"][-1]
    assert diagnostic["phase"] == "proof_refutation_replay"
    assert diagnostic["exit_code"] == 124
    assert diagnostic["failure_kind"] == "verifier_timeout"
    assert diagnostic["replay_stage"] == replay_stage
    assert diagnostic["compiler_launched"] is False
    certificate = original_attempt["counterexample_certificate"]
    graph = GraphInstance.from_networkx(CounterexampleCertificate.from_dict(certificate).to_networkx())
    assert diagnostic["graph_hash"] == graph.canonical_hash
    assert diagnostic["order"] == graph.order and diagnostic["size"] == graph.size
    assert diagnostic["certificate_sha256"] == hashlib.sha256(
        json.dumps(certificate, sort_keys=True).encode()).hexdigest()
    assert diagnostic["conjecture_sha256"] == hashlib.sha256(
        json.dumps(record["conjecture"], sort_keys=True).encode()).hexdigest()
    assert "counterexample" not in record
    assert not record.get("lean_proof")
    assert runner._proof_retry_reason(attempt) == "verifier_timeout"


def test_worker_defers_replay_timeout_and_transports_original_evidence(
        fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    candidate = claim("timed_worker", 2)
    outcome = refutation(candidate)
    original_attempt = copy.deepcopy(outcome.to_dict())
    monkeypatch.setattr(search, "prove_conjecture", lambda self, candidate, **kwargs: outcome)
    replay_timeout(monkeypatch, candidate.id)
    job = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "frozen"})[0]

    delta = runner._run_job(job, runner._snapshot(empty_atlas()), runner._options(),
                            time.monotonic()+30, [], lambda: None)
    transported = json.loads(json.dumps(delta))
    assert_deferred(transported["records"][0], original_attempt, "worker")
    validated = runner._validated_delta_records([transported], [job])
    assert_deferred(validated[0], original_attempt, "worker")
    assert outcome.to_dict() == original_attempt


def test_parent_defers_timeout_without_mutating_the_worker_delta(monkeypatch, tmp_path):
    candidate = claim("timed_parent", 2)
    jobs, deltas = packet(candidate, tmp_path)
    before = copy.deepcopy(deltas)
    replay_timeout(monkeypatch, candidate.id)

    validated = runner._validated_delta_records(deltas, jobs)

    assert_deferred(validated[0], before[0]["records"][0]["proof_attempt"], "parent")
    assert deltas == before


@pytest.mark.parametrize("stage", ["worker", "parent"])
def test_cancellation_after_replay_timeout_aborts_instead_of_deferring(
        fake_engine, monkeypatch, tmp_path, stage):
    _, search = fake_engine
    candidate = claim("cancelled_after_timeout", 2)
    interrupted = []
    replay_timeout(monkeypatch, candidate.id, interrupted)

    def check():
        if interrupted:
            raise InterruptedError("Cancelled after bounded certificate replay")

    if stage == "parent":
        jobs, deltas = packet(candidate, tmp_path)
        before = copy.deepcopy(deltas)
        with pytest.raises(InterruptedError, match="Cancelled after"):
            runner._validated_delta_records(deltas, jobs, check=check)
        assert deltas == before
    else:
        outcome = refutation(candidate)
        before = copy.deepcopy(outcome.to_dict())
        monkeypatch.setattr(search, "prove_conjecture", lambda self, candidate, **kwargs: outcome)
        job = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "frozen"})[0]
        with pytest.raises(InterruptedError, match="Cancelled after"):
            runner._run_job(job, runner._snapshot(empty_atlas()), runner._options(),
                            time.monotonic()+30, [], check)
        assert outcome.to_dict() == before


@pytest.mark.parametrize("stage", ["worker", "parent"])
@pytest.mark.parametrize("tamper", ["hash", "matrix", "wrong_target"])
def test_invalid_evidence_still_fails_before_the_timeout_policy(
        fake_engine, monkeypatch, tmp_path, stage, tamper):
    _, search = fake_engine
    candidate = claim("invalid_evidence", 2)
    outcome = refutation(candidate)
    certificate = outcome.counterexample_certificate
    if tamper == "hash":
        certificate["verification_hash"] = "0"*64
    elif tamper == "matrix":
        certificate["adjacency_matrix"][0][0] = 1
    else:
        certificate["conjecture_id"] = "different_target"
    evaluated = []
    replay_timeout(monkeypatch, candidate.id, evaluated)
    if stage == "worker":
        monkeypatch.setattr(search, "prove_conjecture", lambda self, candidate, **kwargs: outcome)
        job = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "frozen"})[0]
        with pytest.raises(ValueError):
            runner._run_job(job, runner._snapshot(empty_atlas()), runner._options(),
                            time.monotonic()+30, [], lambda: None)
    else:
        jobs, deltas = packet(candidate, tmp_path)
        deltas[0]["records"][0].update(proof_attempt=outcome.to_dict(),
                                      counterexample=copy.deepcopy(certificate))
        before = copy.deepcopy(deltas)
        with pytest.raises(ValueError):
            runner._validated_delta_records(deltas, jobs)
        assert deltas == before
    assert not evaluated  # Tampering is a definite failure, not deferred host work.


def test_parent_contradictory_attachment_remains_fatal(monkeypatch, tmp_path):
    candidate = claim("contradictory_attachment", 2)
    jobs, deltas = packet(candidate, tmp_path)
    deltas[0]["records"][0]["counterexample"]["created_at"] = "changed attachment"
    before = copy.deepcopy(deltas)
    replay_timeout(monkeypatch, candidate.id)
    with pytest.raises(ValueError, match="attached certificate|contradicts"):
        runner._validated_delta_records(deltas, jobs)
    assert deltas == before


def test_parent_timeout_keeps_an_unrelated_valid_refutation(monkeypatch, tmp_path):
    timed, healthy = claim("timed", 2), claim("healthy", 3)
    jobs = runner._jobs("proof", [timed, healthy], tmp_path, 2,
                        {timed.id: "frozen", healthy.id: "frozen"})
    deltas = []
    for job, candidate, graph in zip(jobs, [timed, healthy], [nx.empty_graph(1), nx.empty_graph(2)]):
        attempt = refutation(candidate, graph).to_dict()
        record = {"id": candidate.id, "conjecture": candidate.to_dict(),
                  "proof_search_key": "frozen", "proof_attempt": attempt,
                  "counterexample": copy.deepcopy(attempt["counterexample_certificate"])}
        deltas.append({"job_id": job["job_id"], "kind": "proof", "records": [record]})
    before = copy.deepcopy(deltas)
    replay_timeout(monkeypatch, timed.id)

    records = {r["id"]: r for r in runner._validated_delta_records(deltas, jobs)}

    assert_deferred(records[timed.id], before[0]["records"][0]["proof_attempt"], "parent")
    assert records[healthy.id] == before[1]["records"][0]
    assert records[healthy.id]["proof_attempt"]["status"] == "REFUTED"
    assert deltas == before


def test_coordinator_retries_timed_target_without_refutation_or_boundary_learning(
        fake_engine, monkeypatch, tmp_path):
    database, search = fake_engine
    timed, healthy = claim("A_timed", 2), claim("B_healthy", 3)
    clock, calls, feedback, admitted = [1000.0], [], [], []
    monkeypatch.setattr(runner.time, "time", lambda: clock[0])
    original_feedback = FlywheelFeedback.record_refutation

    def observe(self, candidate, certificate=None):
        feedback.append(candidate.id)
        return original_feedback(self, candidate, certificate)

    def prove(self, candidate, **kwargs):
        calls.append(candidate.id)
        return refutation(candidate, nx.empty_graph(1 if candidate.id == timed.id else 2))

    def admit(self, graph):
        admitted.append((graph.name, graph.order))
        database._cached_gi.append(graph)

    monkeypatch.setattr(FlywheelFeedback, "record_refutation", observe)
    monkeypatch.setattr(search, "prove_conjecture", prove)
    monkeypatch.setattr(database, "add_instance", admit, raising=False)
    replay_timeout(monkeypatch, timed.id)
    atlas = empty_atlas()

    synchronous([timed, healthy], atlas, tmp_path, lean_limit=2)

    record = atlas["theorems"][timed.id]
    assert record["status"] == "EMPIRICAL_SURVIVOR"
    assert not record.get("counterexample") and not record.get("lean_proof")
    assert record["proof_attempt"]["deferred_counterexample_certificate"]["graph_order"] == 1
    assert record["proof_retry_reason"] == "verifier_timeout"
    assert record["proof_retry_count"] == 1
    assert record["next_retry_at"] == 1300.0 and record["next_retry_iteration"] == 3
    assert atlas["total_refuted"] == atlas["total_current_refuted"] == 1
    assert [r["id"] for r in atlas["recent_refutations"]] == [healthy.id]
    assert feedback == [healthy.id]
    assert not any(lemma.get("conjecture_id") == timed.id for lemma in atlas["flywheel_lemmas"])
    deferred = []
    assert runner.replay_counterexamples(atlas, deferred=deferred) == 1
    assert admitted == [(f"learned_{healthy.id}", 2)] and deferred == []

    synchronous([timed, healthy], atlas, tmp_path, lean_limit=2)
    assert calls == [timed.id, healthy.id]
    clock[0], atlas["total_iterations"] = 1400.0, 1
    synchronous([timed, healthy], atlas, tmp_path, lean_limit=2)
    assert calls == [timed.id, healthy.id]  # Elapsed wall time alone cannot bypass checkpoint cooldown.
    atlas["total_iterations"] = 2
    synchronous([timed, healthy], atlas, tmp_path, lean_limit=2)
    assert calls == [timed.id, healthy.id, timed.id]
    record = atlas["theorems"][timed.id]  # Catalog learning may replace a rescreened record.
    assert record["proof_retry_count"] == 2
    assert record["next_retry_at"] == 2000.0 and record["next_retry_iteration"] == 7
    assert record["status"] == "EMPIRICAL_SURVIVOR"
    assert atlas["total_refuted"] == 1 and feedback == [healthy.id]
