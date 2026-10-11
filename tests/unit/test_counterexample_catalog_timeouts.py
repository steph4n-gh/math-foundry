"""An exhausted local invariant search must preserve the checked refutation."""
import copy
import hashlib
import json
import time

import networkx as nx
import pytest

import run_research as runner
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.sieve.certificates import CounterexampleCertificate
from autonomous_math.sieve import model_counterexamples


def boundary(identifier, order):
    candidate = Conjecture.create(id=identifier, lhs=InvariantNode("order"),
                                  rel="<=", rhs=ConstantNode(13))
    certificate = CounterexampleCertificate.from_counterexample_graph(
        nx.complete_graph(order), candidate)
    return {"id": identifier, "status": "REFUTED", "conjecture": candidate.to_dict(),
            "counterexample": certificate.to_dict()}


def test_invariant_timeout_defers_graph_and_preserves_refutation(monkeypatch):
    class Database:
        _cached_gi = []
        calls = []

        def add_instance(self, graph):
            self.calls.append(graph.order)
            if graph.order == 24:
                raise TimeoutError("exact coloring deadline exhausted")
            self._cached_gi.append(graph)

    monkeypatch.setattr(runner, "InstanceDatabase", Database)
    atlas = {"theorems": {name: boundary(name, order)
                          for name, order in [("hard", 24), ("alias", 24), ("easy", 25)]}}
    before = copy.deepcopy(atlas)
    deferred = []
    assert runner.replay_counterexamples(atlas, deferred=deferred) == 1
    assert Database.calls == [24, 25]
    assert [graph.order for graph in Database._cached_gi] == [25]
    assert atlas == before
    assert len(deferred) == 1
    assert deferred[0]["id"] == "hard"
    assert deferred[0]["certificate_sha256"] == hashlib.sha256(
        json.dumps(atlas["theorems"]["hard"]["counterexample"], sort_keys=True).encode()).hexdigest()


def test_boundary_replay_honors_cancellation_before_admission(monkeypatch):
    class Database:
        _cached_gi = []

        def add_instance(self, graph):
            pytest.fail("cancelled replay must not add a graph")

    monkeypatch.setattr(runner, "InstanceDatabase", Database)
    atlas = {"theorems": {"boundary": boundary("boundary", 24)}}

    def stop():
        raise InterruptedError("cancelled")

    with pytest.raises(InterruptedError, match="cancelled"):
        runner.replay_counterexamples(atlas, check=stop)


@pytest.fixture
def model_boundaries():
    records = {}
    for identifier, order in [("hard", 4), ("easy", 5)]:
        candidate = Conjecture.create(id=identifier, lhs=InvariantNode("order"),
                                      rel="<=", rhs=ConstantNode(1))
        graph = nx.complete_graph(order)
        certificate = model_counterexamples.verify_model_counterexample(
            {"order": order, "edges": [list(edge) for edge in graph.edges()]}, candidate)
        data = json.loads(certificate.to_json())
        records[identifier] = {
            "id": identifier, "status": "REFUTED", "conjecture": candidate.to_dict(),
            "counterexample": data,
            "proof_attempt": {"status": "REFUTED", "is_machine_checked": False,
                              "conjecture_id": identifier,
                              "counterexample_certificate": copy.deepcopy(data)},
        }
    return records


@pytest.fixture
def recording_database(monkeypatch):
    class Database:
        _cached_gi = []
        calls = []

        def add_instance(self, graph):
            self.calls.append(graph.order)
            self._cached_gi.append(graph)

    monkeypatch.setattr(runner, "InstanceDatabase", Database)
    return Database


def test_serialized_model_certificate_preserves_bounded_timeout(monkeypatch, model_boundaries):
    record = model_boundaries["hard"]

    def timeout(*args):
        raise TimeoutError("Z3 timed out solving chromatic number for k=7")

    monkeypatch.setattr(model_counterexamples, "_refutation_values", timeout)
    with pytest.raises(TimeoutError, match="k=7"):
        model_counterexamples.verify_model_counterexample_certificate(
            record["counterexample"], Conjecture.from_dict(record["conjecture"]))


def test_certificate_timeout_preserves_refutation_and_continues_easy_graph(
        monkeypatch, model_boundaries, recording_database):
    original = model_counterexamples._refutation_values

    def evaluate(graph, candidate):
        if candidate.id == "hard":
            raise TimeoutError("Z3 timed out solving chromatic number for k=7")
        return original(graph, candidate)

    monkeypatch.setattr(model_counterexamples, "_refutation_values", evaluate)
    atlas = {"theorems": model_boundaries}
    before = copy.deepcopy(atlas)
    deferred = []
    assert runner.replay_counterexamples(atlas, deferred=deferred) == 1
    assert atlas == before
    assert recording_database.calls == [5]
    assert [graph.order for graph in recording_database._cached_gi] == [5]
    assert len(deferred) == 1
    item = deferred[0]
    assert item["id"] == "hard"
    assert item["order"] == 4 and item["size"] == 6
    assert item["reason"] == "Z3 timed out solving chromatic number for k=7"
    assert item["stage"] == "certificate_revalidation"
    assert item["graph_hash"] == GraphInstance.from_networkx(nx.complete_graph(4)).canonical_hash
    assert item["certificate_sha256"] == hashlib.sha256(
        json.dumps(before["theorems"]["hard"]["counterexample"],
                   sort_keys=True).encode()).hexdigest()
    assert item["conjecture_sha256"] == hashlib.sha256(
        json.dumps(before["theorems"]["hard"]["conjecture"],
                   sort_keys=True).encode()).hexdigest()


@pytest.mark.parametrize("malformation", ["matrix", "hash"])
def test_malformed_saved_model_certificate_is_not_deferred(
        model_boundaries, recording_database, malformation):
    record = model_boundaries["hard"]
    if malformation == "matrix":
        record["counterexample"]["adjacency_matrix"][0][1] = True
    else:
        record["counterexample"]["verification_hash"] = "0" * 64
    record["proof_attempt"]["counterexample_certificate"] = copy.deepcopy(record["counterexample"])
    atlas = {"theorems": {"hard": record}}
    before = copy.deepcopy(atlas)
    deferred = []
    with pytest.raises(ValueError):
        runner.replay_counterexamples(atlas, deferred=deferred)
    assert deferred == [] and recording_database.calls == []
    assert atlas == before


def test_contradictory_saved_refutation_still_fails_closed(
        monkeypatch, model_boundaries, recording_database):
    record = model_boundaries["hard"]
    record["proof_attempt"]["counterexample_certificate"]["verification_hash"] = "0" * 64
    monkeypatch.setattr(runner, "_verified_prover_refutation",
                        lambda *args: pytest.fail("contradiction must fail before replay"))
    deferred = []
    with pytest.raises(ValueError, match="Contradictory saved prover refutation"):
        runner.replay_counterexamples({"theorems": {"hard": record}}, deferred=deferred)
    assert deferred == [] and recording_database.calls == []


def test_certificate_replay_cancellation_is_not_deferred(
        monkeypatch, model_boundaries, recording_database):
    def cancelled(*args):
        raise InterruptedError("cancelled during exact verification")

    monkeypatch.setattr(model_counterexamples, "_refutation_values", cancelled)
    deferred = []
    with pytest.raises(InterruptedError, match="cancelled during exact verification"):
        runner.replay_counterexamples({"theorems": model_boundaries}, deferred=deferred)
    assert deferred == [] and recording_database.calls == []


def test_cancellation_after_verifier_timeout_precedes_deferral(
        monkeypatch, model_boundaries, recording_database):
    def timeout(*args):
        raise TimeoutError("solver timeout")

    monkeypatch.setattr(model_counterexamples, "_refutation_values", timeout)
    checks = []

    def stop_after_timeout():
        checks.append(True)
        if len(checks) == 2:
            raise InterruptedError("cancelled after exact verifier timeout")

    deferred = []
    with pytest.raises(InterruptedError, match="cancelled after exact verifier timeout"):
        runner.replay_counterexamples({"theorems": model_boundaries},
                                      deferred=deferred, check=stop_after_timeout)
    assert len(checks) == 2
    assert deferred == [] and recording_database.calls == []


def test_sieve_job_persists_deferral_and_reports_only_admitted_catalog(
        monkeypatch, model_boundaries, recording_database, tmp_path):
    original = model_counterexamples._refutation_values

    def evaluate(graph, candidate):
        if candidate.id == "hard":
            raise TimeoutError("bounded verifier exhausted")
        return original(graph, candidate)

    monkeypatch.setattr(model_counterexamples, "_refutation_values", evaluate)
    candidate = Conjecture.create(id="probe", lhs=InvariantNode("order"),
                                  rel=">=", rhs=ConstantNode(0))
    expected_records = [{"id": candidate.id, "status": "EMPIRICAL_SURVIVOR"}]
    monkeypatch.setattr(runner, "_sieve_delta", lambda candidates, check: expected_records)
    snapshot = {"boundaries": list(model_boundaries.values())}
    before = copy.deepcopy(snapshot)
    job = {"job_id": "sieve-00", "kind": "sieve", "directory": str(tmp_path),
           "candidates": [candidate.to_dict()]}
    delta = runner._run_job(job, snapshot, {"replay_boundary": True},
                            time.monotonic()+10, [], lambda: None)
    persisted = json.loads((tmp_path / "boundary_replay.json").read_text())
    assert persisted["deferred_counterexample_graphs"] == delta["deferred_counterexample_graphs"]
    assert len(persisted["deferred_counterexample_graphs"]) == 1
    deferred = persisted["deferred_counterexample_graphs"][0]
    assert deferred["id"] == "hard" and deferred["stage"] == "certificate_revalidation"
    hard_hash = GraphInstance.from_networkx(nx.complete_graph(4)).canonical_hash
    easy_hash = GraphInstance.from_networkx(nx.complete_graph(5)).canonical_hash
    assert deferred["graph_hash"] == hard_hash
    assert delta["catalog_graph_hashes"] == [easy_hash]
    assert hard_hash not in delta["catalog_graph_hashes"]
    assert delta["records"] == expected_records
    assert recording_database.calls == [5]
    assert snapshot == before
