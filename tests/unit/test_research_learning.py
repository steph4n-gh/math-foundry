"""Controls for challenger migration and dependency-bound negative proof caching."""
import copy
import time
from types import SimpleNamespace

import networkx as nx
import pytest
import run_research as runner
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math.sieve.certificates import CounterexampleCertificate, SieveResult


def candidate():
    return Conjecture.create(id="cache_target", lhs=InvariantNode("order"), rel=">=", rhs=ConstantNode(0))


@pytest.fixture
def fake_search(monkeypatch):
    class Search:
        calls = 0
        key = "initial-context"
        exit_code = 1
        def __init__(self, **kwargs):
            self.toolchain = SimpleNamespace(ensure_workspace_built=lambda: True)
        def is_available(self):
            return True
        def search_key(self, candidate):
            return type(self).key
        def prove_conjecture(self, candidate, **kwargs):
            type(self).calls += 1
            return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=1,
                diagnostics=[{"exit_code": type(self).exit_code}])
    class Database:
        _cached_gi = []
        _cached_matrix = {}
        def sieve_conjecture(self, c):
            return SieveResult(status="SURVIVED", conjecture=c, tested_instances_count=1, checked_instances_count=1)
    monkeypatch.setattr(runner, "LeanProofSearch", Search)
    monkeypatch.setattr(runner, "InstanceDatabase", Database)
    monkeypatch.setattr(runner, "independent_holdout", lambda c, check: SieveResult(
        status="SURVIVED", conjecture=c, tested_instances_count=1, checked_instances_count=1))
    return Search


def batch(atlas, tmp_path):
    runner._evaluate_batch([candidate()], atlas, tmp_path, 1, runner.GracefulDaemonInterrupt(),
                           time.monotonic()+30, {})


def test_identical_failure_skips_until_search_context_changes(fake_search, tmp_path):
    atlas = runner.load_snapshot(tmp_path)
    batch(atlas, tmp_path)
    atlas["total_iterations"] = 2
    batch(atlas, tmp_path)
    assert fake_search.calls == 1
    record = atlas["theorems"]["cache_target"]
    assert record["proof_search_skipped"]
    assert record["discovered_iteration"] == 1
    assert record["last_evaluated_iteration"] == 3
    fake_search.key = "new-certified-lemma"
    batch(atlas, tmp_path)
    assert fake_search.calls == 2
    assert not atlas["theorems"]["cache_target"].get("proof_search_skipped", False)


def test_timeout_is_retried_after_backoff(fake_search, monkeypatch, tmp_path):
    fake_search.exit_code = 124
    clock = [time.time()]
    monkeypatch.setattr(runner.time, "time", lambda: clock[0])
    atlas = runner.load_snapshot(tmp_path)
    batch(atlas, tmp_path)
    batch(atlas, tmp_path)
    assert fake_search.calls == 1
    assert atlas["theorems"]["cache_target"]["proof_search_skipped"]
    clock[0] += 301
    atlas["total_iterations"] = 2
    batch(atlas, tmp_path)
    assert fake_search.calls == 2


def test_old_survivor_is_refuted_once_before_learning(monkeypatch):
    c = Conjecture.create(id="old_false_survivor", lhs=InvariantNode("order"), rel="<=", rhs=ConstantNode(1))
    cert = CounterexampleCertificate.from_counterexample_graph(nx.path_graph(2), c)
    monkeypatch.setattr(runner, "independent_holdout", lambda obj, check: SieveResult(
        status="REFUTED", conjecture=obj, tested_instances_count=1, checked_instances_count=1,
        counterexample_certificate=cert))
    atlas = {"theorems": {c.id: {"id": c.id, "status": "EMPIRICAL_SURVIVOR", "conjecture": c.to_dict()}}, "total_refuted": 4}
    assert runner.reassess_survivors(atlas) == 1
    assert atlas["theorems"][c.id]["status"] == "REFUTED"
    assert atlas["total_refuted"] == 5
    assert runner.reassess_survivors(atlas) == 0
    assert atlas["total_refuted"] == 5
    contradicted = copy.deepcopy(atlas)
    contradicted.pop("holdout_revision")
    contradicted["theorems"][c.id]["status"] = "LEAN_CERTIFIED"
    with pytest.raises(ValueError, match="contradicts a checked theorem"):
        runner.reassess_survivors(contradicted)


def test_evaluation_training_statements_are_held_out():
    from evaluate_self_improvement import heldout_targets, statement_key, counterexample_targets
    from autonomous_math.prover.trusted_lean import bootstrap_candidates
    assert not {statement_key(c) for c in bootstrap_candidates()} & {statement_key(c) for c in heldout_targets()}
    train, test = counterexample_targets()
    assert not {statement_key(c) for c in train} & {statement_key(c) for c in test}
