import networkx as nx
import pytest

from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier
from autonomous_math.sieve.model_counterexamples import (
    validate_counterexample_graph, verify_model_counterexample, verify_model_counterexample_certificate,
)


def payload(graph):
    return {"order": len(graph), "edges": [list(edge) for edge in graph.edges()]}


def bound(lhs, rel="<=", rhs=0, guard=None):
    return Conjecture.create(id="target", lhs=InvariantNode(lhs), rel=rel, rhs=ConstantNode(rhs), guard=guard)


def fitted_false_bound():
    # Exact saved checkpoint75 AST for survivor suffix 5d177a4ac7d4.
    rhs = BinaryOpNode("+", BinaryOpNode("+",
        BinaryOpNode("*", ConstantNode(11.1), InvariantNode("spectral_radius")),
        BinaryOpNode("*", ConstantNode(7.76135479486494e-06), InvariantNode("estrada_index"))),
        ConstantNode(9.833333333333334))
    return Conjecture.create(id="saved_5d177a4ac7d4", lhs=InvariantNode("size"), rel="<=", rhs=rhs)


@pytest.mark.parametrize("data", [
    None, [], {}, {"order": 1, "edges": [], "invariants": {}},
    {"order": True, "edges": []}, {"order": 1.0, "edges": []},
    {"order": -1, "edges": []}, {"order": 65, "edges": []},
    {"order": 2, "edges": [(0, 1)]}, {"order": 2, "edges": [[True, 1]]},
    {"order": 2, "edges": [[0, 1.0]]}, {"order": 2, "edges": [[0, "1"]]},
    {"order": 2, "edges": [[0, 2]]}, {"order": 2, "edges": [[0, 0]]},
    {"order": 3, "edges": [[0, 1], [1, 0]]},
    {"order": 64, "edges": [[0, 1]] * 2017},
])
def test_invalid_graphs_are_rejected_before_allocation(data, monkeypatch):
    monkeypatch.setattr(nx, "Graph", lambda: pytest.fail("invalid input allocated a graph"))
    with pytest.raises(ValueError):
        validate_counterexample_graph(data)


def test_graph_limits_empty_and_canonical_edges():
    assert len(validate_counterexample_graph({"order": 0, "edges": []})) == 0
    graph = validate_counterexample_graph({"order": 3, "edges": [[2, 0], [1, 0]]})
    assert list(graph.nodes()) == [0, 1, 2] and sorted(graph.edges()) == [(0, 1), (0, 2)]
    complete = validate_counterexample_graph(payload(nx.complete_graph(64)))
    assert len(complete) == 64 and complete.number_of_edges() == 2016


def test_actual_saved_false_survivor_has_replayable_host_certificate():
    graph = nx.disjoint_union_all([nx.path_graph(2) for _ in range(22)])
    target = fitted_false_bound()
    cert = verify_model_counterexample(payload(graph), target)
    details = cert.refutation_witness["details"]
    assert cert.graph_order == 44 and cert.graph_size == 22
    assert details["lhs_value"] == 22
    assert details["rhs_value"] == pytest.approx(20.933860299, abs=1e-7)
    assert cert.invariants == {"order": 44, "size": 22}
    serialized = cert.to_json()
    replayed = verify_model_counterexample_certificate(CounterexampleCertificate.from_json(serialized).to_dict(), target)
    assert replayed.to_json() == serialized
    assert CounterexampleCertificateVerifier.verify(replayed, target)


@pytest.mark.parametrize("target,graph,error", [
    (bound("size", ">=", 0), nx.path_graph(2), "not violated"),
    (bound("size", "<=", 0, "is_connected"), nx.empty_graph(2), "premise"),
    (bound("girth", "<=", 1), nx.path_graph(2), "nonfinite"),
    (bound("diameter", "<=", 1), nx.empty_graph(2), "nonfinite"),
    (bound("size", "<=", 0, GuardPredicate(predicate_type="comparison", invariant="girth", op=">", threshold=0)), nx.path_graph(2), "nonfinite"),
])
def test_true_inapplicable_and_nonfinite_are_not_refutations(target, graph, error):
    with pytest.raises(ValueError, match=error):
        verify_model_counterexample(payload(graph), target)


def test_undefined_expression_is_not_a_refutation():
    target = Conjecture.create(id="undefined", lhs=BinaryOpNode("/", ConstantNode(1), InvariantNode("size")), rel="<=", rhs=ConstantNode(0))
    with pytest.raises(ValueError):
        verify_model_counterexample(payload(nx.empty_graph(1)), target)


def test_host_solver_budget_covers_guard_and_expression_without_duplicate_replay(monkeypatch):
    original = GraphInvariantEvaluator.evaluate
    calls = []
    def recording(graph, invariants=None, timeout_ms=5000):
        calls.append((set(invariants), timeout_ms))
        return original(graph, invariants, timeout_ms)
    monkeypatch.setattr(GraphInvariantEvaluator, "evaluate", recording)
    target = bound("chromatic_number", guard=GuardPredicate(predicate_type="comparison", invariant="alpha", op=">=", threshold=0))
    cert = verify_model_counterexample(payload(nx.cycle_graph(5)), target)
    assert calls == [({"chromatic_number", "alpha"}, 1000)]
    assert cert.refutation_witness["details"]["lhs_value"] == 3


@pytest.mark.parametrize("error", [TimeoutError("solver timeout"), InterruptedError("cancelled")])
def test_solver_failure_and_cancellation_never_create_a_certificate(monkeypatch, error):
    def fail(*args, **kwargs):
        raise error
    monkeypatch.setattr(GraphInvariantEvaluator, "evaluate", fail)
    with pytest.raises(InterruptedError if isinstance(error, InterruptedError) else ValueError):
        verify_model_counterexample(payload(nx.path_graph(2)), bound("size"))


@pytest.mark.parametrize("invariant,graph", [
    ("chromatic_number", nx.cycle_graph(33)),
    ("independence_number", nx.cycle_graph(33)),
    ("clique_number", nx.lollipop_graph(4, 29)),
])
def test_large_nonshortcut_hard_invariants_are_unsupported(invariant, graph, monkeypatch):
    monkeypatch.setattr(GraphInvariantEvaluator, "evaluate", lambda *args, **kwargs: pytest.fail("unbounded exact solver launched"))
    with pytest.raises(ValueError, match="Unsupported bounded verification"):
        verify_model_counterexample(payload(graph), bound(invariant))


@pytest.mark.parametrize("invariant,graph,value", [
    ("chromatic_number", nx.complete_graph(64), 64),
    ("independence_number", nx.empty_graph(64), 64),
    ("independence_number", nx.disjoint_union_all([nx.cycle_graph(4) for _ in range(16)]), 32),
    ("clique_number", nx.disjoint_union_all([nx.cycle_graph(4) for _ in range(16)]), 2),
])
def test_large_exact_shortcuts_remain_supported(invariant, graph, value):
    cert = verify_model_counterexample(payload(graph), bound(invariant))
    assert cert.refutation_witness["details"]["lhs_value"] == value


@pytest.mark.parametrize("mutation", [
    lambda d: d.update(conjecture_id="different_target"),
    lambda d: d.update(verification_hash="0" * 64),
    lambda d: d["adjacency_matrix"][0].__setitem__(1, 0),
    lambda d: d["adjacency_matrix"][0].__setitem__(1, True),
    lambda d: d["edges"][0].__setitem__(0, True),
    lambda d: d["invariants"].update(size=True),
    lambda d: d["refutation_witness"]["details"].update(lhs_value=999),
])
def test_serialized_tampering_is_rejected(mutation):
    target = bound("size")
    original = verify_model_counterexample(payload(nx.path_graph(2)), target)
    # JSON round-trip ensures mutable endpoint arrays, as in a saved checkpoint.
    import json
    data = json.loads(original.to_json())
    mutation(data)
    with pytest.raises(ValueError):
        verify_model_counterexample_certificate(data, target)


def test_rehashed_fabricated_witness_is_still_rejected():
    target = bound("size")
    cert = verify_model_counterexample(payload(nx.path_graph(2)), target)
    data = cert.to_dict()
    data["refutation_witness"]["details"]["lhs_value"] = 999
    data["verification_hash"] = CounterexampleCertificate.from_dict(data).compute_hash()
    with pytest.raises(ValueError, match="differ from host"):
        verify_model_counterexample_certificate(data, target)


@pytest.mark.parametrize("witness_type", ["exhaustive_coloring", "odd_cycle", "unknown"])
def test_legacy_witness_types_are_rejected_before_witness_verification(witness_type, monkeypatch):
    target = bound("size")
    cert = verify_model_counterexample(payload(nx.path_graph(2)), target)
    data = cert.to_dict()
    data["refutation_witness"] = {"type": witness_type, "details": {"k": 2}}
    data["verification_hash"] = CounterexampleCertificate.from_dict(data).compute_hash()
    monkeypatch.setattr(CounterexampleCertificateVerifier, "verify_refutation_witness",
        lambda *args: pytest.fail("legacy witness verification must not enumerate"))
    with pytest.raises(ValueError, match="require a direct_evaluation witness"):
        verify_model_counterexample_certificate(data, target)
