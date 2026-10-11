"""Regressions for spectral fits defeated by small mixed graph structures."""

import networkx as nx
import pytest

from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.sieve.adversarial_holdouts import holdout_graphs
from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier


def _scaled(coefficient, invariant):
    return BinaryOpNode("*", ConstantNode(coefficient), InvariantNode(invariant))


def _candidate(name, lhs, relation, rhs, property_name="is_connected"):
    return Conjecture.create(
        id=name, lhs=InvariantNode(lhs), rel=relation, rhs=rhs,
        guard=GuardPredicate(property_name=property_name),
    )


MIN_DEGREE_UPPER = BinaryOpNode("-", _scaled(1.5, "spectral_radius"), _scaled(.25, "signless_laplacian_spectral_radius"))


@pytest.mark.parametrize("graph_name,candidate", [
    ("holdout_wheel_24", _candidate("false_min_degree_upper_wheel", "min_degree", "<=", MIN_DEGREE_UPPER)),
    ("holdout_star_26", _candidate("false_min_degree_upper_star", "min_degree", "<=", MIN_DEGREE_UPPER)),
    ("holdout_lollipop_8_8", _candidate("false_min_degree_lower", "min_degree", ">=",
        BinaryOpNode("-", BinaryOpNode("+", _scaled(.003316859065453037, "signless_laplacian_spectral_radius"),
                                      _scaled(.2, "spectral_radius")), ConstantNode(.04069668494127732)))),
    ("holdout_lollipop_8_8", _candidate("false_min_degree_lower_steep", "min_degree", ">=",
        BinaryOpNode("-", BinaryOpNode("+", _scaled(.020459302546206568, "signless_laplacian_spectral_radius"),
                                      _scaled(1.2, "spectral_radius")), ConstantNode(5.55)))),
    ("holdout_star_15", _candidate("false_tree_degree_lower", "min_degree", ">=",
        BinaryOpNode("-", BinaryOpNode("-", _scaled(.2, "independence_number"),
                                      _scaled(.03182341969233606, "nordhaus_gaddum_spectral_product")), ConstantNode(.25)),
        "is_tree")),
    ("holdout_clique_25", _candidate("false_signless_upper", "signless_laplacian_spectral_radius", "<=",
        BinaryOpNode("+", BinaryOpNode("+", _scaled(1.5, "spectral_spread"), _scaled(.4, "max_degree")), ConstantNode(.8)))),
    ("holdout_leaf_star_10_clique_6", _candidate("false_signless_lower", "signless_laplacian_spectral_radius", ">=",
        BinaryOpNode("+", _scaled(.25, "spectral_spread"), _scaled(.9, "max_degree")))),
    ("holdout_bridge_cliques_5_5", _candidate("false_independence_lower", "independence_number", ">=",
        BinaryOpNode("+", _scaled(.25, "complement_spectral_radius"), ConstantNode(1)))),
])
def test_audited_false_bounds_have_replayable_certificates(graph_name, candidate):
    graph = next(graph for graph in holdout_graphs() if graph.name == graph_name)
    assert candidate.applies(graph)
    holds, lhs, rhs = candidate.evaluate(graph)
    assert not holds
    certificate = CounterexampleCertificate.from_counterexample_graph(
        graph, candidate,
        witness={"type": "direct_evaluation", "details": {"lhs_value": lhs, "rhs_value": rhs}},
    )
    replayed = CounterexampleCertificate.from_json(certificate.to_json())
    restored_candidate = Conjecture.from_dict(candidate.to_dict())
    valid, errors = CounterexampleCertificateVerifier.verify_with_details(replayed, restored_candidate)
    assert valid, errors
    assert replayed.compute_hash() == certificate.verification_hash
    assert set(replayed.to_networkx().nodes()) == set(range(len(graph)))


def test_holdouts_are_deterministic_and_bounded():
    first, second = holdout_graphs(), holdout_graphs()
    signatures = lambda graphs: [(g.name, len(g), sorted(g.edges())) for g in graphs]
    assert signatures(first) == signatures(second)
    assert all(not g.is_directed() and nx.number_of_selfloops(g) == 0 for g in first)
    assert all(len(g) <= 64 and set(g.nodes()) == set(range(len(g))) for g in first)
    assert {g.name for g in first if len(g) > 32} == {"holdout_matching_22", "holdout_cycles_4_16"}
    assert len({(len(g), tuple(sorted(g.edges()))) for g in first}) == len(first)
    assert {g.name for g in first[:7]} >= {
        "holdout_bridge_cliques_5_5", "holdout_leaf_star_10_clique_6",
        "holdout_clique_25", "holdout_star_26",
    }
    assert any(not nx.is_connected(g) for g in first)
    # Callers may annotate or mutate a returned graph without changing future
    # holdout runs or a concurrent caller's suite.
    first[0].clear()
    assert len(holdout_graphs()[0]) == 10


@pytest.mark.parametrize("name,order,edges,independence", [
    ("holdout_matching_22", 44, 22, 22),
    ("holdout_cycles_4_16", 64, 64, 32),
])
def test_large_disconnected_witnesses_use_exact_shortcuts(name, order, edges, independence):
    from autonomous_math.core.invariants import GraphInvariantEvaluator
    graph = next(graph for graph in holdout_graphs() if graph.name == name)
    assert len(graph) == order and graph.number_of_edges() == edges
    assert GraphInvariantEvaluator.evaluate(graph, ["chromatic_number", "clique_number", "independence_number"]) == {
        "chromatic_number": 2, "clique_number": 2, "independence_number": independence,
    }


@pytest.mark.parametrize("lhs,relation,rhs", [
    ("max_degree", "<=", "size"),
    ("min_degree", "<=", "max_degree"),
    ("signless_laplacian_spectral_radius", ">=", "max_degree"),
])
def test_basic_true_bounds_survive_mixed_holdouts(lhs, relation, rhs):
    candidate = Conjecture.create(id=f"true_{lhs}_{rhs}", lhs=InvariantNode(lhs), rel=relation, rhs=InvariantNode(rhs))
    assert all(candidate.evaluate(graph)[0] for graph in holdout_graphs())
