"""Code claims must survive the same host-verified graph witness protocol."""

import json

import networkx as nx
import pytest

from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.sieve.model_counterexamples import (
    verify_model_counterexample, verify_model_counterexample_certificate,
)


def payload(graph):
    return {"order": len(graph), "edges": [list(e) for e in graph.edges()]}


def target(identifier, left, relation, right, guard=None):
    return Conjecture.create(id=identifier, lhs=InvariantNode(left), rel=relation,
                             rhs=right, guard=guard)


def test_zero_code_sentinel_refutes_unguarded_distance_le_length():
    # A(K2) is invertible over F2. There is no nonzero word, so d=n+1=3.
    conjecture = target("distance_length", "parity_code_distance", "<=", InvariantNode("order"))
    cert = verify_model_counterexample(payload(nx.path_graph(2)), conjecture)
    details = cert.refutation_witness["details"]
    assert details["lhs_value"] == 3 and details["rhs_value"] == 2
    replay = verify_model_counterexample_certificate(json.loads(cert.to_json()), conjecture)
    assert replay.to_json() == cert.to_json()


def test_nonzero_code_guard_excludes_the_zero_code_control():
    guard = GuardPredicate(predicate_type="comparison", invariant="parity_code_dimension",
                           op=">=", threshold=1)
    conjecture = target("nonzero_distance_length", "parity_code_distance", "<=",
                        InvariantNode("order"), guard)
    with pytest.raises(ValueError, match="premise"):
        verify_model_counterexample(payload(nx.path_graph(2)), conjecture)


def test_a_real_nonzero_code_refutes_claimed_distance():
    # Opposite vertices of C4 have identical columns; their sum is a weight2 word.
    conjecture = target("false_distance", "parity_code_distance", ">=", ConstantNode(3))
    cert = verify_model_counterexample(payload(nx.cycle_graph(4)), conjecture)
    assert cert.refutation_witness["details"]["lhs_value"] == 2
    verify_model_counterexample_certificate(json.loads(cert.to_json()), conjecture)


def test_expansion_certificate_is_a_lower_bound_not_an_exact_distance():
    # K5 is a repetition code with d=5, but its smallest stopping set has size3.
    conjecture = target("false_expansion_equality", "parity_code_distance", "<=",
                        BinaryOpNode("+", InvariantNode("unique_neighbor_radius"), ConstantNode(1)))
    cert = verify_model_counterexample(payload(nx.complete_graph(5)), conjecture)
    assert cert.refutation_witness["details"]["lhs_value"] == 5
    assert cert.refutation_witness["details"]["rhs_value"] == 3


def test_expansion_distance_bridge_cannot_be_refuted_by_same_graph():
    conjecture = target("expansion_distance", "unique_neighbor_radius", "<",
                        InvariantNode("parity_code_distance"))
    with pytest.raises(ValueError, match="not violated"):
        verify_model_counterexample(payload(nx.complete_graph(5)), conjecture)


def test_large_code_witness_remains_unsupported_not_false():
    conjecture = target("large_code", "parity_code_distance", "<=", ConstantNode(0))
    with pytest.raises(ValueError, match="16"):
        verify_model_counterexample(payload(nx.cycle_graph(17)), conjecture)


def test_counterexample_dimension_guard_is_recomputed():
    guard = GuardPredicate(predicate_type="comparison", invariant="parity_code_dimension",
                           op=">=", threshold=2)
    conjecture = target("dimension_guard", "parity_code_distance", "<=", ConstantNode(0), guard)
    with pytest.raises(ValueError, match="premise"):
        verify_model_counterexample(payload(nx.cycle_graph(5)), conjecture)
