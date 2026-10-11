"""Independent small parity/subset oracles and real nonzero-word peeling."""

import itertools

import networkx as nx
import pytest

from autonomous_math.core.ast import Conjecture, INTEGER_VALUED_INVARIANTS, InvariantNode
from autonomous_math.core.expander_codes import (
    MAX_EXACT_CODE_ORDER, compute_parity_code_dimension, compute_parity_code_distance,
    compute_unique_neighbor_radius, peel_erasures,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import GraphInvariantEvaluator, STANDARD_SCALAR_INVARIANTS


def brute_codewords(graph):
    return [word for word in itertools.product((0, 1), repeat=len(graph))
            if all(sum(word[v] for v in graph.neighbors(check)) % 2 == 0 for check in graph)]


def brute_parameters(graph):
    words = brute_codewords(graph)
    distance = min((sum(word) for word in words if any(word)), default=len(graph) + 1)
    stopping_sizes = [sum(word) for word in itertools.product((0, 1), repeat=len(graph)) if any(word)
                      and all(sum(word[v] for v in graph.neighbors(check)) != 1 for check in graph)]
    radius = min(stopping_sizes, default=len(graph) + 1) - 1
    return distance, len(words).bit_length() - 1, radius


def actual_parameters(graph):
    return (compute_parity_code_distance(graph), compute_parity_code_dimension(graph),
            compute_unique_neighbor_radius(graph))


def test_all_graphs_through_four_vertices_match_independent_brute_oracle():
    for order in range(5):
        edges = list(itertools.combinations(range(order), 2))
        for mask in range(1 << len(edges)):
            graph = nx.empty_graph(order)
            graph.add_edges_from(edge for i, edge in enumerate(edges) if mask & (1 << i))
            assert actual_parameters(graph) == brute_parameters(graph)
            distance, dimension, radius = actual_parameters(graph)
            assert 0 <= radius <= order and radius < distance <= order + 1
            assert 0 <= dimension <= order
            assert dimension == 0 or distance <= order


@pytest.mark.parametrize("graph,expected", [
    (nx.empty_graph(0), (1, 0, 0)),
    (nx.empty_graph(3), (1, 3, 0)),
    (nx.path_graph(2), (3, 0, 2)),
    (nx.disjoint_union(nx.path_graph(2), nx.empty_graph(1)), (1, 1, 0)),
    (nx.complete_graph(3), (3, 1, 2)),
    (nx.cycle_graph(4), (2, 2, 1)),
    (nx.cycle_graph(5), (5, 1, 4)),
    (nx.cycle_graph(6), (3, 2, 2)),
    (nx.complete_graph(4), (5, 0, 2)),
    (nx.complete_graph(5), (5, 1, 2)),
])
def test_empty_isolated_zero_and_regular_controls(graph, expected):
    assert actual_parameters(graph) == expected == brute_parameters(graph)


def test_boundary_size_and_cache_reuse_are_exact():
    graph = nx.disjoint_union_all([nx.path_graph(2) for _ in range(8)])
    assert len(graph) == MAX_EXACT_CODE_ORDER
    assert actual_parameters(graph) == (17, 0, 16)
    # Metadata, edge insertion order and relabeling do not change the code.
    changed = nx.relabel_nodes(graph, {v: 100 - v for v in graph})
    changed.name = "different metadata"
    assert actual_parameters(changed) == actual_parameters(graph)
    assert actual_parameters(nx.empty_graph(16)) == (1, 16, 0)


@pytest.mark.parametrize("name", ["parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"])
def test_cap_is_explicit_and_no_unsupported_value_is_cached(name):
    graph = GraphInstance.from_networkx(nx.empty_graph(17))
    with pytest.raises(ValueError, match="at most 16"):
        GraphInvariantEvaluator.evaluate_single(graph, name)
    assert not graph.has_invariant(name)
    assert name not in STANDARD_SCALAR_INVARIANTS
    assert GraphInvariantEvaluator.evaluate(graph, ["order", "size"]) == {"order": 17, "size": 0}


def test_ast_and_explicit_evaluator_use_real_code_parameters():
    graph = nx.cycle_graph(5)
    values = GraphInvariantEvaluator.evaluate(graph, ["parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"])
    assert values == {"parity_code_distance": 5, "parity_code_dimension": 1, "unique_neighbor_radius": 4}
    assert set(values) <= INTEGER_VALUED_INVARIANTS
    target = Conjecture.create(id="real_code", lhs=InvariantNode("unique_neighbor_radius"), rel="<", rhs=InvariantNode("parity_code_distance"))
    assert target.evaluate(graph) == (True, 4, 5)


@pytest.mark.parametrize("graph", [nx.cycle_graph(5), nx.cycle_graph(6), nx.complete_graph(5)])
def test_peeling_recovers_nonzero_words_for_every_guaranteed_erasure_set(graph):
    radius = compute_unique_neighbor_radius(graph)
    words = brute_codewords(graph)
    assert any(any(word) for word in words)
    for word in words:
        for size in range(radius + 1):
            for erased in itertools.combinations(range(len(graph)), size):
                received = [None if i in erased else bit for i, bit in enumerate(word)]
                snapshot = list(received)
                result = peel_erasures(graph, received)
                assert result.status == "DECODED" and result.word == word
                assert not result.unresolved_positions and not result.violated_checks
                assert len(result.steps) == size
                assert received == snapshot
                assert len({variable for _, variable, _ in result.steps}) == size


def test_peeling_stopping_set_retains_blocked_partial_word():
    graph = nx.cycle_graph(4)
    result = peel_erasures(graph, [None, 0, None, 0])
    assert result.status == "BLOCKED"
    assert result.word == (None, 0, None, 0)
    assert result.unresolved_positions == (0, 2) and not result.steps
    assert not result.violated_checks


def test_inconsistent_known_bits_are_not_reported_as_corrected():
    result = peel_erasures(nx.cycle_graph(5), [1, 0, 0, 0, 0])
    assert result.status == "INCONSISTENT" and result.violated_checks == (1, 4)
    assert result.word == (1, 0, 0, 0, 0) and not result.steps
    # A corrupted sole known bit can select a different valid codeword: this is
    # erasure peeling, with no arbitrary-error correction guarantee.
    result = peel_erasures(nx.cycle_graph(5), [0, None, None, None, None])
    assert result.status == "DECODED" and result.word == (0, 0, 0, 0, 0)


@pytest.mark.parametrize("received", [[], [0], [0, 2], [True, None], ["0", None]])
def test_invalid_decoder_input_is_rejected(received):
    with pytest.raises(ValueError):
        peel_erasures(nx.path_graph(2), received)


def test_empty_decoder_and_unconstrained_erasures():
    assert peel_erasures(nx.empty_graph(0), []).status == "DECODED"
    assert peel_erasures(nx.empty_graph(2), [None, 1]).status == "BLOCKED"
    with pytest.raises(ValueError, match="at most 16"):
        peel_erasures(nx.empty_graph(17), [None] * 17)


@pytest.mark.parametrize("graph", [nx.DiGraph([(0, 1)]), nx.MultiGraph([(0, 1)]), nx.Graph([(0, 0)])])
def test_nonsimple_graphs_are_rejected(graph):
    with pytest.raises(ValueError, match="simple undirected"):
        compute_parity_code_distance(graph)
