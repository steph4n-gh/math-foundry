"""Adversarial regression checks for the optional exact clique ceilings."""
import networkx as nx
import pytest

from spectral_pruning.bitset_solvers import (
    BitsetBaselineSolver, BitsetSpectralSolver, edge_count_clique_bound,
)
from spectral_pruning.certified_bounds_benchmark import exhaustive_clique_masks, validate_witness


@pytest.mark.parametrize('solver_type', [BitsetBaselineSolver, BitsetSpectralSolver])
def test_exhaustive_small_graph_optima_with_and_without_bounds(solver_type):
    for graph in nx.graph_atlas_g():
        optimum = max(mask.bit_count() for mask in exhaustive_clique_masks(graph))
        for enabled in (False, True):
            size, witness, metrics = solver_type(enable_clique_bounds=enabled).solve(graph)
            validate_witness(graph, size, witness)
            assert metrics.completed and not metrics.timed_out
            assert size == optimum


def test_induced_candidate_bounds_use_induced_degrees_and_edges():
    graph = nx.star_graph(8)
    solver = BitsetBaselineSolver(enable_clique_bounds=True)
    solver.solve(graph)
    leaves = sum(1 << vertex for vertex in range(1, 9))
    assert solver._degree_edge_bounds(leaves) == (1, 1)
    assert solver._degree_edge_bounds(0) == (0, 0)
    assert solver._clique_bound_prunes(leaves, 1)
    assert solver.metrics.degree_prunes > 0


def test_edge_prune_can_apply_when_degree_bound_cannot():
    graph = nx.disjoint_union(nx.star_graph(5), nx.complete_graph(3))
    solver = BitsetBaselineSolver(enable_clique_bounds=True)
    solver.solve(graph)
    candidates = (1 << len(graph)) - 1
    degree, edges = solver._degree_edge_bounds(candidates)
    assert degree > 4 and edges <= 4
    before = solver.metrics.edge_prunes
    assert solver._clique_bound_prunes(candidates, 4)
    assert solver.metrics.edge_prunes == before + 1


def test_integer_quadratic_bound_is_tight_at_large_triangular_counts():
    for clique_size in (1, 2, 3, 10, 10**9, 10**30):
        edges = clique_size * (clique_size - 1) // 2
        assert edge_count_clique_bound(edges) == clique_size
        assert clique_size * (clique_size - 1) <= 2 * edges
        assert (clique_size + 1) * clique_size > 2 * edges
        if clique_size > 1:
            assert edge_count_clique_bound(edges - 1) == clique_size - 1


@pytest.mark.parametrize('solver_type', [BitsetBaselineSolver, BitsetSpectralSolver])
def test_edgeless_global_bound_stops_search_without_changing_witness(solver_type):
    graph = nx.empty_graph(30)
    base, base_witness, base_metrics = solver_type().solve(graph)
    size, witness, metrics = solver_type(enable_clique_bounds=True).solve(graph)
    validate_witness(graph, size, witness)
    assert base == size == 1
    assert metrics.completed
    assert metrics.global_bound_stops == 1
    assert metrics.nodes_visited < base_metrics.nodes_visited


@pytest.mark.parametrize('solver_type', [BitsetBaselineSolver, BitsetSpectralSolver])
@pytest.mark.parametrize('enabled', [False, True])
def test_timeout_reports_only_an_incumbent(solver_type, enabled):
    size, witness, metrics = solver_type(enabled).solve(nx.complete_graph(30), timeout_sec=0)
    validate_witness(nx.complete_graph(30), size, witness)
    assert metrics.timed_out and not metrics.completed


@pytest.mark.parametrize('graph', [nx.DiGraph([(0, 1)]), nx.MultiGraph([(0, 1)]), nx.Graph([(0, 0)])])
def test_graph_scope_matches_finite_simple_undirected_proofs(graph):
    with pytest.raises(ValueError, match='finite simple undirected'):
        BitsetBaselineSolver(True).solve(graph)


def test_labels_and_solver_reuse_preserve_actual_vertices():
    solver = BitsetSpectralSolver(True)
    for graph in [nx.relabel_nodes(nx.complete_graph(4), {i: f'vertex-{i}' for i in range(4)}), nx.Graph(), nx.path_graph(7)]:
        size, witness, metrics = solver.solve(graph)
        validate_witness(graph, size, witness)
        assert metrics.completed
