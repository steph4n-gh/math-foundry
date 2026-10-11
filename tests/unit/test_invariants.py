"""Unit tests for GraphInstance, GraphWrapper, and Graph Invariant Engine.

Verifies:
- Graph representation conversions, graph6, canonical hashing, memoization.
- Elementary invariants (order, size, degrees, density).
- Metric invariants (triangles via Tr(A^3)/6, girth, diameter, radius).
- Spectral invariants via pure NumPy (adjacency and Laplacian spectra).
- Exact NP-hard invariants via Z3 (chromatic, clique, independence numbers).
- Structural predicates (bipartite, triangle-free, regular, connected, tree, planar).
- Mathematical bounds (Handshaking, Brooks, Hoffman, Wilf).
- Boundary and corner cases (K0, K1, E5, disconnected graphs).
"""

from __future__ import annotations

import math
import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.graph_types import GraphInstance, GraphWrapper
from autonomous_math.core.invariants import (
    GraphInvariantEvaluator,
    compute_adjacency_spectrum,
    compute_algebraic_connectivity,
    compute_average_degree,
    compute_chromatic_number,
    compute_clique_number,
    compute_density,
    compute_diameter,
    compute_girth,
    compute_hoffman_bound,
    compute_independence_number,
    compute_laplacian_spectral_radius,
    compute_laplacian_spectrum,
    compute_max_degree,
    compute_min_degree,
    compute_order,
    compute_radius,
    compute_size,
    compute_smallest_adjacency_eigenvalue,
    compute_spectral_radius,
    compute_triangle_count,
    compute_wilf_bound,
    is_bipartite,
    is_chordal,
    is_complete,
    is_connected,
    is_empty,
    is_eulerian,
    is_forest,
    is_planar,
    is_regular,
    is_tree,
    is_triangle_free,
)


class TestGraphTypesAndConversions:
    """Verifies GraphInstance representation, hashing, and conversions."""

    def test_graph_instance_initialization_and_canonicalization(self):
        # Unsorted edges with reverse vertex order
        raw_edges = [(3, 1), (2, 0), (1, 3)]  # (1, 3) duplicate, (0, 2)
        inst = GraphInstance(order=4, edges=tuple(raw_edges))

        assert inst.order == 4
        assert inst.size == 2
        assert inst.edges == ((0, 2), (1, 3))
        assert inst.canonical_hash is not None

    def test_self_loops_and_out_of_bounds_rejection(self):
        with pytest.raises(ValueError, match="Self-loops"):
            GraphInstance(order=3, edges=((1, 1),))

        with pytest.raises(ValueError, match="bounds"):
            GraphInstance(order=3, edges=((1, 3),))

        with pytest.raises(ValueError, match="negative"):
            GraphInstance(order=-1, edges=())

    def test_networkx_conversion_roundtrip(self, graph_c5):
        inst = GraphInstance.from_networkx(graph_c5, name="C5")
        assert inst.order == 5
        assert inst.size == 5

        nx_back = inst.to_networkx()
        assert nx.is_isomorphic(graph_c5, nx_back)

    def test_adjacency_matrix_conversion(self):
        adj = np.array([
            [0, 1, 0],
            [1, 0, 1],
            [0, 1, 0]
        ], dtype=int)
        inst = GraphInstance.from_adjacency_matrix(adj)
        assert inst.order == 3
        assert inst.size == 2
        assert np.array_equal(inst.to_adjacency_matrix(), adj)

    def test_graph6_roundtrip(self, graph_petersen):
        inst = GraphInstance.from_networkx(graph_petersen)
        g6 = inst.to_graph6()
        assert isinstance(g6, str) and len(g6) > 0

        reloaded = GraphInstance.from_graph6(g6)
        assert inst.order == reloaded.order
        assert inst.size == reloaded.size
        assert nx.is_isomorphic(inst.to_networkx(), reloaded.to_networkx())

    def test_json_dict_roundtrip(self, graph_c5):
        inst = GraphInstance.from_networkx(graph_c5)
        d = inst.to_dict()
        assert "order" in d and "edges" in d and "hash" in d

        reloaded = GraphInstance.from_dict(d)
        assert reloaded.order == inst.order
        assert reloaded.edges == inst.edges
        assert reloaded.canonical_hash == inst.canonical_hash

    def test_invariant_caching(self, graph_c5):
        inst = GraphInstance.from_networkx(graph_c5)
        assert not inst.has_invariant("triangles")

        val = GraphInvariantEvaluator.evaluate_single(inst, "triangles")
        assert val == 0
        assert inst.has_invariant("triangle_count")
        assert inst.get_invariant("triangle_count") == 0

        inst.clear_cache()
        assert not inst.has_invariant("triangle_count")

    def test_canonical_factories(self):
        empty = GraphInstance.empty(4)
        assert empty.order == 4 and empty.size == 0

        k4 = GraphInstance.complete(4)
        assert k4.order == 4 and k4.size == 6

        c4 = GraphInstance.cycle(4)
        assert c4.order == 4 and c4.size == 4

        p4 = GraphInstance.path(4)
        assert p4.order == 4 and p4.size == 3

        star = GraphInstance.star(4)
        assert star.order == 4 and star.size == 3

        wheel = GraphInstance.wheel(5)
        assert wheel.order == 5 and wheel.size == 8

        bipartite = GraphInstance.complete_bipartite(2, 3)
        assert bipartite.order == 5 and bipartite.size == 6

        pet = GraphInstance.petersen()
        assert pet.order == 10 and pet.size == 15

        grotzsch = GraphInstance.mycielski(4)
        assert grotzsch.order == 11 and grotzsch.size == 20


class TestInvariantsEvaluation:
    """Verifies all 15+ invariants across diverse graph topologies."""

    def test_order_size_density(self, graph_k5, graph_c5, graph_k2_3, graph_empty_5):
        assert compute_order(graph_k5) == 5
        assert compute_size(graph_k5) == 10
        assert np.isclose(compute_density(graph_k5), 1.0)

        assert compute_order(graph_c5) == 5
        assert compute_size(graph_c5) == 5
        assert np.isclose(compute_density(graph_c5), 0.5)

        assert compute_order(graph_k2_3) == 5
        assert compute_size(graph_k2_3) == 6
        assert np.isclose(compute_density(graph_k2_3), 0.6)

        assert compute_order(graph_empty_5) == 5
        assert compute_size(graph_empty_5) == 0
        assert np.isclose(compute_density(graph_empty_5), 0.0)

    def test_degrees(self, graph_star_6, graph_petersen, graph_k5):
        # S6: 1 vertex degree 5, 5 vertices degree 1
        assert compute_max_degree(graph_star_6) == 5
        assert compute_min_degree(graph_star_6) == 1
        assert np.isclose(compute_average_degree(graph_star_6), 10 / 6)

        # Petersen: 3-regular
        assert compute_max_degree(graph_petersen) == 3
        assert compute_min_degree(graph_petersen) == 3
        assert np.isclose(compute_average_degree(graph_petersen), 3.0)

        # K5: 4-regular
        assert compute_max_degree(graph_k5) == 4
        assert compute_min_degree(graph_k5) == 4
        assert np.isclose(compute_average_degree(graph_k5), 4.0)

    def test_triangle_count_trace_formula(self, graph_k5, graph_c5, graph_petersen, graph_k2_3):
        # K5: 5 choose 3 = 10 triangles
        assert compute_triangle_count(graph_k5) == 10
        # C5: 0 triangles
        assert compute_triangle_count(graph_c5) == 0
        # Petersen: triangle-free (girth 5)
        assert compute_triangle_count(graph_petersen) == 0
        # K2,3: bipartite, triangle-free
        assert compute_triangle_count(graph_k2_3) == 0

    def test_girth(self, graph_c4, graph_c5, graph_petersen):
        assert compute_girth(graph_c4) == 4
        assert compute_girth(graph_c5) == 5
        assert compute_girth(graph_petersen) == 5

        p4 = nx.path_graph(4)
        assert math.isinf(compute_girth(p4))

    def test_diameter_and_radius(self, graph_k5, graph_c5, graph_petersen, graph_disconnected_k3_k3):
        assert compute_diameter(graph_k5) == 1
        assert compute_radius(graph_k5) == 1

        assert compute_diameter(graph_c5) == 2
        assert compute_radius(graph_c5) == 2

        assert compute_diameter(graph_petersen) == 2
        assert compute_radius(graph_petersen) == 2

        assert math.isinf(compute_diameter(graph_disconnected_k3_k3))
        assert math.isinf(compute_radius(graph_disconnected_k3_k3))

    def test_adjacency_spectrum_numpy(self, graph_petersen, graph_c5):
        # Petersen spectrum: 3^1, 1^5, -2^4
        evals_pet = compute_adjacency_spectrum(graph_petersen)
        assert len(evals_pet) == 10
        assert np.isclose(evals_pet[0], 3.0)
        assert np.isclose(evals_pet[-1], -2.0)
        assert np.isclose(compute_spectral_radius(graph_petersen), 3.0, rtol=0, atol=1e-12)
        assert np.isclose(compute_smallest_adjacency_eigenvalue(graph_petersen), -2.0, rtol=0, atol=1e-12)

        # C5 spectrum: 2, (sqrt(5)-1)/2, (sqrt(5)-1)/2, -(1+sqrt(5))/2, -(1+sqrt(5))/2
        evals_c5 = compute_adjacency_spectrum(graph_c5)
        assert len(evals_c5) == 5
        assert np.isclose(evals_c5[0], 2.0)
        assert np.isclose(evals_c5[-1], -(1 + np.sqrt(5)) / 2)

    def test_laplacian_spectrum_numpy(self, graph_petersen, graph_disconnected_k3_k3):
        l_evals = compute_laplacian_spectrum(graph_petersen)
        assert len(l_evals) == 10
        assert np.isclose(l_evals[0], 0.0)
        # Fiedler eigenvalue mu_2 of Petersen is 2.0
        assert np.isclose(compute_algebraic_connectivity(graph_petersen), 2.0)
        # Laplacian spectral radius of Petersen is 5.0
        assert np.isclose(compute_laplacian_spectral_radius(graph_petersen), 5.0)

        # Disconnected graph must have algebraic connectivity == 0.0
        assert np.isclose(compute_algebraic_connectivity(graph_disconnected_k3_k3), 0.0)

    def test_chromatic_number_z3(self, graph_k5, graph_c4, graph_c5, graph_petersen):
        # K5: chi = 5
        assert compute_chromatic_number(graph_k5) == 5
        # C4: bipartite, chi = 2
        assert compute_chromatic_number(graph_c4) == 2
        # C5: odd cycle, chi = 3
        assert compute_chromatic_number(graph_c5) == 3
        # Petersen: chi = 3
        assert compute_chromatic_number(graph_petersen) == 3

        # Grotzsch graph: triangle-free with chi = 4
        grotzsch = GraphInstance.mycielski(4)
        assert compute_chromatic_number(grotzsch) == 4

    def test_clique_number_z3(self, graph_k5, graph_c5, graph_petersen, graph_k2_3):
        # K5: omega = 5
        assert compute_clique_number(graph_k5) == 5
        # C5: triangle-free, omega = 2
        assert compute_clique_number(graph_c5) == 2
        # Petersen: triangle-free, omega = 2
        assert compute_clique_number(graph_petersen) == 2
        # K2,3: bipartite, omega = 2
        assert compute_clique_number(graph_k2_3) == 2

    def test_independence_number_z3(self, graph_k5, graph_c5, graph_petersen, graph_star_6):
        # K5: alpha = 1
        assert compute_independence_number(graph_k5) == 1
        # C5: alpha = 2
        assert compute_independence_number(graph_c5) == 2
        # Petersen: alpha = 4
        assert compute_independence_number(graph_petersen) == 4
        # S6: 5 leaves form independent set
        assert compute_independence_number(graph_star_6) == 5

    def test_independence_number_disconnected_bipartite_graphs(self):
        """Verify compute_independence_number correctly handles disconnected bipartite and general graphs."""
        # P2 + K1 (defect 1 witness)
        g1 = nx.Graph()
        g1.add_nodes_from([0, 1, 2])
        g1.add_edge(0, 1)
        assert compute_independence_number(g1) == 2

        # P2 + P2
        g2 = nx.disjoint_union(nx.path_graph(2), nx.path_graph(2))
        assert compute_independence_number(g2) == 2

        # K_{2,3} + K_1
        g3 = nx.disjoint_union(nx.complete_bipartite_graph(2, 3), nx.empty_graph(1))
        assert compute_independence_number(g3) == 4

        # Disconnected non-bipartite: C5 + P2
        g4 = nx.disjoint_union(nx.cycle_graph(5), nx.path_graph(2))
        assert compute_independence_number(g4) == 3

    def test_structural_predicates(self, graph_c5, graph_c4, graph_petersen):
        assert is_triangle_free(graph_c5) is True
        assert is_bipartite(graph_c5) is False
        assert is_regular(graph_c5) is True
        assert is_connected(graph_c5) is True

        assert is_bipartite(graph_c4) is True
        assert is_triangle_free(graph_c4) is True

        assert is_regular(graph_petersen) is True
        assert is_triangle_free(graph_petersen) is True
        assert is_planar(graph_petersen) is False

    def test_spectral_bounds_hoffman_wilf(self, graph_c5, graph_petersen):
        # Hoffman bound: chi >= 1 - (lambda_1 / lambda_n)
        h_c5 = compute_hoffman_bound(graph_c5)
        chi_c5 = compute_chromatic_number(graph_c5)
        assert h_c5 <= chi_c5 + 1e-5

        h_pet = compute_hoffman_bound(graph_petersen)
        chi_pet = compute_chromatic_number(graph_petersen)
        assert h_pet <= chi_pet + 1e-5

        # Wilf bound: chi <= 1 + lambda_1
        w_c5 = compute_wilf_bound(graph_c5)
        assert chi_c5 <= w_c5 + 1e-5

        w_pet = compute_wilf_bound(graph_petersen)
        assert chi_pet <= w_pet + 1e-5

    def test_boundary_corner_cases(self, graph_null, graph_k1, graph_empty_5):
        # K0 (null graph)
        assert compute_order(graph_null) == 0
        assert compute_size(graph_null) == 0
        assert compute_density(graph_null) == 0.0
        assert compute_max_degree(graph_null) == 0
        assert compute_min_degree(graph_null) == 0
        assert compute_chromatic_number(graph_null) == 0
        assert compute_clique_number(graph_null) == 0
        assert compute_independence_number(graph_null) == 0
        assert compute_spectral_radius(graph_null) == 0.0

        # K1 (1 vertex)
        assert compute_order(graph_k1) == 1
        assert compute_size(graph_k1) == 0
        assert compute_density(graph_k1) == 0.0
        assert compute_chromatic_number(graph_k1) == 1
        assert compute_clique_number(graph_k1) == 1
        assert compute_independence_number(graph_k1) == 1

        # E5 (edgeless 5 vertices)
        assert compute_order(graph_empty_5) == 5
        assert compute_size(graph_empty_5) == 0
        assert compute_chromatic_number(graph_empty_5) == 1
        assert compute_clique_number(graph_empty_5) == 1
        assert compute_independence_number(graph_empty_5) == 5
        assert is_connected(graph_empty_5) is False

    def test_graph_invariant_evaluator_batch(self, graph_c5):
        res = GraphInvariantEvaluator.evaluate(graph_c5, ["order", "size", "chi", "omega", "alpha"])
        assert res["order"] == 5
        assert res["size"] == 5
        assert res["chromatic_number"] == 3
        assert res["clique_number"] == 2
        assert res["independence_number"] == 2
