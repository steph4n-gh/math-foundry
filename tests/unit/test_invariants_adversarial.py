"""Adversarial stress-testing suite for Milestone 1 invariant computations.

Tests invariants on adversarial, non-trivial, and boundary graphs:
- Empty graph (n=0)
- Isolated vertices (E_n for n in {1, 2, 5, 10})
- Complete graphs (K_n for n in {1, 2, 3, 4, 5, 6})
- Cycles (C_5, C_7, C_6)
- Bipartite graphs (K_{3,3}, K_{2,4})
- Disconnected components (K_3 u K_3, K_1 u K_4, C_5 u C_7)
- Petersen graph (10 vertices, 15 edges, 3-regular, girth 5, chi 3)
- Mycielski / Grötzsch graph (11 vertices, 20 edges, triangle-free, chi 4)

Verifies algebraic properties:
- Handshaking lemma: sum d(v) = 2m
- Triangle trace identity: T(G) = (1/6) * Tr(A^3)
- Laplacian spectral properties: mu_1 = 0 <= mu_2 <= ... <= mu_n, sum mu_i = 2m
- Algebraic connectivity: mu_2 = 0 iff disconnected (n >= 2)
- Hoffman spectral lower bound: H(G) = 1 - (lambda_1 / lambda_n) <= chi(G)
- Wilf spectral upper bound: W(G) = 1 + lambda_1 >= chi(G)
- Clique-chromatic bound: omega(G) <= chi(G)
- Independence-chromatic bound: chi(G) >= n / alpha(G) (n >= 1)

Verifies conjecture evaluation:
- 'is_triangle_free ==> chi <= 2' on C_5 evaluates to False (lhs=3.0, rhs=2.0)
"""

from __future__ import annotations

import math
import sys
from pathlib import Path
from typing import Dict, List, Tuple

# Ensure autonomous_math root is on sys.path for standalone script execution
AUTONOMOUS_MATH_ROOT = Path(__file__).resolve().parent.parent.parent
if str(AUTONOMOUS_MATH_ROOT) not in sys.path:
    sys.path.insert(0, str(AUTONOMOUS_MATH_ROOT))

import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    ConstantNode,
    Conjecture,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import (
    GraphInvariantEvaluator,
    STANDARD_SCALAR_INVARIANTS,
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


def get_adversarial_graph_corpus() -> Dict[str, nx.Graph]:
    """Catalog of boundary, adversarial, and extremal test graphs."""
    return {
        "empty_0": nx.empty_graph(0),
        "isolated_1": nx.empty_graph(1),
        "isolated_2": nx.empty_graph(2),
        "isolated_5": nx.empty_graph(5),
        "isolated_10": nx.empty_graph(10),
        "k1": nx.complete_graph(1),
        "k2": nx.complete_graph(2),
        "k3": nx.complete_graph(3),
        "k4": nx.complete_graph(4),
        "k5": nx.complete_graph(5),
        "k6": nx.complete_graph(6),
        "c5": nx.cycle_graph(5),
        "c7": nx.cycle_graph(7),
        "c6": nx.cycle_graph(6),
        "k3_3": nx.complete_bipartite_graph(3, 3),
        "k2_4": nx.complete_bipartite_graph(2, 4),
        "k3_u_k3": nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3)),
        "k1_u_k4": nx.disjoint_union(nx.complete_graph(1), nx.complete_graph(4)),
        "c5_u_c7": nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(7)),
        "petersen": nx.petersen_graph(),
        "grotzsch": nx.mycielski_graph(4),
        "star_5": nx.star_graph(4),
        "wheel_6": nx.wheel_graph(6),
    }


class TestAdversarialBoundaryGraphs:
    """Stress tests on specific boundary, extremal, and non-trivial graph topologies."""

    def test_empty_graph_n0(self):
        """Null graph with n=0, m=0: must evaluate all invariants without raising exceptions."""
        g0 = nx.empty_graph(0)
        inst = GraphInstance.from_networkx(g0)

        # Elementary invariants
        assert compute_order(inst) == 0
        assert compute_size(inst) == 0
        assert compute_max_degree(inst) == 0
        assert compute_min_degree(inst) == 0
        assert compute_average_degree(inst) == 0.0
        assert compute_density(inst) == 0.0

        # Metric & topological invariants
        assert compute_triangle_count(inst) == 0
        assert math.isinf(compute_girth(inst))
        assert compute_diameter(inst) == 0
        assert compute_radius(inst) == 0

        # Spectral invariants
        assert compute_adjacency_spectrum(inst) == []
        assert compute_spectral_radius(inst) == 0.0
        assert compute_smallest_adjacency_eigenvalue(inst) == 0.0
        assert compute_laplacian_spectrum(inst) == []
        assert compute_algebraic_connectivity(inst) == 0.0
        assert compute_laplacian_spectral_radius(inst) == 0.0
        assert compute_hoffman_bound(inst) == 0.0
        assert compute_wilf_bound(inst) == 0.0

        # NP-hard invariants
        assert compute_chromatic_number(inst) == 0
        assert compute_clique_number(inst) == 0
        assert compute_independence_number(inst) == 0

        # Predicates
        assert is_empty(inst) is True
        assert is_connected(inst) is False
        assert is_regular(inst) is True
        assert is_complete(inst) is False
        assert is_planar(inst) is True
        assert is_forest(inst) is True
        assert is_tree(inst) is False
        assert is_triangle_free(inst) is True
        assert is_bipartite(inst) is True
        assert is_chordal(inst) is True
        assert is_eulerian(inst) is False

        # Batch evaluation
        batch = GraphInvariantEvaluator.evaluate(inst, STANDARD_SCALAR_INVARIANTS)
        assert len(batch) >= len(STANDARD_SCALAR_INVARIANTS)
        assert batch["order"] == 0

    @pytest.mark.parametrize("n", [1, 2, 5, 10])
    def test_isolated_vertices_en(self, n: int):
        """Edgeless graphs E_n with n vertices and 0 edges."""
        en = nx.empty_graph(n)
        inst = GraphInstance.from_networkx(en)

        assert compute_order(inst) == n
        assert compute_size(inst) == 0
        assert compute_max_degree(inst) == 0
        assert compute_min_degree(inst) == 0
        assert compute_density(inst) == 0.0
        assert compute_triangle_count(inst) == 0

        # Invariants for E_n
        assert compute_chromatic_number(inst) == 1
        assert compute_clique_number(inst) == 1
        assert compute_independence_number(inst) == n

        # Spectra: all zeros
        adj_spec = compute_adjacency_spectrum(inst)
        lap_spec = compute_laplacian_spectrum(inst)
        assert len(adj_spec) == n and all(x == 0.0 for x in adj_spec)
        assert len(lap_spec) == n and all(x == 0.0 for x in lap_spec)

        # Spectral bounds
        assert compute_hoffman_bound(inst) == 1.0
        assert compute_wilf_bound(inst) == 1.0

        # Connectivity
        if n == 1:
            assert is_connected(inst) is True
            assert compute_diameter(inst) == 0
            assert compute_radius(inst) == 0
        else:
            assert is_connected(inst) is False
            assert math.isinf(compute_diameter(inst))
            assert math.isinf(compute_radius(inst))
            assert compute_algebraic_connectivity(inst) == 0.0

    @pytest.mark.parametrize("n", [1, 2, 3, 4, 5, 6])
    def test_complete_graphs_kn(self, n: int):
        """Complete graphs K_n: extreme density, exact spectral and chromatic identities."""
        kn = nx.complete_graph(n)
        inst = GraphInstance.from_networkx(kn)

        expected_m = n * (n - 1) // 2
        expected_tri = n * (n - 1) * (n - 2) // 6

        assert compute_order(inst) == n
        assert compute_size(inst) == expected_m
        assert compute_triangle_count(inst) == expected_tri
        assert compute_chromatic_number(inst) == n
        assert compute_clique_number(inst) == n
        assert compute_independence_number(inst) == 1
        assert np.isclose(compute_density(inst), 1.0 if n >= 2 else 0.0)

        # Adjacency eigenvalues: (n-1)^1, (-1)^(n-1) for n >= 2
        if n >= 2:
            assert np.isclose(compute_spectral_radius(inst), float(n - 1), atol=1e-5)
            assert np.isclose(compute_smallest_adjacency_eigenvalue(inst), -1.0, atol=1e-5)

            # Hoffman bound exact equality: 1 - ((n-1) / (-1)) = n = chi(K_n)
            assert np.isclose(compute_hoffman_bound(inst), float(n), atol=1e-5)

            # Wilf bound exact equality: 1 + (n-1) = n = chi(K_n)
            assert np.isclose(compute_wilf_bound(inst), float(n), atol=1e-5)

            # Laplacian eigenvalues: 0^1, n^(n-1)
            lap = compute_laplacian_spectrum(inst)
            assert np.isclose(lap[0], 0.0, atol=1e-6)
            assert all(np.isclose(x, float(n), atol=1e-5) for x in lap[1:])
            assert np.isclose(compute_algebraic_connectivity(inst), float(n), atol=1e-5)

    def test_cycles_c5_and_c7(self):
        """Cycles C_5 and C_7: odd cycle benchmarks, triangle-free, chromatic 3."""
        for n in (5, 7):
            cn = nx.cycle_graph(n)
            inst = GraphInstance.from_networkx(cn)

            assert compute_order(inst) == n
            assert compute_size(inst) == n
            assert compute_max_degree(inst) == 2
            assert compute_min_degree(inst) == 2
            assert is_regular(inst) is True
            assert is_connected(inst) is True
            assert compute_girth(inst) == n
            assert compute_triangle_count(inst) == 0
            assert is_triangle_free(inst) is True

            # Chromatic, clique, and independence numbers
            assert compute_chromatic_number(inst) == 3
            assert compute_clique_number(inst) == 2
            assert compute_independence_number(inst) == n // 2

            # Spectral radius = 2.0
            assert np.isclose(compute_spectral_radius(inst), 2.0, atol=1e-6)
            # Wilf bound: 1 + 2 = 3 == chi(C_n)
            assert np.isclose(compute_wilf_bound(inst), 3.0, atol=1e-6)

            # Hoffman bound <= chi
            hoffman = compute_hoffman_bound(inst)
            assert hoffman <= 3.0 + 1e-5

            # Laplacian algebraic connectivity: 2 - 2*cos(2*pi/n)
            expected_mu2 = 2.0 - 2.0 * math.cos(2.0 * math.pi / n)
            mu2 = compute_algebraic_connectivity(inst)
            assert np.isclose(mu2, expected_mu2, atol=1e-5)

    def test_complete_bipartite_k3_3(self):
        """Complete bipartite graph K_{3,3}: triangle-free, chromatic 2, girth 4."""
        k33 = nx.complete_bipartite_graph(3, 3)
        inst = GraphInstance.from_networkx(k33)

        assert compute_order(inst) == 6
        assert compute_size(inst) == 9
        assert compute_max_degree(inst) == 3
        assert compute_min_degree(inst) == 3
        assert is_bipartite(inst) is True
        assert compute_girth(inst) == 4
        assert compute_triangle_count(inst) == 0
        assert compute_chromatic_number(inst) == 2
        assert compute_clique_number(inst) == 2
        assert compute_independence_number(inst) == 3

        # Adjacency spectrum: 3, 0, 0, 0, 0, -3
        adj = compute_adjacency_spectrum(inst)
        assert np.isclose(adj[0], 3.0, atol=1e-5)
        assert np.isclose(adj[-1], -3.0, atol=1e-5)

        # Hoffman bound exact equality: 1 - (3 / (-3)) = 2.0 = chi(K_3,3)
        assert np.isclose(compute_hoffman_bound(inst), 2.0, atol=1e-5)
        # Wilf bound: 1 + 3 = 4 >= 2
        assert np.isclose(compute_wilf_bound(inst), 4.0, atol=1e-5)

        # Laplacian spectrum: 0 (x1), 3 (x4), 6 (x1)
        lap = compute_laplacian_spectrum(inst)
        assert np.isclose(lap[0], 0.0, atol=1e-5)
        assert np.isclose(compute_algebraic_connectivity(inst), 3.0, atol=1e-5)
        assert np.isclose(compute_laplacian_spectral_radius(inst), 6.0, atol=1e-5)

    def test_disconnected_k3_u_k3(self):
        """Disconnected graph consisting of two disjoint triangles K_3 u K_3."""
        g = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
        inst = GraphInstance.from_networkx(g)

        assert compute_order(inst) == 6
        assert compute_size(inst) == 6
        assert compute_triangle_count(inst) == 2
        assert compute_chromatic_number(inst) == 3
        assert compute_clique_number(inst) == 3
        assert compute_independence_number(inst) == 2

        assert is_connected(inst) is False
        assert math.isinf(compute_diameter(inst))
        assert math.isinf(compute_radius(inst))
        assert compute_algebraic_connectivity(inst) == 0.0

        # Multiplicity of 0 in Laplacian spectrum equals 2 (number of components)
        lap = compute_laplacian_spectrum(inst)
        zero_eigenvalues = [x for x in lap if abs(x) < 1e-5]
        assert len(zero_eigenvalues) == 2
        assert np.isclose(sum(lap), 12.0, atol=1e-5)  # 2m = 12

    def test_petersen_graph(self):
        """Petersen graph: 10 vertices, 15 edges, 3-regular, girth 5, chi 3, omega 2, alpha 4."""
        pet = nx.petersen_graph()
        inst = GraphInstance.from_networkx(pet)

        assert compute_order(inst) == 10
        assert compute_size(inst) == 15
        assert compute_max_degree(inst) == 3
        assert compute_min_degree(inst) == 3
        assert is_regular(inst) is True
        assert compute_girth(inst) == 5
        assert compute_triangle_count(inst) == 0
        assert is_triangle_free(inst) is True
        assert is_bipartite(inst) is False
        assert is_planar(inst) is False

        assert compute_chromatic_number(inst) == 3
        assert compute_clique_number(inst) == 2
        assert compute_independence_number(inst) == 4

        # Adjacency spectrum: 3^1, 1^5, -2^4
        assert np.isclose(compute_spectral_radius(inst), 3.0, atol=1e-5)
        assert np.isclose(compute_smallest_adjacency_eigenvalue(inst), -2.0, atol=1e-5)

        # Hoffman bound: 1 - (3 / (-2)) = 2.5 <= 3
        assert np.isclose(compute_hoffman_bound(inst), 2.5, atol=1e-5)
        # Wilf bound: 1 + 3 = 4 >= 3
        assert np.isclose(compute_wilf_bound(inst), 4.0, atol=1e-5)

        # Laplacian spectrum: 0^1, 2^5, 5^4
        assert np.isclose(compute_algebraic_connectivity(inst), 2.0, atol=1e-5)
        assert np.isclose(compute_laplacian_spectral_radius(inst), 5.0, atol=1e-5)

    def test_grotzsch_mycielski_graph(self):
        """Grötzsch graph (Mycielskian of C_5): 11 vertices, 20 edges, triangle-free, chi 4."""
        grotzsch = nx.mycielski_graph(4)
        inst = GraphInstance.from_networkx(grotzsch)

        assert compute_order(inst) == 11
        assert compute_size(inst) == 20
        assert compute_triangle_count(inst) == 0
        assert is_triangle_free(inst) is True
        assert compute_girth(inst) == 4
        assert is_bipartite(inst) is False

        # Chromatic number is strictly 4 (smallest triangle-free 4-chromatic graph)
        assert compute_chromatic_number(inst) == 4
        assert compute_clique_number(inst) == 2
        assert compute_independence_number(inst) == 5

        # Spectral bounds
        h = compute_hoffman_bound(inst)
        w = compute_wilf_bound(inst)
        assert h <= 4.0 + 1e-5
        assert 4.0 <= w + 1e-5


class TestAdversarialAlgebraicProperties:
    """Verifies algebraic and spectral theorems across an extensive corpus."""

    @pytest.fixture(scope="class")
    def corpus(self) -> Dict[str, nx.Graph]:
        return get_adversarial_graph_corpus()

    def test_handshaking_lemma_all_graphs(self, corpus):
        """Handshaking lemma: sum_{v in V} d(v) = 2m."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            n = compute_order(inst)
            m = compute_size(inst)
            if n == 0:
                continue
            deg_sum = sum(dict(G.degree()).values())
            assert deg_sum == 2 * m, f"{name}: sum d(v)={deg_sum} != 2m={2*m}"
            assert np.isclose(compute_average_degree(inst), deg_sum / n)

    def test_triangle_trace_formula_all_graphs(self, corpus):
        """Trace formula: T(G) = (1/6) * Tr(A^3)."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            n = compute_order(inst)
            if n < 3:
                assert compute_triangle_count(inst) == 0
                continue
            A = inst.to_adjacency_matrix()
            A3 = A @ A @ A
            tr_A3 = int(np.trace(A3))
            assert tr_A3 % 6 == 0, f"{name}: Tr(A^3)={tr_A3} not divisible by 6"
            expected_triangles = tr_A3 // 6
            computed_triangles = compute_triangle_count(inst)
            assert computed_triangles == expected_triangles, (
                f"{name}: T(G)={computed_triangles} != Tr(A^3)/6={expected_triangles}"
            )

    def test_laplacian_spectral_properties_all_graphs(self, corpus):
        """Laplacian spectrum: mu_1 = 0 <= mu_2 <= ... <= mu_n and sum mu_i = 2m."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            n = compute_order(inst)
            m = compute_size(inst)
            if n == 0:
                assert compute_laplacian_spectrum(inst) == []
                continue

            lap = compute_laplacian_spectrum(inst)
            assert len(lap) == n, f"{name}: laplacian spectrum length mismatch"

            # mu_1 = 0
            assert np.isclose(lap[0], 0.0, atol=1e-6), f"{name}: mu_1={lap[0]} != 0"

            # Monotonic ordering: mu_1 <= mu_2 <= ... <= mu_n
            for i in range(len(lap) - 1):
                assert lap[i] <= lap[i + 1] + 1e-9, (
                    f"{name}: laplacian eigenvalues not sorted at index {i}"
                )

            # Trace formula: sum mu_i = Tr(L) = sum d(v) = 2m
            assert np.isclose(sum(lap), 2.0 * m, atol=1e-5), (
                f"{name}: sum mu_i={sum(lap)} != 2m={2*m}"
            )

    def test_fiedler_algebraic_connectivity_all_graphs(self, corpus):
        """Fiedler value mu_2: mu_2 = 0 iff graph is disconnected (for n >= 2)."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            n = compute_order(inst)
            if n < 2:
                continue
            connected = is_connected(inst)
            mu2 = compute_algebraic_connectivity(inst)
            if connected:
                assert mu2 > 1e-6, f"{name}: connected graph has mu_2 <= 0 ({mu2})"
            else:
                assert np.isclose(mu2, 0.0, atol=1e-6), (
                    f"{name}: disconnected graph has mu_2 > 0 ({mu2})"
                )

    def test_hoffman_spectral_bound_all_graphs(self, corpus):
        """Hoffman bound: 1 - (lambda_1 / lambda_n) <= chi(G) for non-empty graphs."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            if compute_size(inst) == 0:
                continue
            hoffman = compute_hoffman_bound(inst)
            chi = compute_chromatic_number(inst)
            assert hoffman <= chi + 1e-5, (
                f"{name}: Hoffman bound violated: H={hoffman} > chi={chi}"
            )

    def test_wilf_spectral_bound_all_graphs(self, corpus):
        """Wilf bound: chi(G) <= 1 + lambda_1 for all graphs."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            if compute_order(inst) == 0:
                continue
            wilf = compute_wilf_bound(inst)
            chi = compute_chromatic_number(inst)
            assert chi <= wilf + 1e-5, (
                f"{name}: Wilf bound violated: chi={chi} > W={wilf}"
            )

    def test_clique_and_independence_bounds_all_graphs(self, corpus):
        """omega(G) <= chi(G) and chi(G) >= n / alpha(G)."""
        for name, G in corpus.items():
            inst = GraphInstance.from_networkx(G)
            n = compute_order(inst)
            if n == 0:
                continue
            omega = compute_clique_number(inst)
            chi = compute_chromatic_number(inst)
            alpha = compute_independence_number(inst)

            assert omega <= chi, f"{name}: omega={omega} > chi={chi}"
            assert chi >= math.ceil(n / alpha), (
                f"{name}: chi={chi} < ceil(n/alpha)={math.ceil(n/alpha)}"
            )


class TestAdversarialConjectureEvaluation:
    """Stress tests conjecture evaluation, vacuous truth, and the C5 refutation benchmark."""

    def test_c5_refutes_triangle_free_chi_le_2(self):
        """MANDATORY: Verify that 'is_triangle_free ==> chi <= 2' on C_5 returns False."""
        c5 = nx.cycle_graph(5)
        conj = Conjecture.create(
            id="falsify_triangle_free_bipartite",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=ConstantNode(2.0),
            guard=GuardPredicate("is_triangle_free"),
        )

        holds, lhs_val, rhs_val = conj.evaluate(c5)
        assert holds is False, "Conjecture must be refuted by C_5"
        assert lhs_val == 3.0, f"Expected LHS=3.0 on C_5, got {lhs_val}"
        assert rhs_val == 2.0, f"Expected RHS=2.0 on C_5, got {rhs_val}"

    def test_grotzsch_also_refutes_triangle_free_chi_le_2(self):
        """Grötzsch graph (triangle-free with chi=4) also decisively refutes the conjecture."""
        grotzsch = nx.mycielski_graph(4)
        conj = Conjecture.create(
            id="falsify_triangle_free_bipartite",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=ConstantNode(2.0),
            guard=GuardPredicate("is_triangle_free"),
        )

        holds, lhs_val, rhs_val = conj.evaluate(grotzsch)
        assert holds is False
        assert lhs_val == 4.0
        assert rhs_val == 2.0

    def test_vacuous_truth_when_guard_does_not_apply(self):
        """Conjecture with guard 'is_bipartite' on C_5 is vacuously True since C_5 is not bipartite."""
        c5 = nx.cycle_graph(5)
        conj = Conjecture.create(
            id="vacuous_on_c5",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=ConstantNode(2.0),
            guard=GuardPredicate("is_bipartite"),
        )

        holds, lhs_val, rhs_val = conj.evaluate(c5)
        assert holds is True, "Vacuous implication must evaluate to True"
        assert lhs_val == 0.0
        assert rhs_val == 0.0

    def test_universal_brooks_bound_survives_on_c5(self):
        """Universal conjecture: chi <= Delta + 1 holds on C_5 (3 <= 2 + 1)."""
        c5 = nx.cycle_graph(5)
        conj = Conjecture.create(
            id="brooks_loose_survives",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )

        holds, lhs_val, rhs_val = conj.evaluate(c5)
        assert holds is True
        assert lhs_val == 3.0
        assert rhs_val == 3.0

    def test_conjecture_evaluates_on_empty_and_isolated(self):
        """Conjecture evaluation handles edge graphs (n=0, n=1) cleanly without exceptions."""
        g0 = nx.empty_graph(0)
        g1 = nx.empty_graph(1)

        conj = Conjecture.create(
            id="edge_eval_test",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=InvariantNode("order"),
        )

        holds0, l0, r0 = conj.evaluate(g0)
        assert holds0 is True and l0 == 0.0 and r0 == 0.0

        holds1, l1, r1 = conj.evaluate(g1)
        assert holds1 is True and l1 == 1.0 and r1 == 1.0


if __name__ == "__main__":
    import sys

    print("Running adversarial invariant tests standalone...")
    pytest.main([__file__, "-v"])
