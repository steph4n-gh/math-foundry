"""Empirical Adversarial Challenge Suite for Milestone 1 Invariants and AST Evaluation Bugfixes.

Authored by challenger_m1_fix_1.
Adversarially stresses:
1. `compute_independence_number`:
   - Complex disconnected graphs (P2 + K1, P3 + P4, star + isolated + bipartite, K5 + C5).
   - Multi-component non-bipartite graphs (Petersen + K5 + 3 K1, Grotzsch + C5, odd cycle unions).
   - High-volume randomized oracle fuzz testing against exact complement maximum clique oracle.
   - Degenerate boundary cases (null graph, isolated discrete graphs, disconnected cliques, string node IDs).

2. `Conjecture.evaluate`:
   - Null graphs (n=0): Premise guard short-circuiting on expressions containing division (1/alpha, 1/omega, n/alpha, inv(alpha), inv(omega)).
   - Single vertex (n=1): Evaluation of reciprocal and fractional invariant expressions.
   - Disconnected graphs: Evaluation of expressions containing division across multi-component graphs.
   - Adversarial boundary edge cases: Unguarded and negated property guard behaviors on K0.
"""

from __future__ import annotations

import random
from typing import List, Tuple
import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.invariants import (
    compute_independence_number,
    compute_clique_number,
    compute_chromatic_number,
    GraphInvariantEvaluator,
)


def _oracle_independence_number(G: nx.Graph) -> int:
    """Exact mathematical oracle for independence number: alpha(G) = omega(complement(G))."""
    if G.number_of_nodes() == 0:
        return 0
    comp = nx.complement(G)
    clique, _ = nx.algorithms.clique.max_weight_clique(comp, weight=None)
    return len(clique)


class TestChallengerIndependenceNumberDisconnected:
    """Empirical challenge tests for compute_independence_number on complex disconnected graphs."""

    def test_p2_union_k1(self):
        """P2 + K1: Path of length 1 (alpha=1) + isolated vertex (alpha=1) -> alpha=2."""
        g = nx.disjoint_union(nx.path_graph(2), nx.empty_graph(1))
        assert nx.is_bipartite(g)
        assert not nx.is_connected(g)
        assert compute_independence_number(g) == 2

    def test_p3_union_p4(self):
        """P3 + P4: Path of length 2 (alpha=2) + path of length 3 (alpha=2) -> alpha=4."""
        g = nx.disjoint_union(nx.path_graph(3), nx.path_graph(4))
        assert nx.is_bipartite(g)
        assert not nx.is_connected(g)
        assert compute_independence_number(g) == 4

    def test_star_isolated_bipartite(self):
        """Star + isolated + bipartite: S4 + K1 + K_{2,3} and S10 + 5 K1 + K_{3,5}."""
        # Case 1: S4 (5 nodes, alpha=4) + K1 (alpha=1) + K_{2,3} (alpha=3) -> alpha=8
        g1 = nx.disjoint_union(nx.star_graph(4), nx.empty_graph(1))
        g1 = nx.disjoint_union(g1, nx.complete_bipartite_graph(2, 3))
        assert nx.is_bipartite(g1)
        assert compute_independence_number(g1) == 8

        # Case 2: S10 (11 nodes, alpha=10) + 5 K1 (alpha=5) + K_{3,5} (alpha=5) -> alpha=20
        g2 = nx.disjoint_union(nx.star_graph(10), nx.empty_graph(5))
        g2 = nx.disjoint_union(g2, nx.complete_bipartite_graph(3, 5))
        assert nx.is_bipartite(g2)
        assert compute_independence_number(g2) == 20

    def test_k5_union_c5_non_bipartite(self):
        """K5 + C5: Non-bipartite complete graph (alpha=1) + non-bipartite 5-cycle (alpha=2) -> alpha=3."""
        g = nx.disjoint_union(nx.complete_graph(5), nx.cycle_graph(5))
        assert not nx.is_bipartite(g)
        assert not nx.is_connected(g)
        assert compute_independence_number(g) == 3

    def test_complex_multicomponent_non_bipartite(self):
        """Multiple non-bipartite components and mixed families."""
        # 1. Petersen (alpha=4) + K5 (alpha=1) + 3 K1 (alpha=3) -> alpha=8
        g_pet = nx.disjoint_union(nx.petersen_graph(), nx.complete_graph(5))
        g_pet = nx.disjoint_union(g_pet, nx.empty_graph(3))
        assert not nx.is_bipartite(g_pet)
        assert compute_independence_number(g_pet) == 8

        # 2. Grotzsch / Mycielski(4) (order 11, alpha=5) + C5 (alpha=2) -> alpha=7
        grotzsch = nx.mycielski_graph(4)
        g_myc = nx.disjoint_union(grotzsch, nx.cycle_graph(5))
        assert not nx.is_bipartite(g_myc)
        assert compute_independence_number(g_myc) == 7

        # 3. Odd cycle union: C5 (alpha=2) + C7 (alpha=3) + C9 (alpha=4) -> alpha=9
        g_odd = nx.disjoint_union(nx.cycle_graph(5), nx.cycle_graph(7))
        g_odd = nx.disjoint_union(g_odd, nx.cycle_graph(9))
        assert not nx.is_bipartite(g_odd)
        assert compute_independence_number(g_odd) == 9

    def test_boundary_disconnected_graphs(self):
        """Boundary corner cases: discrete empty graphs, disjoint cliques, string node IDs."""
        # Null graph
        assert compute_independence_number(nx.empty_graph(0)) == 0

        # Discrete graph 10 K1
        assert compute_independence_number(nx.empty_graph(10)) == 10

        # Disconnected cliques: K3 (alpha=1) + K4 (alpha=1) + K5 (alpha=1) -> alpha=3
        g_cliques = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(4))
        g_cliques = nx.disjoint_union(g_cliques, nx.complete_graph(5))
        assert compute_independence_number(g_cliques) == 3

        # Non-integer / string node labels
        g_str = nx.Graph()
        g_str.add_edge("node_a", "node_b")
        g_str.add_node("node_isolated_c")
        g_str.add_edge("node_d", "node_e")
        # Components: {a, b} (alpha=1), {c} (alpha=1), {d, e} (alpha=1) -> alpha=3
        assert compute_independence_number(g_str) == 3

    def test_oracle_fuzz_random_disconnected_graphs(self):
        """Stress tests 50 randomized multi-component graph instances against exact complement clique oracle."""
        rng = random.Random(1337)
        for i in range(50):
            k_comps = rng.randint(2, 5)
            g = nx.Graph()
            for _ in range(k_comps):
                choice = rng.randint(0, 5)
                n = rng.randint(1, 6)
                if choice == 0:
                    sub = nx.empty_graph(n)
                elif choice == 1:
                    sub = nx.complete_graph(n)
                elif choice == 2:
                    sub = nx.cycle_graph(max(3, n))
                elif choice == 3:
                    sub = nx.path_graph(max(1, n))
                elif choice == 4:
                    sub = nx.complete_bipartite_graph(rng.randint(1, 3), rng.randint(1, 3))
                else:
                    sub = nx.erdos_renyi_graph(max(2, n), 0.45, seed=rng.randint(0, 10000))
                g = nx.disjoint_union(g, sub)

            expected = _oracle_independence_number(g)
            actual = compute_independence_number(g)
            assert actual == expected, f"Fuzz test iteration {i} failed: expected {expected}, got {actual}"


class TestChallengerConjectureEvaluation:
    """Empirical challenge tests for Conjecture.evaluate with division operations across graph spaces."""

    def test_evaluate_null_graph_guarded_division_safety(self):
        """Conjecture.evaluate on K0 with division by alpha/omega guarded by order >= 1, is_connected, or is_tree."""
        g0 = nx.empty_graph(0)

        # 1. Binary division by alpha: order >= 1 ==> chi >= 1 / alpha
        c1 = Conjecture.create(
            "guard_div_alpha",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds1, l1, r1 = c1.evaluate(g0)
        assert holds1 is True and (l1, r1) == (0.0, 0.0)

        # 2. Binary division by omega: order >= 1 ==> chi >= 1 / omega
        c2 = Conjecture.create(
            "guard_div_omega",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("clique_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds2, l2, r2 = c2.evaluate(g0)
        assert holds2 is True and (l2, r2) == (0.0, 0.0)

        # 3. Unary inverse: order >= 1 ==> inv(alpha) <= 1.0
        c3 = Conjecture.create(
            "guard_inv_alpha",
            lhs=UnaryOpNode("inv", InvariantNode("independence_number")),
            rel="<=",
            rhs=ConstantNode(1.0),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds3, l3, r3 = c3.evaluate(g0)
        assert holds3 is True and (l3, r3) == (0.0, 0.0)

        # 4. Ramsey archetype: order >= 1 ==> chi >= order / independence_number
        c4 = Conjecture.create(
            "ramsey_archetype",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", InvariantNode("order"), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds4, l4, r4 = c4.evaluate(g0)
        assert holds4 is True and (l4, r4) == (0.0, 0.0)

        # 5. Connected property guard: is_connected ==> chi >= 1 / alpha
        c5 = Conjecture.create(
            "guard_connected_div_alpha",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="is_connected"),
        )
        holds5, l5, r5 = c5.evaluate(g0)
        assert holds5 is True and (l5, r5) == (0.0, 0.0)

        # 6. Tree property guard: is_tree ==> chi >= 1 / alpha
        c6 = Conjecture.create(
            "guard_tree_div_alpha",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="is_tree"),
        )
        holds6, l6, r6 = c6.evaluate(g0)
        assert holds6 is True and (l6, r6) == (0.0, 0.0)

    def test_evaluate_single_vertex_division(self):
        """Conjecture.evaluate on single vertex K1 with division by alpha and omega."""
        g1 = nx.empty_graph(1)
        assert compute_independence_number(g1) == 1
        assert compute_clique_number(g1) == 1

        # Expression: order >= 1 ==> chi >= 1 / alpha
        c1 = Conjecture.create(
            "c_div_alpha",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds1, l1, r1 = c1.evaluate(g1)
        assert holds1 is True
        assert l1 == 1.0 and r1 == 1.0

        # Expression: order >= 1 ==> chi >= 1 / omega
        c2 = Conjecture.create(
            "c_div_omega",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("clique_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds2, l2, r2 = c2.evaluate(g1)
        assert holds2 is True
        assert l2 == 1.0 and r2 == 1.0

        # Unary inverse: order >= 1 ==> inv(alpha) <= 1.0
        c3 = Conjecture.create(
            "c_inv_alpha",
            lhs=UnaryOpNode("inv", InvariantNode("independence_number")),
            rel="<=",
            rhs=ConstantNode(1.0),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )
        holds3, l3, r3 = c3.evaluate(g1)
        assert holds3 is True
        assert l3 == 1.0 and r3 == 1.0

    def test_evaluate_disconnected_graphs_division(self):
        """Conjecture.evaluate on complex disconnected graphs with expressions containing division."""
        g_p2_k1 = nx.disjoint_union(nx.path_graph(2), nx.empty_graph(1))
        g_p3_p4 = nx.disjoint_union(nx.path_graph(3), nx.path_graph(4))
        g_star_bip = nx.disjoint_union(nx.star_graph(4), nx.empty_graph(1))
        g_star_bip = nx.disjoint_union(g_star_bip, nx.complete_bipartite_graph(2, 3))
        g_k5_c5 = nx.disjoint_union(nx.complete_graph(5), nx.cycle_graph(5))
        g_5k1 = nx.empty_graph(5)

        test_graphs = [
            ("P2 + K1", g_p2_k1, 2, 2, 2),  # (name, G, alpha, omega, chi)
            ("P3 + P4", g_p3_p4, 4, 2, 2),
            ("Star + iso + bip", g_star_bip, 8, 2, 2),
            ("K5 + C5", g_k5_c5, 3, 5, 5),
            ("5 K1", g_5k1, 5, 1, 1),
        ]

        # 1. 1 / alpha bound
        c_alpha = Conjecture.create(
            "div_alpha",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )

        # 2. 1 / omega bound
        c_omega = Conjecture.create(
            "div_omega",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("clique_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )

        # 3. Ramsey order / alpha bound
        c_ramsey = Conjecture.create(
            "ramsey",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=BinaryOpNode("/", InvariantNode("order"), InvariantNode("independence_number")),
            guard=GuardPredicate(property_name_or_type="comparison", invariant="order", op=">=", threshold=1.0),
        )

        for name, g, expected_alpha, expected_omega, expected_chi in test_graphs:
            # Check 1/alpha
            holds_a, la, ra = c_alpha.evaluate(g)
            assert holds_a is True, f"Failed on {name}"
            assert abs(la - expected_chi) < 1e-6
            assert abs(ra - (1.0 / expected_alpha)) < 1e-6

            # Check 1/omega
            holds_w, lw, rw = c_omega.evaluate(g)
            assert holds_w is True, f"Failed on {name}"
            assert abs(lw - expected_chi) < 1e-6
            assert abs(rw - (1.0 / expected_omega)) < 1e-6

            # Check Ramsey
            holds_r, lr, rr = c_ramsey.evaluate(g)
            assert holds_r is True, f"Failed on {name}"
            assert abs(lr - expected_chi) < 1e-6
            assert abs(rr - (g.number_of_nodes() / expected_alpha)) < 1e-6

    def test_adversarial_unguarded_division_on_null_graph_caveat(self):
        """Documents domain behavior: unguarded division by alpha on K0 raises ZeroDivisionError.

        On the null graph K0, alpha(K0) = 0. An unguarded conjecture '1 <= 1 / alpha'
        evaluated on K0 triggers ZeroDivisionError because the expression is outside
        the mathematical domain of the invariant. This confirms the necessity of
        premise guards (e.g. 'order >= 1') for fractional conjectures.
        """
        g0 = nx.empty_graph(0)
        c_unguarded = Conjecture.create(
            "unguarded_div_alpha",
            lhs=ConstantNode(1.0),
            rel="<=",
            rhs=BinaryOpNode("/", ConstantNode(1.0), InvariantNode("independence_number")),
        )

        with pytest.raises(ZeroDivisionError, match="Domain error: division by zero in '/'"):
            c_unguarded.evaluate(g0)
