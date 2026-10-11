"""Adversarial stress-test suite for DalmatiansFilter and EchoFilter.

Authored by empirical challenger challenger_m1_fix_2 to stress-test:
1. DalmatiansFilter:
   - Permutation invariance across candidate upper and lower bounds.
   - Dominated bounds never leaking through.
   - Obsolete bounds pruned when superseded by Pareto envelopes.
2. EchoFilter:
   - Intra-batch duplicate conjectures.
   - Inverted relation pairs (A <= B and B >= A).
   - Transitive chains (A <= B, B <= C ==> A <= C) in arbitrary permutations.
   - Cyclic graphs and branches originating from cycle nodes.
"""

import itertools
import pytest
import networkx as nx

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.conjecturing.filters import DalmatiansFilter, EchoFilter


class TestDalmatiansFilterAdversarial:
    """Stress tests DalmatiansFilter across permutations and envelope dynamics."""

    @pytest.fixture
    def sample_graphs(self):
        """Construct four standard extremal/boundary test graphs."""
        g1 = nx.path_graph(2)      # P_2: order=2, Delta=1, chi=2, omega=2
        g2 = nx.cycle_graph(5)     # C_5: order=5, Delta=2, chi=3, omega=2
        g3 = nx.complete_graph(4)  # K_4: order=4, Delta=3, chi=4, omega=4
        g4 = nx.star_graph(4)      # K_{1,4}: order=5, Delta=4, chi=2, omega=2
        return [g1, g2, g3, g4]

    def test_strict_upper_bounds_permutation_invariance(self, sample_graphs):
        """Uniformly ordered upper bounds must prune to the unique tightest bound."""
        chi = InvariantNode("chromatic_number")
        b10 = Conjecture.create("b10", chi, "<=", ConstantNode(10.0))
        b5 = Conjecture.create("b5", chi, "<=", ConstantNode(5.0))
        b4 = Conjecture.create("b4", chi, "<=", ConstantNode(4.0))

        candidates = [b10, b5, b4]
        for perm in itertools.permutations(candidates):
            res = DalmatiansFilter.filter(list(perm), sample_graphs)
            assert [c.id for c in res] == ["b4"], f"Failed on perm {[c.id for c in perm]}"

    def test_strict_lower_bounds_permutation_invariance(self, sample_graphs):
        """Uniformly ordered lower bounds must prune to the unique tightest bound."""
        chi = InvariantNode("chromatic_number")
        l1 = Conjecture.create("l1", chi, ">=", ConstantNode(1.0))
        l1_5 = Conjecture.create("l1_5", chi, ">=", ConstantNode(1.5))
        l2 = Conjecture.create("l2", chi, ">=", ConstantNode(2.0))

        candidates = [l1, l1_5, l2]
        for perm in itertools.permutations(candidates):
            res = DalmatiansFilter.filter(list(perm), sample_graphs)
            assert [c.id for c in res] == ["l2"], f"Failed on perm {[c.id for c in perm]}"

    def test_pareto_envelope_pruning_and_permutation_invariance(self, sample_graphs):
        """A candidate bound that provides NO improvement to the Pareto envelope

        must be rejected regardless of evaluation order.
        Counterexample:
        - bA: chi <= Delta + 1 (evals to [2, 3, 4, 5])
        - bE: chi <= omega + 1 (evals to [3, 3, 5, 3])
        - bLoose: chi <= 4.0 (evals to [4, 4, 4, 4])
        bLoose does not improve the envelope [2, 3, 4, 3] anywhere.
        If presented last [bA, bE, bLoose], bLoose is rejected -> ['bA', 'bE'].
        If presented first [bLoose, bA, bE], bLoose must also be pruned -> ['bA', 'bE'].
        """
        chi = InvariantNode("chromatic_number")
        delta = InvariantNode("max_degree")
        omega = InvariantNode("clique_number")
        one = ConstantNode(1.0)

        bA = Conjecture.create("bA", chi, "<=", BinaryOpNode("+", delta, one))
        bE = Conjecture.create("bE", chi, "<=", BinaryOpNode("+", omega, one))
        bLoose = Conjecture.create("bLoose", chi, "<=", ConstantNode(4.0))

        candidates = [bA, bE, bLoose]
        for perm in itertools.permutations(candidates):
            res = DalmatiansFilter.filter(list(perm), sample_graphs)
            res_ids = set(c.id for c in res)
            assert res_ids == {"bA", "bE"}, (
                f"Permutation {[c.id for c in perm]} failed: got {res_ids}, expected {{'bA', 'bE'}}"
            )

    def test_dominating_bound_evicts_inferior_bound_across_all_permutations(self, sample_graphs):
        """A strictly dominating candidate bound must be admitted and evict the inferior bound

        across all permutations, even if it does not strictly improve the global envelope
        on instances where an independent tight bound already ties or wins.
        """
        chi = InvariantNode("chromatic_number")
        delta = InvariantNode("max_degree")
        omega = InvariantNode("clique_number")
        order = InvariantNode("order")
        one = ConstantNode(1.0)

        bA = Conjecture.create("bA", chi, "<=", BinaryOpNode("+", delta, one))
        bB = Conjecture.create("bB", chi, "<=", BinaryOpNode("+", omega, one))
        bC = Conjecture.create("bC", chi, "<=", order)

        candidates = [bA, bB, bC]
        for perm in itertools.permutations(candidates):
            res = DalmatiansFilter.filter(list(perm), sample_graphs)
            res_ids = set(c.id for c in res)
            assert res_ids == {"bA", "bB"}, (
                f"Permutation {[c.id for c in perm]} failed: got {res_ids}, expected {{'bA', 'bB'}}"
            )

    def test_dominating_lower_bound_evicts_inferior_bound_across_all_permutations(self, sample_graphs):
        """Symmetric test for lower bounds: strictly dominating candidate must be admitted."""
        order = InvariantNode("order")
        chi = InvariantNode("chromatic_number")
        omega = InvariantNode("clique_number")

        lA = Conjecture.create("lA", order, ">=", chi)
        lB = Conjecture.create("lB", order, ">=", omega)
        lC = Conjecture.create("lC", order, ">=", ConstantNode(1.0))

        candidates = [lA, lB, lC]
        for perm in itertools.permutations(candidates):
            res = DalmatiansFilter.filter(list(perm), sample_graphs)
            res_ids = set(c.id for c in res)
            assert "lC" not in res_ids, f"Permutation {[c.id for c in perm]} retained dominated lC"



class TestEchoFilterAdversarial:
    """Stress tests EchoFilter across permutations, symmetries, transitivity, and cycles."""

    def test_intra_batch_duplicates(self):
        """Exact duplicates within the batch must retain only the first instance."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        c1 = Conjecture.create("c1", A, "<=", B)
        c2 = Conjecture.create("c2", A, "<=", B)

        res = EchoFilter.filter([c1, c2])
        assert len(res) == 1 and res[0].id == "c1"

    def test_inverted_relation_pairs(self):
        """Inverted relation pairs (A <= B and B >= A) must retain only one instance."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        c_le = Conjecture.create("le", A, "<=", B)
        c_ge = Conjecture.create("ge", B, ">=", A)

        res1 = EchoFilter.filter([c_le, c_ge])
        assert len(res1) == 1 and res1[0].id == "le"

        res2 = EchoFilter.filter([c_ge, c_le])
        assert len(res2) == 1 and res2[0].id == "ge"

    def test_transitive_3_chain_permutations(self):
        """All 6 permutations of [A <= B, B <= C, A <= C] must yield only {A <= B, B <= C}."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")

        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BC = Conjecture.create("BC", B, "<=", C)
        c_AC = Conjecture.create("AC", A, "<=", C)

        for perm in itertools.permutations([c_AB, c_BC, c_AC]):
            res = EchoFilter.filter(list(perm))
            res_ids = set(c.id for c in res)
            assert res_ids == {"AB", "BC"}, f"Permutation {[c.id for c in perm]} failed: got {res_ids}"

    def test_transitive_4_chain_permutations(self):
        """All 720 permutations of a 4-element chain with 3 shortcuts must yield only the 3 base edges."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")
        D = InvariantNode("size")

        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BC = Conjecture.create("BC", B, "<=", C)
        c_CD = Conjecture.create("CD", C, "<=", D)
        c_AC = Conjecture.create("AC", A, "<=", C)
        c_BD = Conjecture.create("BD", B, "<=", D)
        c_AD = Conjecture.create("AD", A, "<=", D)

        candidates = [c_AB, c_BC, c_CD, c_AC, c_BD, c_AD]
        for perm in itertools.permutations(candidates):
            res = EchoFilter.filter(list(perm))
            res_ids = set(c.id for c in res)
            assert res_ids == {"AB", "BC", "CD"}, f"Permutation {[c.id for c in perm]} failed: got {res_ids}"

    def test_cycle_with_outgoing_branch_preservation(self):
        """When nodes are in a cycle (A <= B and B <= A), outgoing independent bounds

        (e.g. B <= C) must NOT be erroneously deleted.
        """
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")

        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BA = Conjecture.create("BA", B, "<=", A)
        c_BC = Conjecture.create("BC", B, "<=", C)

        res = EchoFilter.filter([c_AB, c_BA, c_BC])
        res_ids = set(c.id for c in res)
        assert "BC" in res_ids, f"Independent bound BC was erroneously deleted: got {res_ids}"

    def test_bridge_preservation_across_component_cycle_permutations(self):
        """When two component equivalence classes (cycles) are connected by parallel bridges,

        dynamic transitive reduction must never eliminate ALL bridges connecting the components.
        Across all 720 permutations of [AB, BA, BC, CD, DC, AD], at least one of {BC, AD} must survive.
        """
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")
        D = InvariantNode("size")

        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BA = Conjecture.create("BA", B, "<=", A)
        c_BC = Conjecture.create("BC", B, "<=", C)
        c_CD = Conjecture.create("CD", C, "<=", D)
        c_DC = Conjecture.create("DC", D, "<=", C)
        c_AD = Conjecture.create("AD", A, "<=", D)

        edges = [c_AB, c_BA, c_BC, c_CD, c_DC, c_AD]
        for perm in itertools.permutations(edges):
            res = EchoFilter.filter(list(perm))
            res_ids = set(c.id for c in res)
            assert bool(res_ids.intersection({"BC", "AD"})), (
                f"Both bridges severed in permutation {[c.id for c in perm]}: got {res_ids}"
            )

