"""Empirical Adversarial Challenge Suite for Milestone 1 Conjecturing & Filtration Engine.

Stresses:
1. Conjecture Grammar: Generation across diverse graph families (Erdos-Renyi, Barabasi-Albert, Watts-Strogatz, extremal atlas).
2. 2D Convex Hull Generator: Andrews Monotone Chain facet synthesis across standard and edge-case invariant spaces.
3. TrivialityFilter: Stress tests against algebraic tautologies, contradictions, strict inequalities, and domain trivialities.
4. DalmatiansFilter: Stress tests Fajtlowicz sharpness heuristic under non-monotonic arrival, intermediate dominated bounds, and lower-bound cascades.
5. EchoFilter: Stress tests inequality DAG transitivity and constant relaxation both cross-theorem and intra-batch.
"""

from __future__ import annotations

import random
from typing import List, Tuple
import networkx as nx
import numpy as np
import pytest
import sympy as sp

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.conjecturing.filters import (
    ConjectureFilterPipeline,
    DalmatiansFilter,
    EchoFilter,
    TrivialityFilter,
)
from autonomous_math.conjecturing.generator import (
    ConjectureGenerator,
    _default_sample_graphs,
)
from autonomous_math.conjecturing.grammar import (
    ExpressionGenerator,
    GrammarConfig,
    validate_conjecture,
    validate_expression,
)


def _generate_diverse_graph_corpus(seed: int = 42) -> List[nx.Graph]:
    """Generates an adversarial test atlas combining extremal graphs and random models."""
    rng = random.Random(seed)
    graphs: List[nx.Graph] = []

    # 1. Deterministic extremal graphs
    graphs.extend([
        nx.cycle_graph(3),
        nx.cycle_graph(5),
        nx.cycle_graph(7),
        nx.path_graph(4),
        nx.star_graph(5),
        nx.complete_graph(1),
        nx.complete_graph(4),
        nx.complete_graph(6),
        nx.complete_bipartite_graph(2, 3),
        nx.complete_bipartite_graph(3, 3),
        nx.petersen_graph(),
        nx.wheel_graph(6),
    ])

    # 2. Random graph models (connected)
    for n in [6, 8, 10]:
        g_er = nx.erdos_renyi_graph(n, 0.5, seed=rng.randint(0, 10000))
        if nx.is_connected(g_er):
            graphs.append(g_er)
        graphs.append(nx.barabasi_albert_graph(n, 2, seed=rng.randint(0, 10000)))
        graphs.append(nx.watts_strogatz_graph(n, 4, 0.3, seed=rng.randint(0, 10000)))

    # Ensure all graphs are non-empty and simple
    valid_graphs = [g for g in graphs if g.number_of_nodes() > 0]
    return valid_graphs


# =====================================================================
# 1. GRAMMAR & GENERATOR STRESS TESTS
# =====================================================================


class TestGrammarAndGeneratorStress:
    """Stress tests expression generation and convex hull bounds across diverse graphs."""

    def test_adversarial_independence_number_disconnected_bipartite_crash(self):
        """Verifies compute_independence_number succeeds on disconnected bipartite graphs without crashing."""
        from autonomous_math.core.invariants import GraphInvariantEvaluator
        g_disc = nx.disjoint_union(nx.path_graph(2), nx.path_graph(2))
        assert nx.is_bipartite(g_disc) and not nx.is_connected(g_disc)

        val = GraphInvariantEvaluator.evaluate_single(g_disc, "independence_number")
        assert val == 2

    def test_expression_generation_depth_and_complexity(self):
        """Verifies that generated AST expressions obey depth and complexity invariants."""
        cfg = GrammarConfig(max_depth=2, max_complexity=4)
        gen = ExpressionGenerator(cfg)
        exprs = gen.generate()
        assert len(exprs) > 50

        for e in exprs:
            assert e.depth <= 2
            assert e.complexity <= 4
            errs = validate_expression(e, cfg)
            assert len(errs) == 0, f"Expression {e} failed validation: {errs}"

    def test_conjecture_generation_across_diverse_graph_corpus(self):
        """Generates candidate conjectures and evaluates them across a diverse graph corpus."""
        corpus = _generate_diverse_graph_corpus(seed=123)
        gen = ConjectureGenerator()
        candidates = gen.generate_exhaustive(
            max_depth=2,
            limit=20,
            target_invariants=["chromatic_number", "clique_number", "max_degree"],
        )
        assert len(candidates) == 20

        for c in candidates:
            # Each candidate must evaluate without unhandled exceptions on all graphs
            for g in corpus:
                holds, l, r = c.evaluate(g)
                assert isinstance(holds, bool)
                assert isinstance(l, float)
                assert isinstance(r, float)

    def test_convex_hull_parametric_generator_multiple_spaces(self):
        """Verifies 2D convex hull extremal bound discovery across standard invariant spaces."""
        corpus = _default_sample_graphs()
        gen = ConjectureGenerator()

        spaces = [
            ("chromatic_number", "max_degree"),
            ("clique_number", "chromatic_number"),
            ("spectral_radius", "max_degree"),
            ("size", "order"),
        ]

        for target_y, target_x in spaces:
            conjs = gen.generate_parametric_bounds(
                target_y=target_y, target_x=target_x, graphs=corpus, relations=["<="]
            )
            assert len(conjs) > 0, f"No bounds generated for {target_y} vs {target_x}"

            # Verify that each generated bound holds on all sample graphs used to form the hull
            for c in conjs:
                for g in corpus:
                    holds, l, r = c.evaluate(g)
                    assert holds, f"Convex hull bound {c.statement} violated on graph {g} (lhs={l}, rhs={r})"

    def test_convex_hull_edge_cases(self):
        """Verifies convex hull behavior on degenerate inputs (empty graphs, collinear, single points)."""
        gen = ConjectureGenerator()

        # Degenerate: Single point
        single = [nx.cycle_graph(5)]
        conjs_single = gen.generate_parametric_bounds(graphs=single)
        assert len(conjs_single) == 0, "Single point dataset must produce 0 linear facets"

        # Degenerate: Identical points across multiple graphs
        identical = [nx.path_graph(3), nx.path_graph(3), nx.path_graph(3)]
        conjs_ident = gen.generate_parametric_bounds(target_y="order", target_x="order", graphs=identical)
        assert len(conjs_ident) == 0, "Zero-variance dataset must produce 0 linear facets"


# =====================================================================
# 2. TRIVIALITY FILTER ADVERSARIAL STRESS TESTS
# =====================================================================


class TestTrivialityFilterAdversarial:
    """Stress tests TrivialityFilter with tautologies, contradictions, and non-trivial bounds."""

    @pytest.mark.parametrize(
        "label,lhs,rel,rhs",
        [
            ("x <= x", InvariantNode("order"), "<=", InvariantNode("order")),
            ("x >= x", InvariantNode("order"), ">=", InvariantNode("order")),
            ("x == x", InvariantNode("order"), "==", InvariantNode("order")),
            ("x <= x + 1", InvariantNode("order"), "<=", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0))),
            ("x <= x + 0.5", InvariantNode("order"), "<=", BinaryOpNode("+", InvariantNode("order"), ConstantNode(0.5))),
            ("x + 1 >= x", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0)), ">=", InvariantNode("order")),
            ("x < x + 1", InvariantNode("order"), "<", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0))),
            ("x > x - 1", InvariantNode("order"), ">", BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))),
            ("x + y >= x", BinaryOpNode("+", InvariantNode("order"), InvariantNode("size")), ">=", InvariantNode("order")),
            ("x <= x + y", InvariantNode("order"), "<=", BinaryOpNode("+", InvariantNode("order"), InvariantNode("size"))),
            ("x - y <= x", BinaryOpNode("-", InvariantNode("order"), InvariantNode("size")), "<=", InvariantNode("order")),
            ("2*x >= x", BinaryOpNode("*", ConstantNode(2.0), InvariantNode("order")), ">=", InvariantNode("order")),
            ("x / 2 <= x", BinaryOpNode("/", InvariantNode("order"), ConstantNode(2.0)), "<=", InvariantNode("order")),
            ("1 <= 2", ConstantNode(1.0), "<=", ConstantNode(2.0)),
            ("x >= 0", InvariantNode("order"), ">=", ConstantNode(0.0)),
            ("x >= -5", InvariantNode("order"), ">=", ConstantNode(-5.0)),
        ],
    )
    def test_tautologies_are_rejected(self, label, lhs, rel, rhs):
        """Verifies that algebraic and domain tautologies are strictly rejected by TrivialityFilter."""
        conj = Conjecture.create(id=f"taut_{label}", lhs=lhs, rel=rel, rhs=rhs)
        assert TrivialityFilter.is_trivial(conj) is True, f"Tautology '{label}' was NOT rejected by TrivialityFilter!"

    @pytest.mark.parametrize(
        "label,lhs,rel,rhs",
        [
            ("x < x", InvariantNode("order"), "<", InvariantNode("order")),
            ("x > x", InvariantNode("order"), ">", InvariantNode("order")),
            ("x <= x - 1", InvariantNode("order"), "<=", BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))),
            ("x >= x + 1", InvariantNode("order"), ">=", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0))),
            ("x + 1 <= x", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0)), "<=", InvariantNode("order")),
            ("x + 1 < x", BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0)), "<", InvariantNode("order")),
            ("x - 1 > x", BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0)), ">", InvariantNode("order")),
            ("2 <= 1", ConstantNode(2.0), "<=", ConstantNode(1.0)),
        ],
    )
    def test_contradictions_are_rejected(self, label, lhs, rel, rhs):
        """Verifies that algebraic contradictions are strictly rejected by TrivialityFilter."""
        conj = Conjecture.create(id=f"contra_{label}", lhs=lhs, rel=rel, rhs=rhs)
        assert TrivialityFilter.is_trivial(conj) is True, f"Contradiction '{label}' was NOT rejected by TrivialityFilter!"

    def test_valid_mathematical_conjectures_survive(self):
        """Verifies that legitimate, non-trivial bounds are preserved."""
        non_trivial = [
            Conjecture.create(
                id="brooks",
                lhs=InvariantNode("chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            ),
            Conjecture.create(
                id="clique_bound",
                lhs=InvariantNode("clique_number"),
                rel="<=",
                rhs=InvariantNode("chromatic_number"),
            ),
            Conjecture.create(
                id="wilf",
                lhs=InvariantNode("chromatic_number"),
                rel="<=",
                rhs=BinaryOpNode("+", InvariantNode("spectral_radius"), ConstantNode(1.0)),
            ),
        ]

        filtered = TrivialityFilter.filter(non_trivial)
        assert len(filtered) == 3, "Valid non-trivial conjectures were erroneously dropped!"


# =====================================================================
# 3. ECHO FILTER TESTS (INTER-THEOREM & INTRA-BATCH)
# =====================================================================


class TestEchoFilterSubsumption:
    """Tests EchoFilter transitive redundancy and constant relaxation rejection."""

    def test_echo_rejects_transitive_redundancy_with_existing_theorems(self):
        """Verifies A <= B and B <= C implies A <= C is rejected when existing_theorems is populated."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")

        t_AB = Conjecture.create("t_AB", A, "<=", B)
        t_BC = Conjecture.create("t_BC", B, "<=", C)
        cand_AC = Conjecture.create("cand_AC", A, "<=", C)

        filtered = EchoFilter.filter([cand_AC], existing_theorems=[t_AB, t_BC])
        assert len(filtered) == 0, "Transitive bound A <= C was not rejected given existing theorems A <= B and B <= C!"

    def test_echo_rejects_lower_bound_transitive_redundancy_with_existing_theorems(self):
        """Verifies A >= B and B >= C implies A >= C is rejected when existing_theorems is populated."""
        A = InvariantNode("order")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("clique_number")

        t_AB = Conjecture.create("t_AB", A, ">=", B)
        t_BC = Conjecture.create("t_BC", B, ">=", C)
        cand_AC = Conjecture.create("cand_AC", A, ">=", C)

        filtered = EchoFilter.filter([cand_AC], existing_theorems=[t_AB, t_BC])
        assert len(filtered) == 0, "Transitive lower bound A >= C was not rejected given A >= B and B >= C!"

    def test_echo_rejects_constant_relaxation_with_existing_theorems(self):
        """Verifies A <= B + 5 is rejected when A <= B + 1 is an existing theorem."""
        A = InvariantNode("chromatic_number")
        B = InvariantNode("max_degree")

        t_tight = Conjecture.create("t_tight", A, "<=", BinaryOpNode("+", B, ConstantNode(1.0)))
        cand_loose = Conjecture.create("cand_loose", A, "<=", BinaryOpNode("+", B, ConstantNode(5.0)))

        filtered = EchoFilter.filter([cand_loose], existing_theorems=[t_tight])
        assert len(filtered) == 0, "Constant relaxation A <= B + 5 was not rejected given A <= B + 1!"

    def test_echo_rejects_lower_bound_constant_relaxation_with_existing_theorems(self):
        """Verifies A >= B - 5 is rejected when A >= B - 1 is an existing theorem."""
        A = InvariantNode("order")
        B = InvariantNode("chromatic_number")

        t_tight = Conjecture.create("t_tight", A, ">=", BinaryOpNode("-", B, ConstantNode(1.0)))
        cand_loose = Conjecture.create("cand_loose", A, ">=", BinaryOpNode("-", B, ConstantNode(5.0)))

        filtered = EchoFilter.filter([cand_loose], existing_theorems=[t_tight])
        assert len(filtered) == 0, "Constant relaxation A >= B - 5 was not rejected given A >= B - 1!"

    def test_adversarial_echo_intra_batch_redundancy_leak(self):
        """CHALLENGE TEST: Demonstrates that EchoFilter leaks transitive redundancies within candidate batches.

        When existing_theorems is None, EchoFilter processes [A <= B, B <= C, A <= C] sequentially.
        Because EchoFilter fails to accumulate accepted candidates into its DAG, A <= C leaks through!
        """
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")

        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BC = Conjecture.create("BC", B, "<=", C)
        c_AC = Conjecture.create("AC", A, "<=", C)

        result = EchoFilter.filter([c_AB, c_BC, c_AC], existing_theorems=None)
        accepted_ids = [c.id for c in result]

        # Verifies that EchoFilter eliminates transitive redundancies within candidate batches
        print(f"\n[EchoFilter Intra-Batch Transitivity] Accepted: {accepted_ids}")
        assert "AC" not in accepted_ids
        assert accepted_ids == ["AB", "BC"]

    def test_adversarial_echo_intra_batch_constant_relaxation_leak(self):
        """Verifies that EchoFilter eliminates constant relaxations within candidate batches."""
        A = InvariantNode("chromatic_number")
        B = InvariantNode("max_degree")

        c_tight = Conjecture.create("tight", A, "<=", BinaryOpNode("+", B, ConstantNode(1.0)))
        c_loose = Conjecture.create("loose", A, "<=", BinaryOpNode("+", B, ConstantNode(5.0)))

        result = EchoFilter.filter([c_tight, c_loose], existing_theorems=None)
        accepted_ids = [c.id for c in result]

        print(f"\n[EchoFilter Intra-Batch Relaxation] Accepted: {accepted_ids}")
        assert "loose" not in accepted_ids
        assert accepted_ids == ["tight"]


# =====================================================================
# 4. DALMATIANS FILTER ADVERSARIAL SHARPNESS TESTS
# =====================================================================


class TestDalmatiansFilterAdversarial:
    """Stress tests DalmatiansFilter for strict informativeness and sharpness."""

    def test_dalmatians_accepts_first_valid_bound(self):
        """Verifies that the first valid bound is accepted."""
        g = nx.path_graph(4)
        c = Conjecture.create("b1", InvariantNode("chromatic_number"), "<=", ConstantNode(5.0))
        res = DalmatiansFilter.filter([c], [g])
        assert len(res) == 1

    def test_dalmatians_rejects_strictly_weaker_bound_after_tight_bound(self):
        """Verifies that when a tight bound arrives first, a weaker bound is rejected."""
        g = nx.path_graph(4)
        b_tight = Conjecture.create("tight", InvariantNode("chromatic_number"), "<=", ConstantNode(2.0))
        b_loose = Conjecture.create("loose", InvariantNode("chromatic_number"), "<=", ConstantNode(5.0))

        res = DalmatiansFilter.filter([b_tight, b_loose], [g])
        assert [c.id for c in res] == ["tight"]

    def test_adversarial_dalmatians_admits_uninformative_dominated_bounds_in_cascade(self):
        """Verifies that DalmatiansFilter rejects dominated bound b3 and prunes b1."""
        g1 = nx.path_graph(3)
        g2 = nx.path_graph(4)

        b1 = Conjecture.create("b1", InvariantNode("chromatic_number"), "<=", ConstantNode(10.0))
        b2 = Conjecture.create("b2", InvariantNode("chromatic_number"), "<=", ConstantNode(2.0))
        b3 = Conjecture.create("b3", InvariantNode("chromatic_number"), "<=", ConstantNode(5.0))

        res = DalmatiansFilter.filter([b1, b2, b3], [g1, g2])
        accepted_ids = [c.id for c in res]

        print(f"\n[DalmatiansFilter Dominance Leak] Accepted: {accepted_ids}")
        assert "b3" not in accepted_ids
        assert accepted_ids == ["b2"]

    def test_adversarial_dalmatians_lower_bound_cascade_leak(self):
        """Verifies that DalmatiansFilter rejects dominated lower bound b_4 and prunes b_1."""
        g = nx.complete_graph(6)

        b_1 = Conjecture.create("b_1", InvariantNode("chromatic_number"), ">=", ConstantNode(1.0))
        b_6 = Conjecture.create("b_6", InvariantNode("chromatic_number"), ">=", ConstantNode(6.0))
        b_4 = Conjecture.create("b_4", InvariantNode("chromatic_number"), ">=", ConstantNode(4.0))

        res = DalmatiansFilter.filter([b_1, b_6, b_4], [g])
        accepted_ids = [c.id for c in res]

        print(f"\n[DalmatiansFilter Lower-Bound Leak] Accepted: {accepted_ids}")
        assert "b_4" not in accepted_ids
        assert accepted_ids == ["b_6"]

    def test_adversarial_pipeline_leaks_dominated_bounds_and_relaxations(self):
        """Verifies that full pipeline weeds out dominated bounds and relaxations."""
        g1 = nx.path_graph(4)
        g2 = nx.cycle_graph(5)
        g3 = nx.star_graph(5)

        chi = InvariantNode("chromatic_number")
        Delta = InvariantNode("max_degree")

        b_loose = Conjecture.create("b_loose", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(10.0)))
        b_tight = Conjecture.create("b_tight", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(1.0)))
        b_mid = Conjecture.create("b_mid", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(5.0)))

        pipeline = ConjectureFilterPipeline(test_instances=[g1, g2, g3], existing_theorems=[])
        res = pipeline.run([b_loose, b_tight, b_mid])
        surviving_ids = [c.id for c in res]

        print(f"\n[Pipeline Full Leak] Surviving: {surviving_ids}")
        assert surviving_ids == ["b_tight"]


if __name__ == "__main__":
    pytest.main(["-v", __file__])
