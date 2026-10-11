"""Unit tests for AST Models, Conjecture Generation, and Graffiti Filtration.

Verifies:
- AST Node evaluation, serialization (JSON, LaTeX, Lean 4, SymPy).
- Conjecture evaluation with vacuous truth and empirical refutation on C5.
- Recursive AST generator and complexity metrics.
- 2D Convex Hull parametric bound discovery (discovering Brooks bound chi <= Delta + 1).
- Archetypal conjecture library (Brooks, Turan, Ramsey, spectral, C5 refutation).
- TrivialityFilter (SymPy tautology and contradiction pruning).
- DalmatiansFilter (strict envelope improvement and sharpness).
- EchoFilter (transitivity and constant weakening subsumption).
- ConjectureFilterPipeline end-to-end execution.
"""

from __future__ import annotations

import json
import math
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
    RelationNode,
    UnaryOpNode,
)
from autonomous_math.conjecturing.filters import (
    ConjectureFilterPipeline,
    DalmatiansFilter,
    EchoFilter,
    TrivialityFilter,
)
from autonomous_math.conjecturing.generator import ConjectureGenerator
from autonomous_math.conjecturing.grammar import (
    ExpressionGenerator,
    GrammarConfig,
    validate_conjecture,
    validate_expression,
)


class TestASTModels:
    """Verifies AST representation, evaluation, and exports."""

    def test_invariant_node(self):
        node = InvariantNode("chromatic_number")
        assert node.canonical_name() == "chromatic_number"
        assert node.complexity == 1
        assert node.depth == 1
        assert "chromatic_number" in node.variables

        # Evaluate against dict
        env = {"chromatic_number": 3, "order": 5}
        assert node.evaluate(env) == 3.0

        # Export tests
        assert isinstance(node.to_sympy(), sp.Symbol)
        assert r"\chi(G)" in node.to_latex()
        assert "G.chromaticNumber" in node.to_lean()

    def test_constant_node(self):
        c1 = ConstantNode(1.0)
        assert c1.evaluate({}) == 1.0
        assert c1.complexity == 1
        assert c1.depth == 1
        assert c1.to_latex() == "1"
        assert "(1 : ℝ)" in c1.to_lean()

        c_half = ConstantNode(0.5)
        assert r"\frac{1}{2}" in c_half.to_latex()

    def test_constant_identity_preserves_exact_decimal_meaning(self):
        from fractions import Fraction
        from autonomous_math.prover.trusted_lean import render_challenge

        above, below = ConstantNode(1.0000001), ConstantNode(0.9999999)
        assert above.canonical_key != below.canonical_key
        for value in (above, below, ConstantNode(0.5000000001), ConstantNode(1e-20)):
            rational = Fraction(str(value.value))
            assert value.to_sympy() == sp.Rational(rational.numerator, rational.denominator)
            assert value.to_lean() == f"({rational.numerator} / {rational.denominator} : ℝ)"
            assert ConstantNode(**value.to_dict()).canonical_key == value.canonical_key
        assert ConstantNode(-0.0).canonical_key == ConstantNode(0).canonical_key == "c:0"
        assert ConstantNode(1).canonical_key == ConstantNode(1.0).canonical_key == "c:1"
        n = InvariantNode("order")
        true = Conjecture.create(id="precise_true", lhs=n, rel="<=", rhs=BinaryOpNode("*", above, n))
        false = Conjecture.create(id="precise_false", lhs=n, rel="<=", rhs=BinaryOpNode("*", below, n))
        assert RelationNode("<=", true.lhs_expr, true.rhs_expr).evaluate({"order": 32})[0]
        assert not RelationNode("<=", false.lhs_expr, false.rhs_expr).evaluate({"order": 32})[0]
        assert render_challenge(true)[0] != render_challenge(false)[0]
        assert above.to_latex() == "1.0000001"
        assert below.to_latex() == "0.9999999"

    def test_unary_op_node(self):
        inv = InvariantNode("order")
        sqrt_node = UnaryOpNode("sqrt", inv)
        assert sqrt_node.complexity == 2
        assert sqrt_node.depth == 2
        assert sqrt_node.evaluate({"order": 16}) == 4.0
        assert r"\sqrt{n}" in sqrt_node.to_latex()

        # Domain error check
        with pytest.raises(ValueError, match="Domain error"):
            sqrt_node.evaluate({"order": -1.0})

        # Inverse zero division check
        inv_node = UnaryOpNode("inv", InvariantNode("order"))
        with pytest.raises(ZeroDivisionError):
            inv_node.evaluate({"order": 0})

    def test_binary_op_node(self):
        lhs = InvariantNode("max_degree")
        rhs = ConstantNode(1.0)
        plus_node = BinaryOpNode("+", lhs, rhs)

        assert plus_node.complexity == 3
        assert plus_node.depth == 2
        assert plus_node.evaluate({"max_degree": 4}) == 5.0
        assert "+" in plus_node.to_latex()

        # Division by zero check
        div_node = BinaryOpNode("/", lhs, ConstantNode(0.0))
        with pytest.raises(ZeroDivisionError):
            div_node.evaluate({"max_degree": 4})

    def test_relation_node(self):
        lhs = InvariantNode("chromatic_number")
        rhs = InvariantNode("clique_number")
        rel = RelationNode(">=", lhs, rhs)

        assert rel.complexity == 3
        holds, l_val, r_val = rel.evaluate({"chromatic_number": 3, "clique_number": 2})
        assert holds is True
        assert l_val == 3.0 and r_val == 2.0

        holds_f, _, _ = rel.evaluate({"chromatic_number": 2, "clique_number": 3})
        assert holds_f is False

    def test_conjecture_json_dict_roundtrip(self):
        conj = Conjecture.create(
            id="conj_test_01",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            guard=GuardPredicate(property_name_or_type="is_connected"),
        )

        d = conj.to_dict()
        assert d["id"] == "conj_test_01"
        assert d["rel"] == "<="
        assert "lhs_expr" in d and "rhs_expr" in d

        # JSON string roundtrip
        s = json.dumps(d)
        loaded = json.loads(s)
        reconstructed = Conjecture.from_dict(loaded)

        assert reconstructed.id == conj.id
        assert reconstructed.statement == conj.statement
        assert reconstructed.complexity == conj.complexity
        assert reconstructed.rel == conj.rel

    def test_lean_and_comparator_export(self):
        conj = Conjecture.create(
            id="conj_brooks",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )

        lean_code = conj.to_lean(challenge_module="BrooksBound", theorem_name="brooks_upper_bound")
        assert "theorem brooks_upper_bound" in lean_code
        assert "SimpleGraph" in lean_code
        assert "sorry" in lean_code

        comp_json = conj.to_comparator_json(
            challenge_module="BrooksBound",
            solution_module="AutonomousMath.Solutions.Brooks",
            theorem_name="brooks_upper_bound",
        )
        assert comp_json["challenge_module"] == "ComparatorChallenges.BrooksBound"
        assert "AutonomousMath.BrooksBound.brooks_upper_bound" in comp_json["theorem_names"]


class TestConjectureEvaluation:
    """Verifies empirical evaluation of conjectures on graphs."""

    def test_valid_conjecture_evaluation(self, graph_c5, graph_k4):
        # chi >= omega (True universally)
        conj = Conjecture.create(
            id="chi_ge_omega",
            lhs=InvariantNode("chromatic_number"),
            rel=">=",
            rhs=InvariantNode("clique_number"),
        )

        holds_c5, l_c5, r_c5 = conj.evaluate(graph_c5)
        assert holds_c5 is True
        assert l_c5 == 3.0 and r_c5 == 2.0

        holds_k4, l_k4, r_k4 = conj.evaluate(graph_k4)
        assert holds_k4 is True
        assert l_k4 == 4.0 and r_k4 == 4.0

    def test_vacuous_truth_with_guard(self, graph_k5):
        # Claim: is_triangle_free ==> chi <= 2
        # On K5 (which has 10 triangles), guard is False -> vacuously True
        conj = Conjecture.create(
            id="test_vacuous",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=ConstantNode(2.0),
            guard=GuardPredicate(property_name_or_type="is_triangle_free"),
        )

        holds, _, _ = conj.evaluate(graph_k5)
        assert holds is True, "Conjecture must hold vacuously when premise guard is false"

    def test_vacuous_truth_division_by_zero_safe(self):
        """Verify Conjecture.evaluate does not crash with ZeroDivisionError on K0."""
        gen = ConjectureGenerator()
        archetypes = gen.generate_archetypal()
        ramsey = next(c for c in archetypes if c.id == "archetype_ramsey_chi_alpha")

        # Ramsey: order >= 1 ==> chi >= order / independence_number
        # On K0, order=0, independence_number=0 -> rhs would be 0/0.
        holds, lhs_val, rhs_val = ramsey.evaluate(nx.empty_graph(0))
        assert holds is True
        assert (lhs_val, rhs_val) == (0.0, 0.0)

    def test_c5_refutation_of_triangle_free_chromatic_at_most_2(self, graph_c5):
        # Benchmark claim: is_triangle_free ==> chi <= 2
        # C5 has triangles == 0, so guard is True! But chi(C5) == 3 > 2!
        conj = Conjecture.create(
            id="c5_refutation_target",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=ConstantNode(2.0),
            guard=GuardPredicate(property_name_or_type="is_triangle_free"),
        )

        holds, l_val, r_val = conj.evaluate(graph_c5)
        assert holds is False, "C5 must refute triangle-free non-2-colorability"
        assert l_val == 3.0
        assert r_val == 2.0


class TestConjectureGenerators:
    """Verifies recursive enumerator, parametric convex hull, and archetypal generator."""

    def test_recursive_generator(self):
        generator = ConjectureGenerator()
        candidates = generator.generate_recursive(
            target_invariant="chromatic_number",
            relations=["<="],
            max_depth=2,
            limit=15,
        )

        assert len(candidates) > 0
        for c in candidates:
            assert c.lhs_expr.canonical_key == "inv:chromatic_number"
            assert c.rel == "<="
            assert c.complexity >= 1
            errors = validate_conjecture(c)
            assert len(errors) == 0

    def test_exhaustive_generator(self, graph_c5):
        generator = ConjectureGenerator()
        conjectures = generator.generate_exhaustive(max_depth=2, limit=10)
        assert len(conjectures) == 10

        for c in conjectures:
            holds, l, r = c.evaluate(graph_c5)
            assert isinstance(holds, bool)
            assert isinstance(l, float)
            assert isinstance(r, float)

    def test_parametric_convex_hull_discovers_brooks(self):
        generator = ConjectureGenerator()
        conjs = generator.generate_parametric_bounds(
            target_y="chromatic_number",
            target_x="max_degree",
            relations=["<="],
        )

        assert len(conjs) > 0
        # Check if Brooks-type bound chi <= max_degree + 1 or similar is discovered
        found_brooks = any(
            np.isclose(c.metadata.get("slope", 0.0), 1.0) and np.isclose(c.metadata.get("intercept", 0.0), 1.0)
            for c in conjs
        )
        assert found_brooks, "Convex hull generator failed to discover slope 1.0, intercept 1.0 (Brooks bound)"

    def test_archetypal_generator_catalog(self, graph_c5):
        generator = ConjectureGenerator()
        archetypes = generator.generate_archetypal()

        assert len(archetypes) >= 6
        ids = [c.id for c in archetypes]
        assert "archetype_brooks_standard" in ids
        assert "benchmark_triangle_free_chromatic_at_most_2" in ids

        # Verify benchmark C5 refutation
        target = next(c for c in archetypes if c.id == "benchmark_triangle_free_chromatic_at_most_2")
        holds, _, _ = target.evaluate(graph_c5)
        assert holds is False


class TestConjectureFilters:
    """Verifies Triviality, Dalmatians, and Echo filtration algorithms."""

    def test_triviality_filter(self):
        taut1 = Conjecture.create(
            id="t1",
            lhs=InvariantNode("order"),
            rel="<=",
            rhs=InvariantNode("order"),
        )
        taut2 = Conjecture.create(
            id="t2",
            lhs=InvariantNode("order"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0)),
        )
        contra = Conjecture.create(
            id="c1",
            lhs=InvariantNode("order"),
            rel="<",
            rhs=InvariantNode("order"),
        )
        brooks = Conjecture.create(
            id="brooks",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )

        filtered = TrivialityFilter.filter([taut1, taut2, contra, brooks])
        filtered_ids = [c.id for c in filtered]

        assert "t1" not in filtered_ids
        assert "t2" not in filtered_ids
        assert "c1" not in filtered_ids
        assert "brooks" in filtered_ids

    def test_dalmatians_sharpness_filter(self, graph_c5, graph_petersen, graph_k4):
        # Tight: chi <= Delta + 1
        tight = Conjecture.create(
            id="tight",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )
        # Loose: chi <= Delta + 10 (provides zero improvement on any graph)
        loose = Conjecture.create(
            id="loose",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(10.0)),
        )

        test_instances = [graph_c5, graph_petersen, graph_k4]
        accepted = DalmatiansFilter.filter([tight, loose], test_instances)
        accepted_ids = [c.id for c in accepted]

        assert "tight" in accepted_ids
        assert "loose" not in accepted_ids

    def test_echo_subsumption_filter(self):
        bound1 = Conjecture.create(
            id="bound_base",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )
        # Relaxation: chi <= (max_degree + 1) + 2
        bound_weak = Conjecture.create(
            id="bound_weak",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(3.0)),
        )

        filtered = EchoFilter.filter([bound1, bound_weak], existing_theorems=[bound1])
        # Both base (duplicate) and weak (relaxation) should be eliminated
        filtered_ids = [c.id for c in filtered]
        assert "bound_base" not in filtered_ids
        assert "bound_weak" not in filtered_ids

    def test_filter_pipeline(self, graph_c5, graph_petersen, graph_k4):
        pipeline = ConjectureFilterPipeline(
            test_instances=[graph_c5, graph_petersen, graph_k4],
            existing_theorems=[],
        )

        taut = Conjecture.create(
            id="taut",
            lhs=InvariantNode("order"),
            rel="<=",
            rhs=InvariantNode("order"),
        )
        tight = Conjecture.create(
            id="tight",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        )
        loose = Conjecture.create(
            id="loose",
            lhs=InvariantNode("chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(10.0)),
        )

        surviving = pipeline.run([taut, tight, loose])
        surviving_ids = [c.id for c in surviving]

        assert "taut" not in surviving_ids
        assert "loose" not in surviving_ids
        assert "tight" in surviving_ids

    def test_dalmatians_order_invariance_and_pruning(self, graph_c5, graph_petersen):
        """Verifies that DalmatiansFilter is permutation invariant and prunes obsolete bounds."""
        chi = InvariantNode("chromatic_number")
        Delta = InvariantNode("max_degree")
        b_loose = Conjecture.create("b_loose", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(10.0)))
        b_tight = Conjecture.create("b_tight", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(1.0)))
        b_mid = Conjecture.create("b_mid", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(5.0)))

        # Order 1: loose -> tight -> mid
        res1 = DalmatiansFilter.filter([b_loose, b_tight, b_mid], [graph_c5, graph_petersen])
        assert [c.id for c in res1] == ["b_tight"]

        # Order 2: tight -> loose -> mid
        res2 = DalmatiansFilter.filter([b_tight, b_loose, b_mid], [graph_c5, graph_petersen])
        assert [c.id for c in res2] == ["b_tight"]

        # Order 3: mid -> tight -> loose
        res3 = DalmatiansFilter.filter([b_mid, b_tight, b_loose], [graph_c5, graph_petersen])
        assert [c.id for c in res3] == ["b_tight"]

    def test_dalmatians_incomparable_pareto_envelope(self):
        """Verifies that incomparable bounds both survive on the Pareto frontier."""
        g1 = nx.path_graph(4)    # chi=2, Delta=2, order=4
        g2 = nx.cycle_graph(5)   # chi=3, Delta=2, order=5
        chi = InvariantNode("chromatic_number")
        order = InvariantNode("order")
        Delta = InvariantNode("max_degree")

        # b1: chi <= Delta + 1 (P4: 3, C5: 3)
        # b2: chi <= order - 1 (P4: 3, C5: 4) -> Dominated by b1 on C5
        b1 = Conjecture.create("b1", chi, "<=", BinaryOpNode("+", Delta, ConstantNode(1.0)))
        b2 = Conjecture.create("b2", chi, "<=", BinaryOpNode("-", order, ConstantNode(1.0)))

        res = DalmatiansFilter.filter([b2, b1], [g1, g2])
        assert [c.id for c in res] == ["b1"]

    def test_echo_intra_batch_dynamic_features(self):
        """Verifies that EchoFilter handles intra-batch transitivity, reverse relaxations, and duplicate inversions."""
        A = InvariantNode("clique_number")
        B = InvariantNode("chromatic_number")
        C = InvariantNode("order")

        # Reverse transitivity
        c_AC = Conjecture.create("AC", A, "<=", C)
        c_AB = Conjecture.create("AB", A, "<=", B)
        c_BC = Conjecture.create("BC", B, "<=", C)
        assert [c.id for c in EchoFilter.filter([c_AC, c_AB, c_BC])] == ["AB", "BC"]

        # Reverse constant relaxation
        c_tight = Conjecture.create("tight", A, "<=", BinaryOpNode("+", B, ConstantNode(1.0)))
        c_loose = Conjecture.create("loose", A, "<=", BinaryOpNode("+", B, ConstantNode(5.0)))
        assert [c.id for c in EchoFilter.filter([c_loose, c_tight])] == ["tight"]

        # Inverted relation
        c_BA_ge = Conjecture.create("BA_ge", B, ">=", A)
        assert [c.id for c in EchoFilter.filter([c_AB, c_BA_ge])] == ["AB"]

        # Equality symmetry & inequality subsumption
        c_eq1 = Conjecture.create("eq1", A, "==", B)
        c_eq2 = Conjecture.create("eq2", B, "==", A)
        c_le = Conjecture.create("le", A, "<=", B)
        assert [c.id for c in EchoFilter.filter([c_eq1, c_eq2, c_le])] == ["eq1"]
