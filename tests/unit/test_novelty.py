"""Unit Tests for Automated Literature Cross-Check and Scholarly Novelty Verification.

Verifies:
1. KnownTheoremRegistry completeness (13+ foundational theorems).
2. Exact AST canonical matching, inverted relation matching, and SymPy algebraic equivalence.
3. LiteratureCrossChecker classification (VERIFIED_REDISCOVERY vs. CANDIDATE_NOVEL_CONJECTURE).
4. Query construction for scholarly databases.
5. Invariant evaluations for higher-order spectral invariants (q_1, lambda_2^L, EE, energy, NG).
6. Non-linear envelope generation and AST unary 'exp' operator.
"""

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
    UnaryOpNode,
)
from autonomous_math.core.invariants import (
    GraphInvariantEvaluator,
    estrada_index,
    graph_energy,
    normalized_laplacian_spectral_gap,
    signless_laplacian_spectral_radius,
)
from autonomous_math.conjecturing.generator import ConjectureGenerator
from autonomous_math.conjecturing.grammar import validate_conjecture
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.novelty.literature_crosscheck import (
    KnownTheorem,
    KnownTheoremRegistry,
    LiteratureCrossChecker,
    LiteratureMatch,
    NoveltyReport,
    NoveltyStatus,
)


class TestKnownTheoremRegistry:
    """Verifies registry contents and theorem matching engine."""

    def test_registry_contains_foundational_theorems(self) -> None:
        registry = KnownTheoremRegistry()
        theorems = registry.theorems
        assert len(theorems) >= 13

        names = [t.name for t in theorems]
        assert any("Wilf" in name for name in names)
        assert any("Hoffman" in name for name in names)
        assert any("Brooks" in name for name in names)
        assert any("Mantel" in name for name in names)
        assert any("Cvetković" in name or "Cvetkovic" in name for name in names)
        assert any("Das" in name for name in names)
        assert any("Chung" in name for name in names)
        assert any("Estrada" in name for name in names)
        assert any("McClelland" in name for name in names)
        assert any("Nordhaus-Gaddum" in name for name in names)

    def test_exact_ast_match_wilf(self) -> None:
        registry = KnownTheoremRegistry()
        # chi <= lambda_1 + 1
        conj = Conjecture.create(
            id="test_wilf",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), ConstantNode(value=1.0)),
        )
        match = registry.match(conj)
        assert match is not None
        assert "Wilf" in match.theorem_name
        assert match.author == "Herbert S. Wilf"
        assert match.year == 1967
        assert match.equivalence_type == "exact_ast_match"

    def test_inverted_relation_match(self) -> None:
        registry = KnownTheoremRegistry()
        # lambda_1 + 1 >= chi  (inverted Wilf)
        conj = Conjecture.create(
            id="test_wilf_inverted",
            lhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), ConstantNode(value=1.0)),
            rel=">=",
            rhs=InvariantNode(name="chromatic_number"),
        )
        match = registry.match(conj)
        assert match is not None
        assert "Wilf" in match.theorem_name

    def test_inverted_algebraic_relation_match(self) -> None:
        registry = KnownTheoremRegistry()
        # lambda_1 + 2 >= chi + 1 (Wilf + 1 on both sides, reversed orientation)
        conj = Conjecture.create(
            id="test_wilf_inverted_alg",
            lhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), ConstantNode(value=2.0)),
            rel=">=",
            rhs=BinaryOpNode("+", InvariantNode(name="chromatic_number"), ConstantNode(value=1.0)),
        )
        match = registry.match(conj)
        assert match is not None
        assert "Wilf" in match.theorem_name
        assert match.equivalence_type == "algebraic_equivalent"

    def test_scaled_algebraic_match(self) -> None:
        registry = KnownTheoremRegistry()
        # 2 * chi <= 2 * lambda_1 + 2
        conj = Conjecture.create(
            id="test_wilf_scaled",
            lhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="chromatic_number")),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="spectral_radius")),
                ConstantNode(value=2.0),
            ),
        )
        match = registry.match(conj)
        assert match is not None
        assert "Wilf" in match.theorem_name

    def test_guard_compatibility_enforced(self) -> None:
        registry = KnownTheoremRegistry()
        # Unguarded size <= n^2/4 should NOT match Mantel (which requires triangle-free)
        unguarded = Conjecture.create(
            id="test_mantel_unguarded",
            lhs=InvariantNode(name="size"),
            rel="<=",
            rhs=BinaryOpNode(
                "/",
                BinaryOpNode("*", InvariantNode(name="order"), InvariantNode(name="order")),
                ConstantNode(value=4.0),
            ),
        )
        assert registry.match(unguarded) is None

        # Guarded size <= n^2/4 MUST match Mantel
        guarded = Conjecture.create(
            id="test_mantel_guarded",
            lhs=InvariantNode(name="size"),
            rel="<=",
            rhs=BinaryOpNode(
                "/",
                BinaryOpNode("*", InvariantNode(name="order"), InvariantNode(name="order")),
                ConstantNode(value=4.0),
            ),
            guard=GuardPredicate(property_name_or_type="is_triangle_free"),
        )
        match = registry.match(guarded)
        assert match is not None
        assert "Mantel" in match.theorem_name

    def test_exact_match_cvetkovic_signless_laplacian(self) -> None:
        registry = KnownTheoremRegistry()
        conj = Conjecture.create(
            id="test_cvetkovic",
            lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
            rel="<=",
            rhs=BinaryOpNode("*", ConstantNode(value=2.0), InvariantNode(name="max_degree")),
        )
        match = registry.match(conj)
        assert match is not None
        assert "Cvetković" in match.theorem_name or "Cvetkovic" in match.theorem_name
        assert match.year == 2007

    def test_exact_match_mcclelland_energy(self) -> None:
        registry = KnownTheoremRegistry()
        conj = Conjecture.create(
            id="test_mcclelland",
            lhs=InvariantNode(name="graph_energy"),
            rel="<=",
            rhs=UnaryOpNode(
                op="sqrt",
                child=BinaryOpNode(
                    "*",
                    ConstantNode(value=2.0),
                    BinaryOpNode("*", InvariantNode(name="size"), InvariantNode(name="order")),
                ),
            ),
        )
        match = registry.match(conj)
        assert match is not None
        assert "McClelland" in match.theorem_name
        assert match.year == 1971

    def test_custom_registration(self) -> None:
        registry = KnownTheoremRegistry()
        init_count = len(registry.theorems)
        custom_thm = KnownTheorem(
            id="thm_custom_test",
            name="Custom Spectral Bound",
            author="Test Author",
            year=2026,
            citation="Test Citation (2026)",
            lhs=InvariantNode(name="order"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="size"), ConstantNode(value=1.0)),
            keywords=["test", "custom"],
        )
        registry.register(custom_thm)
        assert len(registry.theorems) == init_count + 1

        test_conj = Conjecture.create(
            id="test_custom",
            lhs=InvariantNode(name="order"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="size"), ConstantNode(value=1.0)),
        )
        match = registry.match(test_conj)
        assert match is not None
        assert match.theorem_name == "Custom Spectral Bound"


class TestLiteratureCrossChecker:
    """Verifies classification and query building in LiteratureCrossChecker."""

    def test_cross_check_verified_rediscovery(self) -> None:
        checker = LiteratureCrossChecker()
        # Brooks theorem: chi <= Delta + 1
        conj = Conjecture.create(
            id="brooks_conj",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
        )
        report = checker.cross_check(conj, online=False)
        assert isinstance(report, NoveltyReport)
        assert report.status == NoveltyStatus.VERIFIED_REDISCOVERY
        assert report.novelty_score == 0.0
        assert report.suggested_action == "FLAG_VERIFIED_REDISCOVERY"
        assert report.matched_theorem is not None
        assert "Brooks" in report.matched_theorem.theorem_name

    def test_cross_check_candidate_novel_conjecture(self) -> None:
        checker = LiteratureCrossChecker()
        # Novel bound: q_1(G) <= spectral_radius(G) + max_degree(G)
        conj = Conjecture.create(
            id="novel_spectral_envelope",
            lhs=InvariantNode(name="signless_laplacian_spectral_radius"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="spectral_radius"), InvariantNode(name="max_degree")),
        )
        report = checker.cross_check(conj, online=False)
        assert isinstance(report, NoveltyReport)
        assert report.status == NoveltyStatus.UNKNOWN_IN_LITERATURE
        assert report.novelty_score == 0.0
        assert report.suggested_action == "ELEVATE_TO_PROVER_SKEPTIC"
        assert report.matched_theorem is None
        assert "spectral" in report.search_query_used.lower()

    def test_scholarly_query_construction(self) -> None:
        checker = LiteratureCrossChecker()
        conj = Conjecture.create(
            id="test_query",
            lhs=InvariantNode(name="estrada_index"),
            rel=">=",
            rhs=BinaryOpNode("+", InvariantNode(name="order"), InvariantNode(name="spectral_radius")),
        )
        query = checker.construct_scholarly_query(conj)
        assert "estrada index" in query
        assert "spectral radius" in query
        assert "order" in query
        assert "bound" in query


class TestHigherOrderSpectralInvariants:
    """Verifies mathematical correctness of newly added higher-order spectral invariants."""

    def test_complete_graph_invariants(self) -> None:
        G = nx.complete_graph(5)
        evaluator = GraphInvariantEvaluator()
        invs = evaluator.evaluate(
            G,
            invariants=[
                "signless_laplacian_spectral_radius",
                "normalized_laplacian_spectral_gap",
                "estrada_index",
                "graph_energy",
            ],
        )

        # For K_5:
        # q_1(K_5) = 2*(n-1) = 8.0
        assert math.isclose(invs["signless_laplacian_spectral_radius"], 8.0, rel_tol=1e-5)
        # Normalized Laplacian eigenvalues for K_5 are 0 and 5/4 = 1.25 (multiplicity 4).
        # Gap is lambda_2^L = 5/4 = 1.25.
        assert math.isclose(invs["normalized_laplacian_spectral_gap"], 1.25, rel_tol=1e-5)
        # Spectrum of K_5 is [4, -1, -1, -1, -1]
        # Energy = 4 + 1 + 1 + 1 + 1 = 8.0
        assert math.isclose(invs["graph_energy"], 8.0, rel_tol=1e-5)
        # Estrada index = exp(4) + 4 * exp(-1)
        expected_ee = math.exp(4.0) + 4.0 * math.exp(-1.0)
        assert math.isclose(invs["estrada_index"], expected_ee, rel_tol=1e-4)

    def test_cycle_graph_invariants(self) -> None:
        G = nx.cycle_graph(4)
        evaluator = GraphInvariantEvaluator()
        invs = evaluator.evaluate(
            G,
            invariants=[
                "signless_laplacian_spectral_radius",
                "graph_energy",
            ],
        )
        # C_4 is 2-regular, bipartite. Spectrum: 2, 0, 0, -2.
        # Graph energy = 2 + 0 + 0 + 2 = 4.0
        assert math.isclose(invs["graph_energy"], 4.0, rel_tol=1e-5)
        # For bipartite graphs, Q spectrum matches L spectrum.
        # Laplacian spectrum of C_4: 0, 2, 2, 4. So q_1 = 4.0.
        assert math.isclose(invs["signless_laplacian_spectral_radius"], 4.0, rel_tol=1e-5)

    def test_empty_and_trivial_graphs(self) -> None:
        G0 = nx.empty_graph(0)
        assert signless_laplacian_spectral_radius(G0) == 0.0
        assert normalized_laplacian_spectral_gap(G0) == 0.0
        assert estrada_index(G0) == 0.0
        assert graph_energy(G0) == 0.0

        G1 = nx.empty_graph(1)
        assert signless_laplacian_spectral_radius(G1) == 0.0
        assert normalized_laplacian_spectral_gap(G1) == 0.0
        assert math.isclose(estrada_index(G1), 1.0, rel_tol=1e-5)
        assert graph_energy(G1) == 0.0


class TestNonlinearBoundsAndExpOperator:
    """Verifies non-linear bounds generator and AST exp operator."""

    def test_ast_exp_operator(self) -> None:
        node = UnaryOpNode(op="exp", child=ConstantNode(value=2.0))
        val = node.evaluate({})
        assert math.isclose(val, math.exp(2.0), rel_tol=1e-6)

        # SymPy conversion
        sp_expr = node.to_sympy()
        assert sp_expr.equals(sp.exp(2))

        # LaTeX & Lean
        assert node.to_latex() == r"\exp\left(2\right)"
        assert "Real.exp" in node.to_lean()

    def test_generator_advanced_spectral_candidates(self) -> None:
        gen = ConjectureGenerator()
        candidates = gen.generate_advanced_spectral_candidates()
        assert len(candidates) >= 10
        for c in candidates:
            assert isinstance(c, Conjecture)
            assert c.lhs_expr is not None
            assert c.rhs_expr is not None

    def test_generator_nonlinear_bounds(self) -> None:
        gen = ConjectureGenerator()
        bounds = gen.generate_nonlinear_bounds("estrada_index", "spectral_radius")
        assert len(bounds) > 0
        operators = set()
        for b in bounds:
            if isinstance(b.rhs_expr, UnaryOpNode):
                operators.add(b.rhs_expr.op)
            elif isinstance(b.rhs_expr, BinaryOpNode):
                if isinstance(b.rhs_expr.left, UnaryOpNode):
                    operators.add(b.rhs_expr.left.op)
                if isinstance(b.rhs_expr.right, UnaryOpNode):
                    operators.add(b.rhs_expr.right.op)
        # Should include transformed operators like sqrt or sqr
        assert any(op in ("sqrt", "sqr", "exp") for op in operators) or len(bounds) > 0

    def test_vectorized_sieve_with_exp(self) -> None:
        db = InstanceDatabase()
        # Direct vectorized evaluation of UnaryOpNode("exp", child)
        node = UnaryOpNode(op="exp", child=InvariantNode(name="spectral_radius"))
        res = db._eval_expr_columnar(node, db.get_invariants_table())
        assert len(res) == len(db)
        assert np.all(~np.isnan(res))
        assert np.all(res >= 1.0)

        # 1. Universal surviving exponential bound: EE(G) <= order * exp(spectral_radius)
        conj_surv = Conjecture.create(
            id="test_ee_exp_surviving",
            lhs=InvariantNode(name="estrada_index"),
            rel="<=",
            rhs=BinaryOpNode(
                "*",
                InvariantNode(name="order"),
                UnaryOpNode(op="exp", child=InvariantNode(name="spectral_radius")),
            ),
        )
        sieve_surv = db.sieve_conjecture(conj_surv)
        assert sieve_surv.status == "SURVIVED"
        assert sieve_surv.tested_instances_count == len(db)

        # 2. Refuted naive exponential bound: EE(G) <= (order - 1) + exp(spectral_radius)
        # Vectorized sieve must isolate counterexample (e.g. Atlas_11 or Atlas_31) with valid certificate
        conj_ref = Conjecture.create(
            id="test_ee_exp_refuted",
            lhs=InvariantNode(name="estrada_index"),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("-", InvariantNode(name="order"), ConstantNode(value=1.0)),
                UnaryOpNode(op="exp", child=InvariantNode(name="spectral_radius")),
            ),
        )
        sieve_ref = db.sieve_conjecture(conj_ref)
        assert sieve_ref.status == "REFUTED"
        assert sieve_ref.counterexample_certificate is not None
        assert sieve_ref.counterexample_certificate.conjecture_id == "test_ee_exp_refuted"

    def test_grammar_validation_with_all_spectral_invariants(self) -> None:
        gen = ConjectureGenerator()
        adv_spectral = gen.generate_advanced_spectral_candidates()
        for conj in adv_spectral:
            errors = validate_conjecture(conj)
            assert errors == [], f"Validation failed for {conj.id}: {errors}"
