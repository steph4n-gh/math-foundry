"""Tier 2 E2E Boundary & Corner Case Test Suite.

Verifies mathematical boundary conditions, extreme invariants, and structural corner cases:
- Null graph (0 vertices, 0 edges)
- Single-vertex graph (K1: n=1, m=0, division-by-zero risks)
- Edgeless/discrete graphs (En: n>1, m=0)
- Complete graphs (Kn: maximal density, equality on Brooks bound)
- Star graphs (Sn: extreme degree variance, leaf vs center)
- Disconnected graphs (K3 + K3, K1 + C5: infinite diameter, zero algebraic connectivity)
- Extreme spectral ratios and division-by-zero guards in AST evaluation
- Adversarial Skeptic catching the odd-cycle exception in Brooks' theorem
- Malformed certificate input robustness
- Unproven conjecture export handling
"""

from __future__ import annotations

import math
from pathlib import Path

import networkx as nx
import numpy as np
import pytest

from .conftest import ReferenceGraphOracle, ReferenceArtifactValidator


class TestTier2BoundaryAndCornerCases:
    """Boundary conditions and structural edge cases across pipeline modules."""

    def test_boundary_empty_null_graph_zero_vertices(self, graph_null, oracle):
        """Boundary: K0 (0 vertices, 0 edges) must not trigger uncaught crashes."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = ["order", "size", "max_degree", "min_degree", "density", "triangle_count"]
        computed = evaluator_cls.evaluate(graph_null, invariants)

        assert computed["order"] == 0
        assert computed["size"] == 0
        assert computed["max_degree"] == 0
        assert computed["min_degree"] == 0
        assert computed["density"] == 0.0
        assert computed["triangle_count"] == 0

    def test_boundary_single_vertex_graph_division_by_zero(self, graph_k1, oracle):
        """Boundary: K1 (1 vertex, 0 edges) has n(n-1) = 0 denominator in density formula."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = [
            "order", "size", "max_degree", "min_degree", "density",
            "chromatic_number", "clique_number", "independence_number",
            "diameter", "radius", "algebraic_connectivity"
        ]
        computed = evaluator_cls.evaluate(graph_k1, invariants)

        assert computed["order"] == 1
        assert computed["size"] == 0
        assert computed["density"] == 0.0  # Must not raise ZeroDivisionError
        assert computed["chromatic_number"] == 1
        assert computed["clique_number"] == 1
        assert computed["independence_number"] == 1
        assert computed["max_degree"] == 0
        assert computed["min_degree"] == 0

    def test_boundary_edgeless_graph_discrete(self, graph_empty_5, oracle):
        """Boundary: E5 (5 isolated vertices) has 0 edges and disconnected components."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = [
            "order", "size", "max_degree", "min_degree", "density",
            "chromatic_number", "clique_number", "independence_number",
            "is_connected", "girth"
        ]
        computed = evaluator_cls.evaluate(graph_empty_5, invariants)

        assert computed["order"] == 5
        assert computed["size"] == 0
        assert computed["density"] == 0.0
        assert computed["chromatic_number"] == 1
        assert computed["clique_number"] == 1
        assert computed["independence_number"] == 5
        assert computed["is_connected"] is False
        assert math.isinf(computed["girth"]) or computed["girth"] > 1000

    def test_boundary_complete_graph_clique(self, graph_k5, oracle):
        """Boundary: K5 has maximum density (1.0), omega = n, chi = n, alpha = 1."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = [
            "order", "size", "max_degree", "min_degree", "density",
            "chromatic_number", "clique_number", "independence_number",
            "triangle_count", "spectral_radius", "algebraic_connectivity"
        ]
        computed = evaluator_cls.evaluate(graph_k5, invariants)

        assert computed["order"] == 5
        assert computed["size"] == 10
        assert computed["density"] == 1.0
        assert computed["chromatic_number"] == 5
        assert computed["clique_number"] == 5
        assert computed["independence_number"] == 1
        assert computed["triangle_count"] == 10  # 5 choose 3 = 10
        # Spectral radius of K_n is n - 1
        assert np.isclose(computed["spectral_radius"], 4.0, atol=1e-5)
        # Algebraic connectivity of K_n is n
        assert np.isclose(computed["algebraic_connectivity"], 5.0, atol=1e-5)

    def test_boundary_star_graph_extreme_degrees(self, graph_star_6, oracle):
        """Boundary: S6 has extreme degree asymmetry (Delta = 5, delta = 1) and chi = 2."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = [
            "order", "size", "max_degree", "min_degree",
            "chromatic_number", "clique_number", "independence_number",
            "triangle_count", "is_bipartite"
        ]
        computed = evaluator_cls.evaluate(graph_star_6, invariants)

        assert computed["order"] == 6
        assert computed["size"] == 5
        assert computed["max_degree"] == 5
        assert computed["min_degree"] == 1
        assert computed["chromatic_number"] == 2
        assert computed["clique_number"] == 2
        assert computed["independence_number"] == 5
        assert computed["triangle_count"] == 0
        assert computed["is_bipartite"] is True

    def test_boundary_disconnected_components_infinite_diameter(self, graph_disconnected_k3_k3, oracle):
        """Boundary: K3 + K3 is disconnected; algebraic connectivity must be 0, diameter inf."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        invariants = ["is_connected", "algebraic_connectivity", "diameter"]
        computed = evaluator_cls.evaluate(graph_disconnected_k3_k3, invariants)

        assert computed["is_connected"] is False
        assert np.isclose(computed["algebraic_connectivity"], 0.0, atol=1e-6)
        assert math.isinf(computed["diameter"]) or computed["diameter"] > 1000

    def test_boundary_ast_division_by_zero_safe_handling(self, graph_k1):
        """Boundary: AST division node when denominator evaluates to 0 must not crash."""
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")
        Conjecture = getattr(ast_mod, "Conjecture")

        # Expression: order / (order - 1) on K1 (where order = 1, denom = 0)
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        div_expr = BinaryOpNode("/", InvariantNode("order"), denom)
        conj = Conjecture(
            id="div_zero_test",
            statement="order / (order - 1) >= 0",
            lhs_expr=div_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.0),
            complexity=3,
        )

        # Evaluating on K1 must either catch ZeroDivisionError and return False/inf or raise ArithmeticError
        try:
            holds, lhs_val, _ = conj.evaluate(graph_k1)
            # If handled numerically, lhs_val should be infinite or NaN
            assert math.isinf(lhs_val) or math.isnan(lhs_val) or holds is False
        except (ZeroDivisionError, ValueError):
            # Controlled mathematical exception is acceptable
            pass

    def test_boundary_skeptic_catches_odd_cycle_exception_in_brooks(self, graph_c5):
        """Boundary: Brooks' bound chi <= Delta fails specifically on odd cycles (C5: Delta=2, chi=3)."""
        skeptic_mod = pytest.importorskip("autonomous_math.prover.skeptic")
        dag_mod = pytest.importorskip("autonomous_math.prover.dag")
        AdversarialSkeptic = getattr(skeptic_mod, "AdversarialSkeptic")
        ProofNode = getattr(dag_mod, "ProofNode")
        DeductionStep = getattr(dag_mod, "DeductionStep")

        # Propose naive Brooks application: chi(G) <= Delta(G) for all connected graphs
        premise = ProofNode(
            node_id="premise_connected",
            label="G is connected",
            statement_latex=r"G \text{ connected}",
            statement_lean="G.Connected",
            node_type="PREMISE",
            scope={"assumptions": ["connected"]},
        )
        target = ProofNode(
            node_id="naive_brooks",
            label="chi(G) <= Delta(G)",
            statement_latex=r"\chi(G) \le \Delta(G)",
            statement_lean="G.chromaticNumber <= G.maxDegree",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["connected"]},
        )

        step = DeductionStep(
            step_id="naive_brooks_step",
            target_node_id=target.node_id,
            premise_node_ids=[premise.node_id],
            rule_type="AXIOM_APPLICATION",
            rule_name="NaiveBrooks",
            justification="Applying Brooks without odd cycle exclusion",
        )

        skeptic = AdversarialSkeptic()
        has_counter, critique = skeptic.check_edge_cases(step, test_graphs=[graph_c5])
        assert has_counter is True or "odd cycle" in (critique or "").lower() or "c5" in (critique or "").lower()

    def test_boundary_malformed_json_certificate_rejection(self):
        """Boundary: Sieve certificate verifier cleanly rejects malformed certificates."""
        cert_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        CounterexampleCertificate = getattr(cert_mod, "CounterexampleCertificate")
        CounterexampleCertificateVerifier = getattr(cert_mod, "CounterexampleCertificateVerifier")
        Conjecture = getattr(ast_mod, "Conjecture")

        dummy_conj = Conjecture(
            id="dummy", statement="dummy", lhs_expr=ast_mod.ConstantNode(1.0),
            rel="<=", rhs_expr=ast_mod.ConstantNode(2.0), complexity=1
        )

        # 1. Asymmetric adjacency matrix
        asymmetric_cert = CounterexampleCertificate(
            conjecture_id="dummy", graph_order=2, graph_size=1,
            adjacency_matrix=[[0, 1], [0, 0]],  # Not symmetric!
            edges=[(0, 1)], invariants={}, refutation_witness={"type": "direct_evaluation"},
            verification_hash="hash1",
        )
        assert CounterexampleCertificateVerifier.verify(asymmetric_cert, dummy_conj) is False

        # 2. Dimension mismatch (order=3 but 2x2 matrix)
        dim_mismatch_cert = CounterexampleCertificate(
            conjecture_id="dummy", graph_order=3, graph_size=1,
            adjacency_matrix=[[0, 1], [1, 0]],  # Only 2 rows!
            edges=[(0, 1)], invariants={}, refutation_witness={"type": "direct_evaluation"},
            verification_hash="hash2",
        )
        assert CounterexampleCertificateVerifier.verify(dim_mismatch_cert, dummy_conj) is False

    def test_boundary_export_unproven_conjecture_handling(self, tmp_path):
        """Boundary: Exporters handle UNPROVEN result gracefully without crashing on empty proof tree."""
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        prover_mod = pytest.importorskip("autonomous_math.prover.dag")

        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")

        unproven_conj = ast_mod.Conjecture(
            id="open_hadwiger",
            statement="Hadwiger conjecture for k=7",
            lhs_expr=ast_mod.ConstantNode(7.0),
            rel="<=",
            rhs_expr=ast_mod.ConstantNode(7.0),
            complexity=5,
        )

        unproven_result = search_mod.ProofResult(
            conjecture=unproven_conj,
            dag=prover_mod.LemmaDAG(root_node_id="root"),
            status="UNPROVEN",
            minimal_proof_tree=[],
            critique_summary={"reason": "Search depth exhausted"},
        )

        # Both generators must succeed without exceptions
        latex_gen = LatexPreprintGenerator()
        tex_dir = latex_gen.generate(unproven_result, output_dir=tmp_path / "unproven_latex")
        assert (tex_dir / "main.tex").exists()

        lean_gen = LeanComparatorGenerator()
        json_p, lean_p = lean_gen.generate(unproven_result, output_dir=tmp_path / "unproven_lean")
        assert json_p.exists()
        assert lean_p.exists()
