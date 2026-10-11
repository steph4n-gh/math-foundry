"""Unit Tests for 3D and Higher-Dimensional Multivariate Envelopes & Folklore Attributions.

Verifies:
1. 3D convex hull planar bounds generation (`generate_multivariate_bounds`).
2. Synthesis of target multi-invariant triads:
   - (chi vs (Delta, omega)) [Reed-type bounds]
   - (chi vs (d_bar, omega))
   - (m vs (n, omega)) [Turan-type density bounds]
   - (alpha vs (n, Delta)) [Caro-Wei bounds]
   - (q_1 vs (Delta, lambda_1)) [Signless Laplacian multi-spectral bounds]
3. Conditional / guarded 3D mining (is_triangle_free, is_regular, is_bipartite).
4. Robustness against coplanar, flat, or degenerate point clouds (e.g. bipartite chi == omega).
5. Vectorized empirical sieving and tightness on InstanceDatabase.
6. Folklore / textbook theorem attribution in KnownTheoremRegistry and LiteratureCrossChecker
   (chi >= omega, omega <= n - alpha + 1, alpha <= n - m/Delta, etc.).
7. Campaign configuration (triads present in all presets) and Lean 4 export compatibility.
"""

from __future__ import annotations

import math
from pathlib import Path
import tempfile
import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.conjecturing.generator import (
    ConjectureGenerator,
    _build_linear_rhs,
    _snap_rational,
)
from autonomous_math.export.lean_generator import LeanComparatorGenerator
from autonomous_math.novelty.literature_crosscheck import (
    KnownTheoremRegistry,
    LiteratureCrossChecker,
    NoveltyReport,
    NoveltyStatus,
)
from autonomous_math.sieve.instance_db import InstanceDatabase
from run_research import CAMPAIGN_PRESETS


class TestMultivariateConvexHull3D:
    """Verifies 3D and higher-dimensional convex hull bound generation."""

    def test_build_linear_rhs_combinations(self) -> None:
        """Verify _build_linear_rhs helper with diverse positive, negative, zero, and constant terms."""
        # 1. chi <= 0.5 * Delta + 0.5 * omega + 1.0
        rhs1 = _build_linear_rhs(["max_degree", "clique_number"], [0.5, 0.5], 1.0)
        assert isinstance(rhs1, BinaryOpNode)
        assert rhs1.op == "+"

        # 2. omega <= 1.0 * order - 1.0 * independence_number + 1.0
        rhs2 = _build_linear_rhs(["order", "independence_number"], [1.0, -1.0], 1.0)
        assert isinstance(rhs2, BinaryOpNode)

        # 3. chi >= 1.0 * omega (with zero slope on first invariant)
        rhs3 = _build_linear_rhs(["max_degree", "clique_number"], [0.0, 1.0], 0.0)
        assert isinstance(rhs3, InvariantNode)
        assert rhs3.name == "clique_number"

        # 4. Only constants
        rhs4 = _build_linear_rhs(["max_degree", "clique_number"], [0.0, 0.0], 5.0)
        assert isinstance(rhs4, ConstantNode)
        assert rhs4.value == 5.0

    def test_reed_triad_generation(self) -> None:
        """Verify (chi vs (Delta, omega)) generates sharp upper bounds and clique lower bound."""
        gen = ConjectureGenerator()
        conjs = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree", "clique_number"],
            relations=["<=", ">="],
        )

        assert len(conjs) >= 5

        # Check for presence of upper bounds
        upper_bounds = [c for c in conjs if c.rel == "<="]
        assert len(upper_bounds) >= 3

        # Check for presence of lower bounds
        lower_bounds = [c for c in conjs if c.rel == ">="]
        assert len(lower_bounds) >= 1

        # Check that clique lower bound chi >= omega is synthesized
        has_clique_bound = any(
            c.rel == ">="
            and isinstance(c.rhs_expr, InvariantNode)
            and c.rhs_expr.name == "clique_number"
            for c in lower_bounds
        )
        assert has_clique_bound, "Expected chi >= omega lower bound in generated set"

        # Check that Reed-type upper bound with positive slopes is synthesized
        has_reed_type = any(
            c.rel == "<="
            and len(c.metadata.get("slopes", [])) == 2
            and c.metadata["slopes"][0] > 0
            and c.metadata["slopes"][1] > 0
            for c in upper_bounds
        )
        assert has_reed_type, "Expected Reed-type positive slope bound in generated upper bounds"

        # Check metadata
        for c in conjs:
            assert c.metadata.get("source") == "multivariate_convex_hull"
            assert c.metadata.get("dimension") == 3
            assert c.metadata.get("target_y") == "chromatic_number"
            assert c.metadata.get("target_xs") == ["max_degree", "clique_number"]

    def test_all_five_target_triads(self) -> None:
        """Verify all 5 target triads specified in requirements synthesize valid envelopes."""
        gen = ConjectureGenerator()
        target_triads = [
            ("chromatic_number", ["max_degree", "clique_number"]),
            ("chromatic_number", ["average_degree", "clique_number"]),
            ("size", ["order", "clique_number"]),
            ("independence_number", ["order", "max_degree"]),
            ("signless_laplacian_spectral_radius", ["max_degree", "spectral_radius"]),
        ]

        for y_inv, x_invs in target_triads:
            bounds = gen.generate_multivariate_bounds(
                target_y=y_inv,
                target_xs=x_invs,
                relations=["<=", ">="],
                max_bounds=6,
            )
            assert len(bounds) > 0, f"Triad ({y_inv} vs {x_invs}) produced 0 bounds"
            for b in bounds:
                assert b.lhs_expr.name == y_inv
                vars_in_rhs = b.rhs_expr.variables
                assert any(x in vars_in_rhs for x in x_invs) or isinstance(b.rhs_expr, ConstantNode)

    def test_guarded_mining_triangle_free(self) -> None:
        """Verify mining conditioned on is_triangle_free attaches guard and preserves validity."""
        gen = ConjectureGenerator()
        bounds = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree", "clique_number"],
            guard="is_triangle_free",
            relations=["<="],
        )
        assert len(bounds) >= 2
        for b in bounds:
            assert b.guard_predicate is not None
            assert isinstance(b.guard_predicate, GuardPredicate)
            assert b.guard_predicate.property_name == "is_triangle_free"
            assert "triangle-free" in b.statement

    def test_guarded_mining_regular(self) -> None:
        """Verify mining conditioned on is_regular."""
        gen = ConjectureGenerator()
        bounds = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree", "clique_number"],
            guard=GuardPredicate(property_name_or_type="is_regular"),
            relations=["<="],
        )
        assert len(bounds) >= 2
        for b in bounds:
            assert b.guard_predicate is not None
            assert b.guard_predicate.property_name == "is_regular"

    def test_guarded_mining_bipartite_coplanar_handling(self) -> None:
        """Verify mining conditioned on is_bipartite handles coplanar flat dimension gracefully."""
        gen = ConjectureGenerator()
        # On bipartite graphs, chi == omega, which is a 2D plane in 3D space.
        # This test ensures Qhull precision error is intercepted and coplanar least squares fit recovers chi <= omega.
        bounds = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree", "clique_number"],
            guard="is_bipartite",
            relations=["<=", ">="],
        )
        assert len(bounds) > 0
        # Check that chi <= omega or chi == omega was synthesized
        has_omega_bound = any(
            isinstance(b.rhs_expr, InvariantNode) and b.rhs_expr.name == "clique_number"
            for b in bounds
        )
        assert has_omega_bound, "Expected bipartite exact bound chi <= omega or chi >= omega"

    def test_2d_fallback_with_single_variable(self) -> None:
        """Passing a single independent invariant must delegate to 2D parametric generation."""
        gen = ConjectureGenerator()
        bounds = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree"],
            guard="is_triangle_free",
        )
        assert len(bounds) >= 1
        for b in bounds:
            assert b.guard_predicate is not None
            assert b.guard_predicate.property_name == "is_triangle_free"

    def test_higher_dimensional_4d_convex_hull(self) -> None:
        """Verify N-D scalability: 4D point cloud (chi vs (Delta, omega, order))."""
        gen = ConjectureGenerator()
        bounds = gen.generate_multivariate_bounds(
            target_y="chromatic_number",
            target_xs=["max_degree", "clique_number", "order"],
            relations=["<="],
            max_bounds=5,
        )
        assert len(bounds) >= 1
        for b in bounds:
            assert b.metadata.get("dimension") == 4
            assert len(b.metadata.get("target_xs", [])) == 3

    def test_snap_rational_precision(self) -> None:
        """Verify _snap_rational accurately selects the lowest-error denominator."""
        assert _snap_rational(0.8333333333333334) == pytest.approx(5 / 6)
        assert _snap_rational(2.875) == 2.875  # 23 / 8
        assert _snap_rational(0.8) == 0.8  # 4 / 5
        assert _snap_rational(0.5) == 0.5  # 1 / 2
        assert _snap_rational(0.3333333333333333) == pytest.approx(1 / 3)
        assert _snap_rational(4.0) == 4.0

    def test_build_linear_rhs_clean_negative_formatting(self) -> None:
        """Negative slopes should not cause double-multiplication or nested -1 * 2 * x ASTs."""
        # 1. Negative slope without other positive variables: -2 * Delta + 5
        rhs_neg = _build_linear_rhs(["max_degree"], [-2.0], 5.0)
        assert " -1 \\cdot 2" not in rhs_neg.to_latex()
        assert rhs_neg.to_latex() == "-2 \\cdot \\Delta(G) + 5"

        # 2. Positive and negative variables ordered naturally: n - alpha + 1
        rhs_mixed = _build_linear_rhs(["independence_number", "order"], [-1.0, 1.0], 1.0)
        assert rhs_mixed.to_latex() == "n - (\\alpha(G)) + 1"

    def test_dataset_validity_guarantee_sieve(self) -> None:
        """Generated 3D bounds across all 5 target triads must strictly survive empirical testing on the database."""
        gen = ConjectureGenerator()
        db = InstanceDatabase()

        target_triads = [
            ("chromatic_number", ["max_degree", "clique_number"]),
            ("chromatic_number", ["average_degree", "clique_number"]),
            ("size", ["order", "clique_number"]),
            ("independence_number", ["order", "max_degree"]),
            ("signless_laplacian_spectral_radius", ["max_degree", "spectral_radius"]),
        ]

        total_tested = 0
        for y_inv, x_invs in target_triads:
            bounds = gen.generate_multivariate_bounds(
                target_y=y_inv,
                target_xs=x_invs,
                relations=["<=", ">="],
            )
            assert len(bounds) >= 5, f"Triad ({y_inv} vs {x_invs}) produced fewer than 5 bounds"
            for b in bounds:
                res = db.sieve_conjecture(b)
                assert res.status == "SURVIVED", f"Conjecture {b.statement} was unexpectedly refuted on database"
                assert res.tested_instances_count >= 1000
                total_tested += 1

        assert total_tested >= 50

    def test_edge_cases_and_degeneracies(self) -> None:
        """Verify degenerate inputs handle gracefully without exceptions."""
        gen = ConjectureGenerator()
        # Empty graph list
        assert gen.generate_multivariate_bounds("chromatic_number", ["max_degree", "clique_number"], graphs=[]) == []

        # Single graph
        single_g = [nx.path_graph(3)]
        assert gen.generate_multivariate_bounds("chromatic_number", ["max_degree", "clique_number"], graphs=single_g) == []

        # Identical graphs (affine rank 0 in 3D)
        identical = [nx.path_graph(4) for _ in range(5)]
        res = gen.generate_multivariate_bounds("chromatic_number", ["max_degree", "clique_number"], graphs=identical)
        assert isinstance(res, list)

        # Collinear graphs (affine rank 1 in 3D): path graphs P_3 to P_14 have size = order - 1, max_degree = 2
        paths = [nx.path_graph(i) for i in range(3, 15)]
        path_bounds = gen.generate_multivariate_bounds(
            target_y="size",
            target_xs=["order", "max_degree"],
            graphs=paths,
            relations=["<=", ">="],
        )
        assert len(path_bounds) == 2, f"Expected exactly 2 exact line bounds for collinear paths, got {len(path_bounds)}"
        for pb in path_bounds:
            assert pb.metadata["slopes"] == [1.0, 0.0]
            assert pb.metadata["intercept"] == -1.0
            assert "m <= n - (1)" in pb.statement or "m >= n - (1)" in pb.statement


class TestFolkloreAttribution:
    """Verifies that fundamental textbook/folklore relations are attributed to literature."""

    def test_folklore_chi_ge_omega_attribution(self) -> None:
        """chi(G) >= omega(G) must be classified as TEXTBOOK_FOLKLORE."""
        checker = LiteratureCrossChecker()
        conj = Conjecture.create(
            id="test_chi_omega",
            lhs=InvariantNode(name="chromatic_number"),
            rel=">=",
            rhs=InvariantNode(name="clique_number"),
        )
        report = checker.cross_check(conj, online=False)
        assert report.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert report.suggested_action == "FLAG_TEXTBOOK_FOLKLORE"
        assert report.matched_theorem is not None
        assert "Coloring-Clique" in report.matched_theorem.theorem_name
        assert report.novelty_score == 0.0

    def test_folklore_erdos_szekeres_attribution(self) -> None:
        """omega <= n - alpha + 1 and alpha <= n - omega + 1 must match Erdős-Szekeres folklore."""
        checker = LiteratureCrossChecker()
        conj_omega = Conjecture.create(
            id="test_es_omega",
            lhs=InvariantNode(name="clique_number"),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("-", InvariantNode(name="order"), InvariantNode(name="independence_number")),
                ConstantNode(value=1.0),
            ),
        )
        report1 = checker.cross_check(conj_omega, online=False)
        assert report1.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert "Erdős-Szekeres" in report1.matched_theorem.theorem_name

        conj_alpha = Conjecture.create(
            id="test_es_alpha",
            lhs=InvariantNode(name="independence_number"),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("-", InvariantNode(name="order"), InvariantNode(name="clique_number")),
                ConstantNode(value=1.0),
            ),
        )
        report2 = checker.cross_check(conj_alpha, online=False)
        assert report2.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert "Erdős-Szekeres" in report2.matched_theorem.theorem_name

    def test_folklore_caro_wei_attribution(self) -> None:
        """alpha <= n - m / Delta must match Caro-Wei degree-extremal bound."""
        checker = LiteratureCrossChecker()
        conj = Conjecture.create(
            id="test_caro_wei",
            lhs=InvariantNode(name="independence_number"),
            rel="<=",
            rhs=BinaryOpNode(
                "-",
                InvariantNode(name="order"),
                BinaryOpNode("/", InvariantNode(name="size"), InvariantNode(name="max_degree")),
            ),
            guard=GuardPredicate(predicate_type="comparison", invariant="max_degree", op=">=", threshold=1.0),
        )
        report = checker.cross_check(conj, online=False)
        assert report.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert "Caro-Wei" in report.matched_theorem.theorem_name

    def test_folklore_trivial_order_bounds(self) -> None:
        """Trivial bounds chi <= n, omega <= n, alpha <= n must match folklore."""
        checker = LiteratureCrossChecker()
        for inv in ["chromatic_number", "clique_number", "independence_number"]:
            conj = Conjecture.create(
                id=f"test_order_{inv}",
                lhs=InvariantNode(name=inv),
                rel="<=",
                rhs=InvariantNode(name="order"),
            )
            report = checker.cross_check(conj, online=False)
            assert report.status == NoveltyStatus.TEXTBOOK_FOLKLORE

    def test_folklore_bipartite_attribution(self) -> None:
        """Bipartite bounds chi <= omega and chi <= 2 must match TEXTBOOK_FOLKLORE."""
        checker = LiteratureCrossChecker()
        conj_bip_omega = Conjecture.create(
            id="test_bip_omega",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=InvariantNode(name="clique_number"),
            guard=GuardPredicate(property_name_or_type="is_bipartite"),
        )
        report1 = checker.cross_check(conj_bip_omega, online=False)
        assert report1.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert "Bipartite" in report1.matched_theorem.theorem_name

        conj_bip_two = Conjecture.create(
            id="test_bip_two",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=ConstantNode(value=2.0),
            guard=GuardPredicate(property_name_or_type="is_bipartite"),
        )
        report2 = checker.cross_check(conj_bip_two, online=False)
        assert report2.status == NoveltyStatus.TEXTBOOK_FOLKLORE

    def test_folklore_specialization_guard_attribution(self) -> None:
        """Guarded instances of universal theorems must be attributed as specializations, not false novelties."""
        checker = LiteratureCrossChecker()

        # 1. chi >= omega on triangle-free graphs is a specialization of fundamental folklore chi >= omega
        conj_tf_omega = Conjecture.create(
            id="test_tf_omega",
            lhs=InvariantNode(name="chromatic_number"),
            rel=">=",
            rhs=InvariantNode(name="clique_number"),
            guard=GuardPredicate(property_name_or_type="is_triangle_free"),
        )
        report1 = checker.cross_check(conj_tf_omega, online=False)
        assert report1.status == NoveltyStatus.TEXTBOOK_FOLKLORE
        assert report1.matched_theorem.equivalence_type == "specialization"

        # 2. chi <= Delta + 1 on triangle-free graphs is a specialization of Brooks' classical theorem
        conj_tf_brooks = Conjecture.create(
            id="test_tf_brooks",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
            guard=GuardPredicate(property_name_or_type="is_triangle_free"),
        )
        report2 = checker.cross_check(conj_tf_brooks, online=False)
        assert report2.status == NoveltyStatus.VERIFIED_REDISCOVERY
        assert "Brooks" in report2.matched_theorem.theorem_name
        assert report2.matched_theorem.equivalence_type == "specialization"

    def test_folklore_degree_bounds(self) -> None:
        """Textbook bounds omega <= Delta + 1 and d_bar <= Delta must match folklore."""
        checker = LiteratureCrossChecker()
        conj_omega = Conjecture.create(
            id="test_omega_deg",
            lhs=InvariantNode(name="clique_number"),
            rel="<=",
            rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
        )
        report1 = checker.cross_check(conj_omega, online=False)
        assert report1.status == NoveltyStatus.TEXTBOOK_FOLKLORE

        conj_deg = Conjecture.create(
            id="test_avg_max_deg",
            lhs=InvariantNode(name="average_degree"),
            rel="<=",
            rhs=InvariantNode(name="max_degree"),
        )
        report2 = checker.cross_check(conj_deg, online=False)
        assert report2.status == NoveltyStatus.TEXTBOOK_FOLKLORE

    def test_novel_3d_bound_not_falsely_reported_folklore(self) -> None:
        """A genuinely non-trivial 3D bound must NOT be matched to folklore and elevated as candidate novel."""
        checker = LiteratureCrossChecker()
        conj = Conjecture.create(
            id="novel_3d_reed_type",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("*", ConstantNode(value=0.37), InvariantNode(name="max_degree")),
                BinaryOpNode(
                    "+",
                    BinaryOpNode("*", ConstantNode(value=0.52), InvariantNode(name="clique_number")),
                    ConstantNode(value=1.48),
                ),
            ),
        )
        report = checker.cross_check(conj, online=False)
        assert report.status == NoveltyStatus.UNKNOWN_IN_LITERATURE
        assert report.novelty_score == 0.0
        assert report.suggested_action == "ELEVATE_TO_PROVER_SKEPTIC"

    def test_lean_workspace_rebuild_on_mtime(self) -> None:
        """LeanToolchain.ensure_workspace_built must correctly verify or rebuild workspace."""
        from autonomous_math.prover.lean_prover import LeanToolchain
        tc = LeanToolchain()
        if tc.is_available:
            assert tc.ensure_workspace_built() is True


class TestCampaignTriadsIntegration:
    """Verifies campaign presets configuration and Lean 4 export for 3D bounds."""

    def test_all_campaign_presets_have_triads(self) -> None:
        """Ensure all 4 research campaign presets specify non-empty triads."""
        for preset_name, cfg in CAMPAIGN_PRESETS.items():
            assert "triads" in cfg, f"Preset '{preset_name}' is missing 'triads'"
            assert len(cfg["triads"]) > 0, f"Preset '{preset_name}' has empty 'triads'"
            for entry in cfg["triads"]:
                assert len(entry) in (2, 3), f"Invalid triad entry: {entry}"
                assert isinstance(entry[0], str)
                assert isinstance(entry[1], list) and len(entry[1]) >= 2

    def test_lean4_comparator_export_for_3d_bounds(self) -> None:
        """Verify that 3D conjectures export to valid Lean 4 challenge specs and JSON metadata."""
        conj = Conjecture.create(
            id="test_reed_lean_export",
            lhs=InvariantNode(name="chromatic_number"),
            rel="<=",
            rhs=BinaryOpNode(
                "+",
                BinaryOpNode("*", ConstantNode(value=0.5), InvariantNode(name="max_degree")),
                BinaryOpNode(
                    "+",
                    BinaryOpNode("*", ConstantNode(value=0.5), InvariantNode(name="clique_number")),
                    ConstantNode(value=1.0),
                ),
            ),
        )
        gen = LeanComparatorGenerator()
        with tempfile.TemporaryDirectory() as td:
            res = gen.generate(conj, output_dir=Path(td))
            assert res.lean_file.exists()
            assert res.json_file.exists()

            lean_src = res.lean_file.read_text(encoding="utf-8")
            assert "G.chromaticNumber" in lean_src
            assert "G.maxDegree" in lean_src
            assert "G.cliqueNum" in lean_src
            assert "sorry" in lean_src
