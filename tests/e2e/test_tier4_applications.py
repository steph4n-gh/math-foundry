"""Tier 4 E2E Real-World Discovery Application Scenarios.

Verifies end-to-end mathematical discovery workflows:
1. Scenario 1 (Acceptance Criteria): C5 Refutation of Triangle-Free 2-Colorability
2. Scenario 2: Caro-Wei / Turan Independence Number Lower Bound (alpha >= n / (Delta + 1))
3. Scenario 3: Clique-Chromatic Lower Bound (chi >= omega)
4. Scenario 4: Hoffman Spectral Lower Bound on Chromatic Number (chi >= 1 - lambda_1 / lambda_n)
5. Scenario 5: Grotzsch Graph Refutation of Triangle-Free 3-Colorability (chi(M4) = 4)
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx
import numpy as np
import pytest

from .conftest import ReferenceGraphOracle, ReferenceArtifactValidator


class TestTier4RealWorldDiscoveryScenarios:
    """End-to-end execution of authentic mathematical discovery challenges."""

    def test_application_scenario_c5_refutation_of_triangle_free_2_colorability(
        self, tmp_path, graph_c5, oracle
    ):
        """Scenario 1 (Acceptance Criteria): Empirical sieve refutes 'Triangle-free ==> chi <= 2' with C5."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        cegar_mod = pytest.importorskip("autonomous_math.sieve.cegar")
        cert_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        validator_mod = pytest.importorskip("autonomous_math.export.validator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        CEGARSieve = getattr(cegar_mod, "CEGARSieve")
        CounterexampleCertificateVerifier = getattr(cert_mod, "CounterexampleCertificateVerifier")
        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")
        OutputSyntaxValidator = getattr(validator_mod, "OutputSyntaxValidator")

        # 1. Target Conjecture: Triangle-free graphs have chi <= 2
        conj = Conjecture(
            id="conj_triangle_free_bipartite",
            statement="is_triangle_free(G) ==> chi(G) <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        # 2. Sieve falsification via Z3 CEGAR
        cegar = CEGARSieve()
        witness_g = cegar.synthesize_counterexample(max_order=5, is_triangle_free=True, target_chromatic_lower_bound=3)
        assert witness_g is not None
        assert nx.is_isomorphic(witness_g, graph_c5)

        # 3. Build & verify explicit Counterexample Certificate
        adj_matrix = nx.to_numpy_array(witness_g, dtype=int).tolist()
        odd_cycle = next(c for c in nx.cycle_basis(witness_g) if len(c) % 2 == 1)
        cert = cert_mod.CounterexampleCertificate(
            conjecture_id=conj.id,
            graph_order=5,
            graph_size=5,
            adjacency_matrix=adj_matrix,
            edges=list(witness_g.edges()),
            invariants=oracle.evaluate_all(witness_g),
            refutation_witness={
                "type": "odd_cycle",
                "details": list(odd_cycle) + [odd_cycle[0]],
            },
            verification_hash="sha256_c5_witness_verified",
        )

        is_cert_valid = CounterexampleCertificateVerifier.verify(cert, conj)
        assert is_cert_valid is True

        sieve_result = cert_mod.SieveResult(
            status="REFUTED",
            conjecture=conj,
            tested_instances_count=50,
            counterexample_certificate=cert,
        )

        # 4. Generate LaTeX Preprint
        latex_gen = LatexPreprintGenerator()
        tex_dir = latex_gen.generate(sieve_result, output_dir=tmp_path / "c5_paper")

        # Verify C5 matrix and section content
        cert_tex = (tex_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "pmatrix" in cert_tex or "matrix" in cert_tex
        valid_latex, l_errs = OutputSyntaxValidator.validate_latex_directory(tex_dir)
        assert valid_latex is True, f"LaTeX errors: {l_errs}"

        # 5. Generate Lean 4 Comparator Challenge
        lean_gen = LeanComparatorGenerator()
        json_path, lean_path = lean_gen.generate(sieve_result, output_dir=tmp_path / "c5_lean")

        is_valid_json, j_errs = ReferenceArtifactValidator.validate_lean_comparator_json(json_path.read_text())
        assert is_valid_json is True, f"JSON errors: {j_errs}"

        lean_code = lean_path.read_text()
        is_valid_lean, lean_errs = ReferenceArtifactValidator.validate_lean_source(lean_code)
        assert is_valid_lean is True, f"Lean errors: {lean_errs}"

        # Must express existence of triangle-free non-2-colorable graph
        assert "CliqueFree 3" in lean_code or "triangle_free" in lean_code.lower()
        assert "Colorable 2" in lean_code or "two_colorable" in lean_code.lower()

    def test_application_scenario_independent_set_lower_bound(self, tmp_path, oracle):
        """Scenario 2: Discovery and proof of Caro-Wei bound alpha >= n / (Delta + 1)."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")

        # 1. Candidate Conjecture: alpha >= n / (Delta + 1)
        denom = BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0))
        rhs = BinaryOpNode("/", InvariantNode("order"), denom)
        conj = Conjecture(
            id="caro_wei_bound",
            statement="alpha >= n / (Delta + 1)",
            lhs_expr=InvariantNode("independence_number"),
            rel=">=",
            rhs_expr=rhs,
            complexity=4,
        )

        # 2. Sieve testing against instance database
        db = sieve_mod.InstanceDatabase()
        sieve_res = db.sieve_conjecture(conj)
        assert sieve_res.status == "SURVIVED"

        # 3. Prover-Skeptic search loop
        prover = search_mod.ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=5)
        assert proof_res.status == "PROVEN"

        # 4. Export deliverables
        latex_gen = latex_mod.LatexPreprintGenerator()
        tex_dir = latex_gen.generate(proof_res, output_dir=tmp_path / "caro_wei_tex")
        assert (tex_dir / "main.tex").exists()

        lean_gen = lean_mod.LeanComparatorGenerator()
        j_p, l_p = lean_gen.generate(proof_res, output_dir=tmp_path / "caro_wei_lean")
        lean_code = l_p.read_text()
        assert "indepNum" in lean_code or "independence_number" in lean_code.lower()

    def test_application_scenario_clique_chromatic_bound(self, tmp_path, oracle):
        """Scenario 3: Universal bound chi >= omega tested across instances, proved, and exported."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")

        conj = Conjecture(
            id="chi_ge_omega",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        # Sieve passes all instances
        db = sieve_mod.InstanceDatabase()
        sieve_res = db.sieve_conjecture(conj)
        assert sieve_res.status == "SURVIVED"

        # Prover constructs deductive proof from coloring partition
        prover = search_mod.ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=4)
        assert proof_res.status == "PROVEN"

        # Lean 4 theorem export
        lean_gen = lean_mod.LeanComparatorGenerator()
        j_p, l_p = lean_gen.generate(proof_res, output_dir=tmp_path / "clique_chromatic_lean")
        lean_code = l_p.read_text()
        assert "cliqueNum" in lean_code or "clique" in lean_code.lower()
        assert "chromaticNumber" in lean_code or "chromatic" in lean_code.lower()

    def test_application_scenario_hoffman_spectral_bound_discovery(self, graph_petersen, oracle):
        """Scenario 4: Hoffman bound chi >= 1 - lambda_1 / lambda_n achieves exact sharpness on Petersen."""
        spec = oracle.adjacency_spectrum(graph_petersen)
        lambda_1 = spec[0]   # 3.0
        lambda_n = spec[-1]  # -2.0

        assert np.isclose(lambda_1, 3.0)
        assert np.isclose(lambda_n, -2.0)

        hoffman_bound = 1.0 - (lambda_1 / lambda_n)  # 1 - (3 / -2) = 1 + 1.5 = 2.5
        exact_chi = oracle.chromatic_number_exact(graph_petersen)  # 3

        # Exact sharpness: ceiling(2.5) == 3 == chi(Petersen)
        assert np.ceil(hoffman_bound) == exact_chi

    def test_application_scenario_grotzsch_refutation_of_triangle_free_3_colorability(
        self, graph_grotzsch, oracle
    ):
        """Scenario 5: Grotzsch graph (Mycielski 4) refutes 'Triangle-free ==> chi <= 3' with chi = 4."""
        assert graph_grotzsch.number_of_nodes() == 11
        assert graph_grotzsch.number_of_edges() == 20
        assert oracle.is_triangle_free(graph_grotzsch) is True
        assert oracle.chromatic_number_exact(graph_grotzsch) == 4

        # Grotzsch graph proves that triangle-free graphs can have chromatic number >= 4
        assert oracle.clique_number(graph_grotzsch) == 2
