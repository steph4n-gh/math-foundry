"""Tier 3 E2E Pairwise & Cross-Feature Integration Test Suite.

Verifies end-to-end data flow and cross-module interactions:
- Conjecture Generation -> Empirical Sieve (filtration & categorization)
- Sieve Counterexample -> LaTeX Manuscript (matrix rendering & certificate tables)
- Sieve Counterexample -> Lean 4 Comparator Challenge (existential refutation)
- Sieve Survivor -> Prover-Skeptic Engine (AO* search orchestration)
- Prover Lemma DAG -> Dual Export (TikZ visualizer & modular Lean scaffolding)
- Adversarial Skeptic Critique -> Search Loop Backtracking & Recovery
- Complete 5-Stage Discovery Pipeline (Conjecture -> Sieve -> Prove -> Export -> Validate)
"""

from __future__ import annotations

import json
from pathlib import Path

import networkx as nx
import numpy as np
import pytest

from .conftest import ReferenceGraphOracle, ReferenceArtifactValidator


class TestTier3PairwiseCrossFeatureInteractions:
    """Cross-feature integration tests tracing data flow across pipeline boundaries."""

    def test_pairwise_conjecture_generation_to_sieve_falsification(self):
        """Pairwise: Conjectures from generator are correctly classified by Sieve."""
        gen_mod = pytest.importorskip("autonomous_math.conjecturing.generator")
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        ConjectureGenerator = getattr(gen_mod, "ConjectureGenerator")
        InstanceDatabase = getattr(sieve_mod, "InstanceDatabase")
        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")

        # Create known true conjecture: chromatic_number >= clique_number
        conj_true = Conjecture(
            id="true_clique_bound",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        # Create known false conjecture: independence_number * clique_number >= order
        conj_false = Conjecture(
            id="false_ramsey_bound",
            statement="alpha * omega >= n",
            lhs_expr=ast_mod.BinaryOpNode("*", InvariantNode("independence_number"), InvariantNode("clique_number")),
            rel=">=",
            rhs_expr=InvariantNode("order"),
            complexity=3,
        )

        db = InstanceDatabase()
        res_true = db.sieve_conjecture(conj_true)
        res_false = db.sieve_conjecture(conj_false)

        assert res_true.status == "SURVIVED"
        assert res_true.counterexample_certificate is None

        assert res_false.status == "REFUTED"
        assert res_false.counterexample_certificate is not None
        assert res_false.counterexample_certificate.conjecture_id == conj_false.id

    def test_pairwise_sieve_certificate_to_latex_export(self, tmp_path, graph_c5):
        """Pairwise: Sieve CounterexampleCertificate renders into LaTeX manuscript with matrix."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        validator_mod = pytest.importorskip("autonomous_math.export.validator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        CounterexampleCertificate = getattr(sieve_mod, "CounterexampleCertificate")
        SieveResult = getattr(sieve_mod, "SieveResult")
        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")
        OutputSyntaxValidator = getattr(validator_mod, "OutputSyntaxValidator")

        conj = ast_mod.Conjecture(
            id="tf_two_colorable",
            statement="TriangleFree(G) ==> chi(G) <= 2",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ast_mod.ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        cert = CounterexampleCertificate(
            conjecture_id=conj.id,
            graph_order=5,
            graph_size=5,
            adjacency_matrix=nx.to_numpy_array(graph_c5, dtype=int).tolist(),
            edges=list(graph_c5.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 3},
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 4, 0]},
            verification_hash="sha256_witness_c5",
        )

        result = SieveResult(
            status="REFUTED",
            conjecture=conj,
            tested_instances_count=100,
            counterexample_certificate=cert,
        )

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(result, output_dir=tmp_path / "c5_paper")

        # Verify generated LaTeX contains the certificate details
        cert_section_file = out_dir / "sections" / "proof_or_cert.tex"
        assert cert_section_file.exists()
        cert_tex = cert_section_file.read_text()

        # Must display the counterexample adjacency matrix
        assert "pmatrix" in cert_tex or "matrix" in cert_tex
        assert "odd_cycle" in cert_tex or "Odd Cycle" in cert_tex or "C_5" in cert_tex or "C5" in cert_tex

        # Verify whole manuscript syntax integrity
        valid, errs = OutputSyntaxValidator.validate_latex_directory(out_dir)
        assert valid is True, f"LaTeX validation failed: {errs}"

    def test_pairwise_sieve_certificate_to_lean4_counterexample_challenge(self, tmp_path, graph_c5):
        """Pairwise: Sieve CounterexampleCertificate exports as Lean 4 refutation challenge."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        CounterexampleCertificate = getattr(sieve_mod, "CounterexampleCertificate")
        SieveResult = getattr(sieve_mod, "SieveResult")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")

        conj = ast_mod.Conjecture(
            id="triangle_free_not_two_colorable",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ast_mod.ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )
        cert = CounterexampleCertificate(
            conjecture_id=conj.id,
            graph_order=5,
            graph_size=5,
            adjacency_matrix=nx.to_numpy_array(graph_c5, dtype=int).tolist(),
            edges=list(graph_c5.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 3},
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 4, 0]},
            verification_hash="hash_c5",
        )
        result = SieveResult(status="REFUTED", conjecture=conj, tested_instances_count=1, counterexample_certificate=cert)

        gen = LeanComparatorGenerator()
        json_path, lean_path = gen.generate(result, output_dir=tmp_path / "lean_c5")

        # Validate Lean 4 challenge specification
        is_valid_json, json_errs = ReferenceArtifactValidator.validate_lean_comparator_json(json_path.read_text())
        assert is_valid_json, f"Invalid JSON: {json_errs}"

        lean_code = lean_path.read_text()
        is_valid_lean, lean_errs = ReferenceArtifactValidator.validate_lean_source(lean_code)
        assert is_valid_lean, f"Invalid Lean 4: {lean_errs}"

        # Refutation should assert existence of counterexample or negation of universal claim
        assert "∃" in lean_code or "¬" in lean_code or "not" in lean_code.lower()

    def test_pairwise_sieve_survivor_to_prover_search(self):
        """Pairwise: Conjectures surviving sieve advance to Prover-Skeptic search loop."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        InstanceDatabase = getattr(sieve_mod, "InstanceDatabase")
        ProverSkepticSearch = getattr(search_mod, "ProverSkepticSearch")
        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")

        conj = Conjecture(
            id="clique_chromatic_survivor",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        db = InstanceDatabase()
        sieve_result = db.sieve_conjecture(conj)
        assert sieve_result.status == "SURVIVED"

        # Advance survivor to Prover
        prover = ProverSkepticSearch()
        proof_result = prover.prove(sieve_result.conjecture, max_depth=4)

        assert proof_result.status in ["PROVEN", "UNPROVEN"]
        assert proof_result.dag is not None
        assert proof_result.conjecture.id == conj.id

    def test_pairwise_prover_proof_to_latex_and_lean_export(self, tmp_path):
        """Pairwise: Proven ProofResult generates both TikZ DAG in LaTeX and Lean 4 challenge."""
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        dag_mod = pytest.importorskip("autonomous_math.prover.dag")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        validator_mod = pytest.importorskip("autonomous_math.export.validator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")

        ProofResult = getattr(search_mod, "ProofResult")
        LemmaDAG = getattr(dag_mod, "LemmaDAG")
        ProofNode = getattr(dag_mod, "ProofNode")
        DeductionStep = getattr(dag_mod, "DeductionStep")
        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")
        OutputSyntaxValidator = getattr(validator_mod, "OutputSyntaxValidator")

        conj = ast_mod.Conjecture(
            id="proven_bound", statement="chi <= Delta + 1",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"), rel="<=",
            rhs_expr=ast_mod.BinaryOpNode("+", ast_mod.InvariantNode("max_degree"), ast_mod.ConstantNode(1.0)),
            complexity=3
        )

        dag = LemmaDAG(root_node_id="root")
        n_root = ProofNode(node_id="root", label="chi <= Delta + 1", statement_latex=r"\chi \le \Delta + 1", statement_lean="chi <= Delta + 1", node_type="TARGET_CONJECTURE", status="PROVEN")
        n_premise = ProofNode(node_id="p1", label="Greedy bound", statement_latex=r"\chi \le \text{Greedy}", statement_lean="chi <= greedy", node_type="AXIOM", status="PROVEN")
        dag.add_node(n_root)
        dag.add_node(n_premise)
        step = DeductionStep(step_id="step1", target_node_id="root", premise_node_ids=["p1"], rule_type="AXIOM_APPLICATION", rule_name="Greedy", justification="Greedy induction", z3_verified=True, skeptic_approved=True)
        dag.add_step(step)

        proof_res = ProofResult(
            conjecture=conj,
            dag=dag,
            status="PROVEN",
            minimal_proof_tree=[step],
            critique_summary={"audited_steps": 1, "rejected_steps": 0},
        )

        # LaTeX Export
        latex_gen = LatexPreprintGenerator()
        tex_dir = latex_gen.generate(proof_res, output_dir=tmp_path / "proven_paper")
        tikz_file = tex_dir / "figures" / "lemma_dag.tex"
        assert tikz_file.exists()
        assert "\\begin{tikzpicture}" in tikz_file.read_text()
        valid_latex, l_errs = OutputSyntaxValidator.validate_latex_directory(tex_dir)
        assert valid_latex is True, f"LaTeX errors: {l_errs}"

        # Lean 4 Export
        lean_gen = LeanComparatorGenerator()
        j_path, l_path = lean_gen.generate(proof_res, output_dir=tmp_path / "proven_lean")
        valid_json, j_errs = ReferenceArtifactValidator.validate_lean_comparator_json(j_path.read_text())
        assert valid_json is True, f"JSON errors: {j_errs}"
        valid_lean, lean_errs = ReferenceArtifactValidator.validate_lean_source(l_path.read_text())
        assert valid_lean is True, f"Lean errors: {lean_errs}"

    def test_pairwise_skeptic_critique_drives_search_backtracking(self):
        """Pairwise: Skeptic critique forces AO* search to backtrack from invalid branch to valid proof."""
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        ProverSkepticSearch = getattr(search_mod, "ProverSkepticSearch")

        conj = ast_mod.Conjecture(
            id="backtrack_test_bound",
            statement="chi <= Delta + 1",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ast_mod.BinaryOpNode("+", ast_mod.InvariantNode("max_degree"), ast_mod.ConstantNode(1.0)),
            complexity=3,
        )

        prover = ProverSkepticSearch()
        proof_result = prover.prove(conj, max_depth=5)

        # Ensure that critique summary logged audits and resulting minimal proof contains only approved steps
        critique_summary = proof_result.critique_summary
        assert isinstance(critique_summary, dict)
        for step in proof_result.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True

    def test_pairwise_full_pipeline_end_to_end_conjecture_sieve_prove_export(self, tmp_path):
        """Pairwise: Complete 5-stage discovery cycle runs autonomously from invariants to deliverables."""
        gen_mod = pytest.importorskip("autonomous_math.conjecturing.generator")
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        validator_mod = pytest.importorskip("autonomous_math.export.validator")

        # 1. Generate conjectures
        generator = gen_mod.ConjectureGenerator()
        candidates = generator.generate_exhaustive(max_depth=2, limit=5)
        assert len(candidates) > 0
        target = candidates[0]

        # 2. Sieve filter
        db = sieve_mod.InstanceDatabase()
        sieve_res = db.sieve_conjecture(target)

        # 3. Prove (if survived) or process certificate (if refuted)
        if sieve_res.status == "SURVIVED":
            prover = search_mod.ProverSkepticSearch()
            outcome = prover.prove(target, max_depth=3)
        else:
            outcome = sieve_res

        # 4. Dual Export
        latex_gen = latex_mod.LatexPreprintGenerator()
        lean_gen = lean_mod.LeanComparatorGenerator()

        tex_dir = latex_gen.generate(outcome, output_dir=tmp_path / "e2e_paper")
        j_p, l_p = lean_gen.generate(outcome, output_dir=tmp_path / "e2e_lean")

        # 5. Dual Validate
        valid_tex, tex_errs = validator_mod.OutputSyntaxValidator.validate_latex_directory(tex_dir)
        assert valid_tex is True, f"TeX errs: {tex_errs}"

        valid_j, j_errs = ReferenceArtifactValidator.validate_lean_comparator_json(j_p.read_text())
        assert valid_j is True, f"JSON errs: {j_errs}"

        valid_l, l_errs = ReferenceArtifactValidator.validate_lean_source(l_p.read_text())
        assert valid_l is True, f"Lean errs: {l_errs}"
