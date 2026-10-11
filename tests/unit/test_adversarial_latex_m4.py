"""Adversarial stress-test suite for Milestone 4: LaTeX Preprint Generator & Artifact Validator.

Authored by empirical challenger challenger_m4_1 to stress-test:
1. LatexPreprintGenerator:
   - Diverse result types: ProofResult (proven, unproven), SieveResult (C5, survived),
     empty conjectures, complex nested AST expressions, special LaTeX characters.
   - Boundary graphs: order 0 (K0), order 1 (K1), large graphs (order 50).
   - Structural balance: Every output file must have strictly matching \\begin and \\end
     tags, balanced curly braces {}, and terminating semicolons in TikZ figures.
2. ArtifactValidator:
   - Intentionally broken LaTeX content: unbalanced environments, unmatched braces,
     missing required files, malformed TikZ environments.
   - 100% detection rate: validate_latex and validate_latex_directory must catch all flaws
     with is_valid == False and informative error strings.
   - 2-tuple unpacking: valid, errs = validator.validate_latex(...).
"""

from __future__ import annotations

import os
from pathlib import Path
import random
import re
from typing import Any, Dict, List
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.export.latex_generator import (
    LatexPreprintGenerator,
    LaTeXPreprintGenerator,
    _escape_latex_text,
    _format_pmatrix,
)
from autonomous_math.export.validator import (
    ArtifactValidationResult,
    ArtifactValidator,
    OutputSyntaxValidator,
    check_latex_brace_balance,
    check_latex_environments,
    check_tikz_environments,
    strip_latex_comments,
    validate_latex_directory_structure,
)
from autonomous_math.prover.dag import (
    DeductionStep,
    LemmaDAG,
    ProofNode,
)
from autonomous_math.prover.search import ProofResult
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    SieveResult,
    build_c5_counterexample_certificate,
)


# ============================================================================
# ADVERSARIAL GENERATOR FIXTURES & HELPERS
# ============================================================================

def assert_bundle_syntactically_balanced(out_dir: Path) -> None:
    """Rigorous verification of balanced tags, braces, and TikZ in every file."""
    assert out_dir.is_dir(), f"Expected directory at {out_dir}"
    
    tex_files = list(out_dir.rglob("*.tex"))
    assert len(tex_files) >= 8, f"Expected at least 8 tex files, found {len(tex_files)}"
    
    for tex_path in tex_files:
        content = tex_path.read_text(encoding="utf-8")
        clean = strip_latex_comments(content)
        
        # Check brace balance
        br_ok, br_errs = check_latex_brace_balance(content)
        assert br_ok is True, f"Unbalanced braces in {tex_path.name}: {br_errs}"
        
        # Check environment balance
        env_ok, env_errs = check_latex_environments(content)
        assert env_ok is True, f"Unbalanced environments in {tex_path.name}: {env_errs}"
        
        # Check TikZ if present
        if r"\begin{tikzpicture}" in clean:
            tz_ok, tz_errs = check_tikz_environments(content)
            assert tz_ok is True, f"Malformed TikZ in {tex_path.name}: {tz_errs}"

    # Directory level validation
    val_res = ArtifactValidator.validate_latex_directory(out_dir)
    assert val_res.is_valid is True, f"Directory validation failed: {val_res.errors}"


# ============================================================================
# 1. LATEX PREPRINT GENERATOR ADVERSARIAL SUITE
# ============================================================================

class TestLatexPreprintGeneratorAdversarial:
    """Adversarial stress-testing of LatexPreprintGenerator."""

    def test_generator_with_empty_conjecture(self, tmp_path):
        """Empty conjecture with empty string statements and minimal attributes."""
        empty_conj = Conjecture(
            id="empty_conjecture_001",
            statement="",
            lhs_expr=ConstantNode(0.0),
            rel="<=",
            rhs_expr=ConstantNode(0.0),
            complexity=1,
        )
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(empty_conj, output_dir=tmp_path / "empty_paper")
        assert_bundle_syntactically_balanced(out_dir)

    def test_generator_with_none_conjecture(self, tmp_path):
        """Generator invoked with None conjecture."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(None, output_dir=tmp_path / "none_paper")
        assert_bundle_syntactically_balanced(out_dir)

    def test_generator_with_latex_special_characters_in_conjecture(self, tmp_path):
        """Conjecture statement containing LaTeX special characters (_, %, &, $, #)."""
        special_stmt = r"chi_chromatic & omega_clique <= 50% #special $formula$ ~ test"
        conj = Conjecture(
            id="special_chars_001",
            statement=special_stmt,
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(50.0),
            guard_predicate="has_property_%_&_$",
            complexity=5,
        )
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(conj, output_dir=tmp_path / "special_paper")
        assert_bundle_syntactically_balanced(out_dir)

        # Check main.tex title and formulation
        main_tex = (out_dir / "main.tex").read_text()
        assert r"\%" in main_tex or "%" not in main_tex  # Escaped or clean

        form_tex = (out_dir / "sections" / "formulation.tex").read_text()
        assert_bundle_syntactically_balanced(out_dir)

    def test_generator_with_deeply_nested_complex_expression(self, tmp_path):
        """Conjecture with deeply nested AST expression (depth 5)."""
        nested_expr = BinaryOpNode(
            "/",
            BinaryOpNode(
                "+",
                BinaryOpNode(
                    "*",
                    InvariantNode("order"),
                    InvariantNode("max_degree"),
                ),
                ConstantNode(1.0),
            ),
            BinaryOpNode(
                "+",
                InvariantNode("independence_number"),
                ConstantNode(1.0),
            ),
        )
        conj = Conjecture(
            id="nested_bound_001",
            statement="complex_nested_expression",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=nested_expr,
            complexity=9,
        )
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(conj, output_dir=tmp_path / "nested_paper")
        assert_bundle_syntactically_balanced(out_dir)

    def test_generator_with_order_0_boundary_graph(self, tmp_path):
        """Boundary graph: Order 0 (null graph, 0 vertices, 0 edges, empty adjacency matrix)."""
        cert = CounterexampleCertificate(
            conjecture_id="null_graph_test",
            graph_order=0,
            graph_size=0,
            adjacency_matrix=[],
            edges=[],
            invariants={"order": 0, "size": 0},
            refutation_witness={"type": "null_graph", "details": "order 0"},
            verification_hash="hash_order_0",
        )
        sieve_res = SieveResult(
            status="REFUTED",
            conjecture=Conjecture(
                id="null_graph_conj",
                statement="n >= 1",
                lhs_expr=ConstantNode(0.0),
                rel=">=",
                rhs_expr=ConstantNode(1.0),
                complexity=1,
            ),
            tested_instances_count=1,
            counterexample_certificate=cert,
        )
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(sieve_res, output_dir=tmp_path / "order_0_paper")
        assert_bundle_syntactically_balanced(out_dir)

        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert r"\begin{pmatrix}\end{pmatrix}" in cert_tex

    def test_generator_with_order_1_boundary_graph(self, tmp_path):
        """Boundary graph: Order 1 (single isolated vertex K1, [[0]] adjacency matrix)."""
        cert = CounterexampleCertificate(
            conjecture_id="k1_graph_test",
            graph_order=1,
            graph_size=0,
            adjacency_matrix=[[0]],
            edges=[],
            invariants={"order": 1, "size": 0, "max_degree": 0},
            refutation_witness={"type": "isolated_vertex", "details": "order 1"},
            verification_hash="hash_order_1",
        )
        sieve_res = SieveResult(
            status="REFUTED",
            conjecture=Conjecture(
                id="k1_graph_conj",
                statement="m >= 1",
                lhs_expr=ConstantNode(0.0),
                rel=">=",
                rhs_expr=ConstantNode(1.0),
                complexity=1,
            ),
            tested_instances_count=1,
            counterexample_certificate=cert,
        )
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(sieve_res, output_dir=tmp_path / "order_1_paper")
        assert_bundle_syntactically_balanced(out_dir)

        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert r"\begin{pmatrix}" in cert_tex
        assert r"\end{pmatrix}" in cert_tex

    def test_generator_with_large_order_50_graph(self, tmp_path):
        """Large graph: Order 50 graph with 50x50 adjacency matrix and 50 invariants."""
        n = 50
        # Generate symmetric adjacency matrix for order 50
        random.seed(42)
        adj = [[0] * n for _ in range(n)]
        edges = []
        for i in range(n):
            for j in range(i + 1, n):
                if random.random() < 0.2:
                    adj[i][j] = 1
                    adj[j][i] = 1
                    edges.append((i, j))

        invariants = {f"inv_{i}": round(i * 1.5, 2) for i in range(50)}
        cert = CounterexampleCertificate(
            conjecture_id="large_order_50_test",
            graph_order=n,
            graph_size=len(edges),
            adjacency_matrix=adj,
            edges=edges,
            invariants=invariants,
            refutation_witness={"type": "large_erdos_renyi", "details": f"order {n}, edges {len(edges)}"},
            verification_hash="hash_order_50_secure",
        )
        sieve_res = SieveResult(
            status="REFUTED",
            conjecture=Conjecture(
                id="large_graph_conj",
                statement="large graph bound",
                lhs_expr=ConstantNode(50.0),
                rel="<=",
                rhs_expr=ConstantNode(10.0),
                complexity=2,
            ),
            tested_instances_count=500,
            counterexample_certificate=cert,
        )

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(sieve_res, output_dir=tmp_path / "order_50_paper")
        assert_bundle_syntactically_balanced(out_dir)

        # Check that 50 rows were rendered
        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert r"\begin{pmatrix}" in cert_tex
        assert r"\end{pmatrix}" in cert_tex
        assert cert_tex.count(r"\\") >= 49

    def test_generator_with_complex_multi_step_dag(self, tmp_path):
        """ProofResult with complex 5-step DAG containing branching premises."""
        dag = LemmaDAG(root_node_id="target")
        target_node = ProofNode(
            node_id="target",
            label=r"\chi \le \Delta + 1",
            statement_latex=r"\chi(G) \le \Delta(G) + 1",
            statement_lean="chi <= Delta + 1",
            node_type="TARGET_CONJECTURE",
            status="PROVEN",
        )
        lemma1 = ProofNode(
            node_id="lemma_ordering",
            label="Degree Ordering Lemma",
            statement_latex=r"v_1, \dots, v_n \text{ ordering}",
            statement_lean="ordering",
            node_type="LEMMA",
            status="PROVEN",
        )
        lemma2 = ProofNode(
            node_id="lemma_greedy",
            label="Greedy Color Allocation",
            statement_latex=r"c(v_i) \le \deg(v_i) + 1",
            statement_lean="color_le_deg",
            node_type="LEMMA",
            status="PROVEN",
        )
        axiom1 = ProofNode(
            node_id="axiom_well_ordering",
            label="Well-Ordering Principle",
            statement_latex=r"\mathbb{N} \text{ well-ordered}",
            statement_lean="well_ordered",
            node_type="AXIOM",
            status="PROVEN",
        )

        dag.add_node(target_node)
        dag.add_node(lemma1)
        dag.add_node(lemma2)
        dag.add_node(axiom1)

        step1 = DeductionStep(
            step_id="s1",
            target_node_id="lemma_ordering",
            premise_node_ids=["axiom_well_ordering"],
            rule_type="AXIOM_APPLICATION",
            rule_name="Well-Ordering",
            justification="Establish greedy vertex sequence",
            z3_verified=True,
            skeptic_approved=True,
        )
        step2 = DeductionStep(
            step_id="s2",
            target_node_id="lemma_greedy",
            premise_node_ids=["lemma_ordering"],
            rule_type="INDUCTION",
            rule_name="Greedy Coloring Step",
            justification="Upper bound color assignment by back-degree",
            z3_verified=True,
            skeptic_approved=True,
        )
        step3 = DeductionStep(
            step_id="s3",
            target_node_id="target",
            premise_node_ids=["lemma_greedy"],
            rule_type="MODUS_PONENS",
            rule_name="Max-Degree Specialization",
            justification="Max-degree dominates all vertex degrees",
            z3_verified=True,
            skeptic_approved=True,
        )

        dag.add_step(step1)
        dag.add_step(step2)
        dag.add_step(step3)

        proof_res = ProofResult(
            conjecture=Conjecture(
                id="greedy_bound_conj",
                statement="chi <= Delta + 1",
                lhs_expr=InvariantNode("chromatic_number"),
                rel="<=",
                rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
                complexity=3,
            ),
            dag=dag,
            status="PROVEN",
            minimal_proof_tree=[step1, step2, step3],
            critique_summary={"audited_steps": 3, "rejected_steps": 0},
        )

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(proof_res, output_dir=tmp_path / "complex_dag_paper")
        assert_bundle_syntactically_balanced(out_dir)

        # Check proof section has all 3 steps
        proof_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "Step 1" in proof_tex
        assert "Step 2" in proof_tex
        assert "Step 3" in proof_tex
        assert "Well-Ordering" in proof_tex

    def test_generator_with_survived_sieve_result(self, tmp_path):
        """SieveResult that SURVIVED without refutation certificate."""
        conj = Conjecture(
            id="surviving_turans_bound",
            statement="m <= n^2 / 4",
            lhs_expr=InvariantNode("size"),
            rel="<=",
            rhs_expr=BinaryOpNode("/", BinaryOpNode("^", InvariantNode("order"), ConstantNode(2.0)), ConstantNode(4.0)),
            guard_predicate="is_triangle_free",
            complexity=4,
        )
        sieve_res = SieveResult(
            status="SURVIVED",
            conjecture=conj,
            tested_instances_count=1000,
            counterexample_certificate=None,
        )

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(sieve_res, output_dir=tmp_path / "survived_paper")
        assert_bundle_syntactically_balanced(out_dir)

        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "survived all empirical tests" in cert_tex


# ============================================================================
# 2. ARTIFACT VALIDATOR ADVERSARIAL SUITE
# ============================================================================

class TestArtifactValidatorAdversarial:
    """Adversarial stress-testing of ArtifactValidator and OutputSyntaxValidator."""

    def test_validator_detects_unclosed_environment(self):
        """Detect unclosed LaTeX environment."""
        snippets = [
            "\\begin{theorem}\nContent.\n",
            "\\begin{document}\n\\begin{proof}\nStep 1.\n\\end{document}\n",
            "\\begin{tabular}{cc}\n1 & 2 \\\\\n",
            "\\begin{pmatrix}\n1 & 0 \\\\\n",
        ]
        for s in snippets:
            valid, errs = ArtifactValidator.validate_latex_content(s)
            assert valid is False
            assert len(errs) > 0
            assert any("unclosed" in e.lower() or "unbalanced" in e.lower() or "mismatched" in e.lower() for e in errs)

    def test_validator_detects_mismatched_environment_nesting(self):
        """Detect mismatched nesting order: \\begin{A}\\begin{B}\\end{A}\\end{B}."""
        bad_nesting = (
            "\\begin{theorem}\n"
            "\\begin{proof}\n"
            "Deduction.\n"
            "\\end{theorem}\n"
            "\\end{proof}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(bad_nesting)
        assert valid is False
        assert any("mismatched" in e.lower() for e in errs)

    def test_validator_detects_unexpected_end_environment(self):
        """Detect \\end{env} without preceding \\begin{env}."""
        bad_end = (
            "\\section{Intro}\n"
            "Some content.\n"
            "\\end{lemma}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(bad_end)
        assert valid is False
        assert any("unexpected" in e.lower() or "unbalanced" in e.lower() for e in errs)

    def test_validator_detects_unclosed_curly_brace(self):
        """Detect unclosed opening curly brace {."""
        snippets = [
            "\\title{Autonomous Discovery",
            "\\textbf{bold text",
            "\\frac{numerator}{denominator",
            "\\texorpdfstring{text}{bookmark",
        ]
        for s in snippets:
            valid, errs = ArtifactValidator.validate_latex_content(s)
            assert valid is False
            assert any("unclosed" in e.lower() or "unbalanced" in e.lower() for e in errs)

    def test_validator_detects_unexpected_closing_brace(self):
        """Detect unexpected closing curly brace }."""
        snippets = [
            "\\title{Autonomous Discovery}}",
            "Some plain text with closing brace } in body.",
            "\\begin{document}\n}\\end{document}",
        ]
        for s in snippets:
            valid, errs = ArtifactValidator.validate_latex_content(s)
            assert valid is False
            assert any("unmatched closing" in e.lower() for e in errs)

    def test_validator_handles_escaped_braces_and_comments_accurately(self):
        """Ensure escaped braces and braces in comments are handled without false positives."""
        valid_latex = (
            "\\begin{document}\n"
            "% This is a comment with unmatched { and } and \\begin{dummy}\n"
            "The set $S = \\{ x \\in X \\mid x > 0 \\}$ is non-empty.\n"
            "Literal percent: 50\\% reduction.\n"
            "\\end{document}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(valid_latex)
        assert valid is True
        assert len(errs) == 0

    def test_validator_detects_unclosed_escaped_braces_edge_case(self):
        """Genuine unclosed brace adjacent to escaped braces."""
        bad_latex = (
            "\\begin{document}\n"
            "The set $S = \\{ x \\in X \\mid x > 0 \\}\n"
            "\\end{document}\n"
            "Extra { without match."
        )
        valid, errs = ArtifactValidator.validate_latex_content(bad_latex)
        assert valid is False
        assert any("unclosed" in e.lower() for e in errs)

    def test_validator_detects_malformed_tikz_environments(self):
        """Detect malformed TikZ syntax."""
        # Case 1: Unclosed tikzpicture
        unclosed_tikz = (
            "\\begin{tikzpicture}\n"
            "\\node (a) at (0, 0) {A};\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(unclosed_tikz)
        assert valid is False
        assert any("tikzpicture" in e.lower() or "unclosed" in e.lower() for e in errs)

        # Case 2: Missing semicolon in \node
        no_semi_node = (
            "\\begin{tikzpicture}\n"
            "\\node (a) at (0, 0) {A}\n"
            "\\end{tikzpicture}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(no_semi_node)
        assert valid is False
        assert any("semicolon" in e.lower() for e in errs)

        # Case 3: Missing semicolon in \draw
        no_semi_draw = (
            "\\begin{tikzpicture}\n"
            "\\draw (0, 0) -- (1, 1)\n"
            "\\end{tikzpicture}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(no_semi_draw)
        assert valid is False
        assert any("semicolon" in e.lower() for e in errs)

    def test_validator_detects_missing_directory_files(self, tmp_path):
        """Detect missing required files in LaTeX manuscript directory."""
        bundle_dir = tmp_path / "broken_bundle"
        bundle_dir.mkdir()

        # Only create main.tex
        (bundle_dir / "main.tex").write_text("\\begin{document}\\end{document}")

        valid, errs = ArtifactValidator.validate_latex_directory(bundle_dir)
        assert valid is False
        assert any("preamble.tex" in e for e in errs)
        assert any("references.bib" in e for e in errs)
        assert any("lemma_dag.tex" in e for e in errs)

    def test_validator_detects_broken_input_reference_in_main(self, tmp_path):
        """Detect \\input{nonexistent_section} reference in main.tex."""
        bundle_dir = tmp_path / "input_broken_bundle"
        bundle_dir.mkdir()

        (bundle_dir / "preamble.tex").write_text("% preamble")
        (bundle_dir / "references.bib").write_text("% bib")
        fig_dir = bundle_dir / "figures"
        fig_dir.mkdir()
        (fig_dir / "lemma_dag.tex").write_text("\\begin{tikzpicture}\\end{tikzpicture}")

        (bundle_dir / "main.tex").write_text(
            "\\input{preamble}\n"
            "\\input{sections/nonexistent_file}\n"
            "\\begin{document}\\end{document}\n"
        )

        valid, errs = ArtifactValidator.validate_latex_directory(bundle_dir)
        assert valid is False
        assert any("nonexistent_file" in e for e in errs)

    def test_validator_tuple_unpacking_and_rich_model_properties(self):
        """Verify ArtifactValidationResult supports tuple unpacking, indexing, bool conversion, and to_dict."""
        # Success result
        res_ok = ArtifactValidationResult.valid(details={"key": "val"}, warnings=["minor"])
        assert bool(res_ok) is True
        assert res_ok.is_valid is True
        assert len(res_ok.errors) == 0
        assert len(res_ok) == 2
        
        valid_val, err_list = res_ok
        assert valid_val is True
        assert err_list == []
        assert res_ok[0] is True
        assert res_ok[1] == []
        assert res_ok.to_dict()["is_valid"] is True

        # Failure result
        res_fail = ArtifactValidationResult.invalid(errors=["Error 1", "Error 2"])
        assert bool(res_fail) is False
        assert res_fail.is_valid is False
        assert len(res_fail.errors) == 2
        
        valid_val2, err_list2 = res_fail
        assert valid_val2 is False
        assert err_list2 == ["Error 1", "Error 2"]
        assert res_fail[0] is False
        assert res_fail[1] == ["Error 1", "Error 2"]

        # Out-of-bounds index
        with pytest.raises(IndexError):
            _ = res_fail[2]

    def test_validator_rejects_nonexistent_directory_or_file(self, tmp_path):
        """Reject non-existent directory or file cleanly without unhandled crash."""
        res = ArtifactValidator.validate_latex(tmp_path / "phantom_dir")
        assert res.is_valid is False
        assert any("does not exist" in e for e in res.errors)

        valid, errs = res
        assert valid is False
        assert len(errs) > 0

    def test_generator_in_memory_dictionary_return(self):
        """When output_dir is None, generate_manuscript returns Dict[str, str] without disk I/O."""
        gen = LatexPreprintGenerator()
        files = gen.generate_manuscript(output_dir=None)
        assert isinstance(files, dict)
        expected_keys = {
            "main.tex",
            "preamble.tex",
            "references.bib",
            "figures/lemma_dag.tex",
            "sections/abstract.tex",
            "sections/introduction.tex",
            "sections/formulation.tex",
            "sections/methods.tex",
            "sections/results.tex",
            "sections/proof_or_cert.tex",
        }
        assert expected_keys.issubset(set(files.keys()))
        for rel_path, content in files.items():
            assert isinstance(content, str)
            assert len(content) > 0
            if rel_path.endswith(".tex"):
                valid, errs = ArtifactValidator.validate_latex_content(content)
                assert valid is True, f"In-memory file {rel_path} failed validation: {errs}"

    def test_generator_polymorphic_dict_target(self, tmp_path):
        """Generator handles raw dictionary targets representing SieveResult or ProofResult."""
        raw_dict = {
            "status": "REFUTED",
            "conjecture": {
                "statement": "chi <= 2",
                "statement_latex": r"\chi(G) \le 2",
                "guard_predicate": "triangle_free",
            },
            "counterexample_certificate": {
                "graph_order": 5,
                "graph_size": 5,
                "adjacency_matrix": [[0, 1, 0, 0, 1], [1, 0, 1, 0, 0], [0, 1, 0, 1, 0], [0, 0, 1, 0, 1], [1, 0, 0, 1, 0]],
                "invariants": {"triangle_count": 0, "chromatic_number": 3},
                "refutation_witness": {"type": "odd_cycle", "details": [0, 1, 2, 3, 4, 0]},
                "verification_hash": "c5_dict_hash_123",
            },
        }
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(raw_dict, output_dir=tmp_path / "dict_target_paper")
        assert_bundle_syntactically_balanced(out_dir)

    def test_validator_asterisk_and_nested_environments(self):
        """Asterisked environments (align*, equation*) and deep nesting validate cleanly."""
        nested_tex = (
            "\\begin{document}\n"
            "\\begin{theorem}\n"
            "Here is the bound:\n"
            "\\begin{equation*}\n"
            "  \\chi(G) \\le \\Delta(G) + 1\n"
            "\\end{equation*}\n"
            "\\begin{proof}\n"
            "\\begin{enumerate}\n"
            "\\item Step 1: Base case.\n"
            "\\end{enumerate}\n"
            "\\end{proof}\n"
            "\\end{theorem}\n"
            "\\end{document}\n"
        )
        valid, errs = ArtifactValidator.validate_latex_content(nested_tex)
        assert valid is True
        assert len(errs) == 0

    def test_validate_export_bundle_full_pipeline(self, tmp_path):
        """validate_export_bundle correctly validates directory containing preprint."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(None, output_dir=tmp_path / "bundle_valid")
        res = ArtifactValidator.validate_export_bundle(out_dir)
        assert res.is_valid is True
        assert len(res.errors) == 0

