"""Unit test suite for Academic LaTeX Preprint Generator (Feature 13)
and LaTeX Syntax/Completeness Validator (Feature 15).
"""

from __future__ import annotations

import json
from pathlib import Path
import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
)
from autonomous_math.export.latex_generator import (
    LatexPreprintGenerator,
    LaTeXPreprintGenerator,
)
from autonomous_math.export.validator import (
    ArtifactValidationResult,
    ArtifactValidator,
    OutputSyntaxValidator,
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
# FIXTURES
# ============================================================================

@pytest.fixture
def sample_conjecture() -> Conjecture:
    """Sample chromatic bound conjecture: chi <= Delta + 1."""
    return Conjecture(
        id="chi_le_delta_plus_one",
        statement="chi <= Delta + 1",
        lhs_expr=InvariantNode("chromatic_number"),
        rel="<=",
        rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        complexity=3,
    )


@pytest.fixture
def c5_refuted_result() -> SieveResult:
    """Sample SieveResult refuting triangle-free 2-colorability on C5."""
    conj = Conjecture(
        id="tf_two_colorable",
        statement="is_triangle_free ==> chi <= 2",
        lhs_expr=InvariantNode("chromatic_number"),
        rel="<=",
        rhs_expr=ConstantNode(2.0),
        guard_predicate="is_triangle_free",
        complexity=2,
    )
    cert = build_c5_counterexample_certificate(conjecture_id=conj.id)
    return SieveResult(
        status="REFUTED",
        conjecture=conj,
        tested_instances_count=50,
        counterexample_certificate=cert,
    )


@pytest.fixture
def proven_proof_result(sample_conjecture) -> ProofResult:
    """Sample ProofResult with multi-step LemmaDAG."""
    dag = LemmaDAG(root_node_id="root")
    root_node = ProofNode(
        node_id="root",
        label=r"\chi \le \Delta + 1",
        statement_latex=r"\chi(G) \le \Delta(G) + 1",
        statement_lean="chi <= Delta + 1",
        node_type="TARGET_CONJECTURE",
        status="PROVEN",
    )
    greedy_node = ProofNode(
        node_id="greedy_bound",
        label="Greedy Coloring Bound",
        statement_latex=r"\chi(G) \le \Delta(G) + 1",
        statement_lean="chi <= Delta + 1",
        node_type="AXIOM",
        status="PROVEN",
    )
    dag.add_node(root_node)
    dag.add_node(greedy_node)

    step = DeductionStep(
        step_id="step_greedy",
        target_node_id="root",
        premise_node_ids=["greedy_bound"],
        rule_type="AXIOM_APPLICATION",
        rule_name="Greedy Coloring Axiom",
        justification="Immediate deduction by Greedy Bound axiom",
        z3_verified=True,
        skeptic_approved=True,
    )
    dag.add_step(step)

    return ProofResult(
        conjecture=sample_conjecture,
        dag=dag,
        status="PROVEN",
        minimal_proof_tree=[step],
        critique_summary={"audited_steps": 1, "rejected_steps": 0},
    )


@pytest.fixture
def unproven_proof_result() -> ProofResult:
    """Sample UNPROVEN ProofResult with empty proof tree."""
    conj = Conjecture(
        id="hadwiger_7",
        statement="Hadwiger conjecture k=7",
        lhs_expr=ConstantNode(7.0),
        rel="<=",
        rhs_expr=ConstantNode(7.0),
        complexity=5,
    )
    return ProofResult(
        conjecture=conj,
        dag=LemmaDAG(root_node_id="root"),
        status="UNPROVEN",
        minimal_proof_tree=[],
        critique_summary={"reason": "Search depth budget exhausted"},
    )


# ============================================================================
# 1. LATEX GENERATOR UNIT TESTS (FEATURE 13)
# ============================================================================

class TestLatexPreprintGenerator:
    """Tests for LatexPreprintGenerator producing publication-ready preprints."""

    def test_generator_alias_compatibility(self):
        """Verify LatexPreprintGenerator and LaTeXPreprintGenerator aliases exist."""
        assert LatexPreprintGenerator is LaTeXPreprintGenerator

    def test_generate_from_refuted_sieve_result(self, tmp_path, c5_refuted_result):
        """Verify generation of manuscript from refuted conjecture with C5 certificate."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(c5_refuted_result, output_dir=tmp_path / "c5_paper")

        assert out_dir.exists()
        assert (out_dir / "main.tex").exists()
        assert (out_dir / "preamble.tex").exists()
        assert (out_dir / "references.bib").exists()
        assert (out_dir / "figures" / "lemma_dag.tex").exists()
        assert (out_dir / "sections" / "abstract.tex").exists()
        assert (out_dir / "sections" / "introduction.tex").exists()
        assert (out_dir / "sections" / "formulation.tex").exists()
        assert (out_dir / "sections" / "proof_or_cert.tex").exists()

        # Verify C5 certificate matrix rendering
        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "pmatrix" in cert_tex or "matrix" in cert_tex
        assert "odd_cycle" in cert_tex or "Odd Cycle" in cert_tex or "C_5" in cert_tex or "C5" in cert_tex

        # Verify generated output passes syntax validation
        res = ArtifactValidator.validate_latex(out_dir)
        assert res.is_valid is True, f"Validation errors: {res.errors}"

    def test_generate_from_proven_proof_result(self, tmp_path, proven_proof_result):
        """Verify generation of manuscript from proven result with TikZ DAG."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(proven_proof_result, output_dir=tmp_path / "proven_paper")

        assert (out_dir / "main.tex").exists()
        dag_tex = (out_dir / "figures" / "lemma_dag.tex").read_text()
        assert "\\begin{tikzpicture}" in dag_tex
        assert "\\end{tikzpicture}" in dag_tex
        assert "target_node" in dag_tex
        assert "axiom_node" in dag_tex

        res = ArtifactValidator.validate_latex(out_dir)
        assert res.is_valid is True, f"Validation errors: {res.errors}"

    def test_generate_from_unproven_proof_result_graceful(self, tmp_path, unproven_proof_result):
        """Verify generator handles UNPROVEN results gracefully without crashing."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate(unproven_proof_result, output_dir=tmp_path / "unproven_paper")

        assert (out_dir / "main.tex").exists()
        res = ArtifactValidator.validate_latex(out_dir)
        assert res.is_valid is True, f"Validation errors: {res.errors}"

    def test_generate_manuscript_direct_call(self, tmp_path, sample_conjecture):
        """Verify generate_manuscript interface method works directly with conjecture."""
        gen = LatexPreprintGenerator()
        out_dir = gen.generate_manuscript(conjecture=sample_conjecture, output_dir=tmp_path / "direct_paper")
        assert (out_dir / "main.tex").exists()
        res = ArtifactValidator.validate_latex(out_dir)
        assert res.is_valid is True


# ============================================================================
# 2. LATEX VALIDATOR UNIT TESTS (FEATURE 15)
# ============================================================================

class TestArtifactValidatorLatex:
    """Tests for ArtifactValidator and OutputSyntaxValidator on LaTeX artifacts."""

    def test_validator_alias_compatibility(self):
        """Verify OutputSyntaxValidator is an alias of ArtifactValidator."""
        assert OutputSyntaxValidator is ArtifactValidator

    def test_clean_latex_content_validates_true(self):
        """Clean LaTeX snippet validates with zero errors."""
        clean = (
            "\\begin{document}\n"
            "\\begin{theorem}\nClaim.\n\\end{theorem}\n"
            "\\end{document}\n"
        )
        res = ArtifactValidator.validate_latex_content(clean)
        assert res.is_valid is True
        assert len(res.errors) == 0

        # Tuple unpacking test
        valid, errs = res
        assert valid is True
        assert len(errs) == 0

    def test_corrupt_latex_unclosed_environment_detected(self):
        """Unclosed LaTeX environment is detected with descriptive message."""
        corrupt = (
            "\\begin{document}\n"
            "\\begin{theorem}\nClaim.\n"
            "\\end{document}\n"
        )
        valid, errs = OutputSyntaxValidator.validate_latex_content(corrupt)
        assert valid is False
        assert len(errs) > 0
        assert any("theorem" in e.lower() for e in errs)

    def test_mismatched_environment_closure_detected(self):
        """Mismatched environment closure (begin{proof} closed by end{lemma}) is detected."""
        corrupt = (
            "\\begin{document}\n"
            "\\begin{proof}\nProof body.\n\\end{lemma}\n"
            "\\end{document}\n"
        )
        res = ArtifactValidator.validate_latex_content(corrupt)
        assert res.is_valid is False
        assert any("mismatched" in e.lower() for e in res.errors)

    def test_unbalanced_curly_braces_detected(self):
        """Unbalanced curly braces (missing closing brace) are detected."""
        corrupt = "\\section{Introduction\nSome text."
        res = ArtifactValidator.validate_latex_content(corrupt)
        assert res.is_valid is False
        assert any("unclosed '{'" in e for e in res.errors)

    def test_extra_closing_brace_detected(self):
        """Extra closing brace '}' is detected with line position."""
        corrupt = "\\section{Introduction}}\nSome text."
        res = ArtifactValidator.validate_latex_content(corrupt)
        assert res.is_valid is False
        assert any("unmatched closing brace '}'" in e.lower() for e in res.errors)

    def test_escaped_braces_do_not_cause_false_positive(self):
        """Escaped braces \\{ and \\} are not counted as structural block delimiters."""
        content = (
            "\\begin{document}\n"
            "The set $S = \\{ v \\in V \\mid \\text{deg}(v) \\ge 3 \\}$ is non-empty.\n"
            "\\end{document}\n"
        )
        res = ArtifactValidator.validate_latex_content(content)
        assert res.is_valid is True
        assert len(res.errors) == 0

    def test_latex_comments_do_not_cause_false_positive(self):
        """Environments and braces inside comments % are ignored."""
        content = (
            "\\begin{document}\n"
            "% \\begin{theorem}\n"
            "% } unmatched closing in comment\n"
            "Real content.\n"
            "\\end{document}\n"
        )
        res = ArtifactValidator.validate_latex_content(content)
        assert res.is_valid is True
        assert len(res.errors) == 0

    def test_tikz_environment_semicolon_validation(self):
        """TikZ environments missing command-terminating semicolons are detected."""
        corrupt_tikz = (
            "\\begin{tikzpicture}\n"
            "  \\node (a) at (0, 0) {Root}\n"  # Missing semicolon
            "\\end{tikzpicture}\n"
        )
        res = ArtifactValidator.validate_latex_content(corrupt_tikz)
        assert res.is_valid is False
        assert any("semicolon" in e.lower() for e in res.errors)

    def test_missing_required_files_in_directory(self, tmp_path):
        """Validator flags missing required files in LaTeX preprint directory."""
        incomplete_dir = tmp_path / "incomplete"
        incomplete_dir.mkdir()
        (incomplete_dir / "main.tex").write_text("\\begin{document}\\end{document}")
        # Missing preamble.tex, references.bib, figures/lemma_dag.tex

        res = ArtifactValidator.validate_latex(incomplete_dir)
        assert res.is_valid is False
        assert any("preamble.tex" in e for e in res.errors)
        assert any("references.bib" in e for e in res.errors)
        assert any("lemma_dag.tex" in e for e in res.errors)

    def test_broken_input_reference_detected(self, tmp_path):
        """Validator detects \\input{non_existent} references in main.tex."""
        tex_dir = tmp_path / "broken_input"
        tex_dir.mkdir()
        (tex_dir / "main.tex").write_text("\\input{sections/missing}\n\\begin{document}\\end{document}")
        (tex_dir / "preamble.tex").write_text("% preamble")
        (tex_dir / "references.bib").write_text("% bib")
        fig_dir = tex_dir / "figures"
        fig_dir.mkdir()
        (fig_dir / "lemma_dag.tex").write_text("\\begin{tikzpicture}\\end{tikzpicture}")

        res = ArtifactValidator.validate_latex(tex_dir)
        assert res.is_valid is False
        assert any("sections/missing" in e for e in res.errors)

    def test_nonexistent_path_rejected(self, tmp_path):
        """Validator rejects non-existent paths gracefully."""
        res = ArtifactValidator.validate_latex(tmp_path / "does_not_exist")
        assert res.is_valid is False
        assert any("does not exist" in e for e in res.errors)
