"""Unit test suite for Lean 4 Comparator Scaffolding & Exporter (Feature 14)
and Lean 4 / Comparator JSON Syntax Validator (Feature 15).
"""

from __future__ import annotations

import json
from pathlib import Path
import pytest
from pydantic import ValidationError

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
)
from autonomous_math.export.comparator_schema import ComparatorChallengeSpec
from autonomous_math.export.latex_generator import LatexPreprintGenerator
from autonomous_math.export.lean_generator import (
    ChallengeArtifacts,
    Lean4ChallengeGenerator,
    LeanComparatorGenerator,
)
from autonomous_math.export.validator import (
    ArtifactValidationResult,
    ArtifactValidator,
    OutputSyntaxValidator,
)
from autonomous_math.prover.dag import LemmaDAG, ProofNode
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
        id="greedy_coloring_bound",
        statement="chi <= Delta + 1",
        lhs_expr=InvariantNode("chromatic_number"),
        rel="<=",
        rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        complexity=3,
    )


@pytest.fixture
def proven_proof_result(sample_conjecture) -> ProofResult:
    """Sample PROVEN ProofResult."""
    dag = LemmaDAG(root_node_id="root")
    dag.add_node(ProofNode(
        node_id="root",
        label="chi <= Delta + 1",
        statement_latex=r"\chi \le \Delta + 1",
        statement_lean="chi <= Delta + 1",
        node_type="TARGET_CONJECTURE",
        status="PROVEN",
    ))
    return ProofResult(
        conjecture=sample_conjecture,
        dag=dag,
        status="PROVEN",
        minimal_proof_tree=[],
        critique_summary={},
    )


@pytest.fixture
def c5_refuted_result() -> SieveResult:
    """Sample REFUTED SieveResult with C5 witness."""
    conj = Conjecture(
        id="triangle_free_not_two_colorable",
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


# ============================================================================
# 1. COMPARATOR CHALLENGE SPEC MODEL UNIT TESTS (FEATURE 14)
# ============================================================================

class TestComparatorChallengeSpecModel:
    """Tests for ComparatorChallengeSpec Pydantic V2 model."""

    def test_spec_instantiation_defaults(self):
        """Model instantiates with required fields and correct defaults."""
        spec = ComparatorChallengeSpec(
            challenge_module="ComparatorChallenges.GreedyColoring",
            solution_module="OAI.Combinatorics.Coloring.Main",
            theorem_names=["OAI.GreedyColoring.chromatic_le_max_degree_add_one"],
        )
        assert spec.challenge_module == "ComparatorChallenges.GreedyColoring"
        assert spec.solution_module == "OAI.Combinatorics.Coloring.Main"
        assert len(spec.theorem_names) == 1
        assert spec.definition_names == []
        assert spec.permitted_axioms == ["propext", "Quot.sound", "Classical.choice"]
        assert spec.enable_nanoda is False

    def test_spec_dict_and_json_roundtrip(self):
        """Model serializes to dict and JSON and reconstructs faithfully."""
        spec = ComparatorChallengeSpec(
            challenge_module="ComparatorChallenges.BrooksBound",
            solution_module="OAI.Combinatorics.Brooks.Main",
            theorem_names=["OAI.BrooksBound.brooks_theorem"],
        )
        d = spec.to_dict()
        assert d["challenge_module"] == spec.challenge_module
        assert d["permitted_axioms"] == spec.permitted_axioms

        json_str = spec.to_json()
        assert isinstance(json_str, str)
        reconstructed = ComparatorChallengeSpec.from_json(json_str)
        assert reconstructed.challenge_module == spec.challenge_module
        assert reconstructed.theorem_names == spec.theorem_names

    def test_spec_validation_rejects_missing_required_keys(self):
        """Model rejects missing required fields."""
        with pytest.raises(ValidationError):
            ComparatorChallengeSpec.model_validate({
                "solution_module": "OAI.Test.Main",
                "theorem_names": ["thm1"],
            })

    def test_spec_validation_rejects_invalid_types(self):
        """Model rejects invalid types for enable_nanoda and theorem_names."""
        with pytest.raises(ValidationError):
            ComparatorChallengeSpec(
                challenge_module="Mod",
                solution_module="Sol",
                theorem_names="not_a_list",  # Must be list
            )


# ============================================================================
# 2. LEAN GENERATOR UNIT TESTS (FEATURE 14)
# ============================================================================

class TestLeanComparatorGenerator:
    """Tests for LeanComparatorGenerator producing Lean 4 artifacts."""

    def test_generator_alias_compatibility(self):
        """Verify LeanComparatorGenerator and Lean4ChallengeGenerator aliases exist."""
        assert LeanComparatorGenerator is Lean4ChallengeGenerator

    def test_generate_from_proven_result(self, tmp_path, proven_proof_result):
        """Verify generator produces valid .lean and .json companion files for proven result."""
        gen = LeanComparatorGenerator()
        json_path, lean_path = gen.generate(proven_proof_result, output_dir=tmp_path / "lean_proven")

        assert json_path.exists()
        assert lean_path.exists()
        assert json_path.suffix == ".json"
        assert lean_path.suffix == ".lean"

        # Validate Lean source structure
        lean_text = lean_path.read_text()
        assert "import Mathlib" in lean_text
        assert "namespace OAI" in lean_text
        assert "theorem" in lean_text
        assert "sorry" in lean_text

        # Validate JSON content
        spec = ComparatorChallengeSpec.from_json(json_path.read_text())
        assert len(spec.theorem_names) > 0
        assert spec.permitted_axioms == ["propext", "Quot.sound", "Classical.choice"]

        # Validate through ArtifactValidator
        res = ArtifactValidator.validate_lean(lean_path, json_path)
        assert res.is_valid is True, f"Validation errors: {res.errors}"

    def test_generate_from_refuted_result(self, tmp_path, c5_refuted_result):
        """Verify generator produces existential counterexample challenge for refuted result."""
        gen = LeanComparatorGenerator()
        json_path, lean_path = gen.generate(c5_refuted_result, output_dir=tmp_path / "lean_refuted")

        assert json_path.exists()
        assert lean_path.exists()

        lean_text = lean_path.read_text()
        assert "import Mathlib" in lean_text
        assert "namespace OAI" in lean_text
        assert "∃" in lean_text or "not" in lean_text.lower() or "¬" in lean_text
        assert "CliqueFree 3" in lean_text
        assert "Colorable 2" in lean_text

        res = ArtifactValidator.validate_lean(lean_path, json_path)
        assert res.is_valid is True, f"Validation errors: {res.errors}"

    def test_unproven_conjecture_handling(self, tmp_path):
        """Verify generator handles unproven conjecture without crashing."""
        conj = Conjecture(
            id="open_hadwiger",
            statement="Hadwiger k=7",
            lhs_expr=ConstantNode(7.0),
            rel="<=",
            rhs_expr=ConstantNode(7.0),
            complexity=5,
        )
        unproven = ProofResult(
            conjecture=conj,
            dag=LemmaDAG(root_node_id="root"),
            status="UNPROVEN",
            minimal_proof_tree=[],
        )

        gen = Lean4ChallengeGenerator()
        json_path, lean_path = gen.generate_challenge(conj, proof_result=unproven, output_dir=tmp_path / "unproven")
        assert json_path.exists()
        assert lean_path.exists()

    def test_raw_dict_conjecture_input(self, tmp_path):
        """Verify generator handles raw dict input seamlessly."""
        raw_dict = {
            "conjecture": {"id": "c_cli", "statement": "chi <= Delta + 1"},
            "status": "PROVEN",
        }
        gen = LeanComparatorGenerator()
        json_path, lean_path = gen.generate(raw_dict, output_dir=tmp_path / "raw")
        assert json_path.exists()
        assert lean_path.exists()
        assert "chromaticNumber" in lean_path.read_text()


# ============================================================================
# 3. LEAN & COMPARATOR JSON VALIDATOR UNIT TESTS (FEATURE 15)
# ============================================================================

class TestArtifactValidatorLean:
    """Tests for ArtifactValidator on Lean 4 source and comparator JSON schemas."""

    def test_clean_lean_source_validates_true(self):
        """Clean Lean 4 source code validates successfully."""
        clean = (
            "import Mathlib\n\n"
            "namespace OAI\n\n"
            "namespace TestModule\n\n"
            "theorem sample_bound : True := by\n"
            "  sorry\n\n"
            "end TestModule\n\n"
            "end OAI\n"
        )
        res = ArtifactValidator.validate_lean_source(clean)
        assert res.is_valid is True
        assert len(res.errors) == 0

        # Tuple unpacking test
        valid, errs = res
        assert valid is True
        assert len(errs) == 0

    def test_clean_comparator_json_validates_true(self):
        """Clean comparator JSON validates successfully."""
        raw_json = json.dumps({
            "challenge_module": "ComparatorChallenges.Test",
            "solution_module": "OAI.Test.Main",
            "theorem_names": ["OAI.Test.sample_theorem"],
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": False,
        })
        res = ArtifactValidator.validate_lean_comparator_json(raw_json)
        assert res.is_valid is True
        assert len(res.errors) == 0

    def test_missing_mathlib_import_detected(self):
        """Lean code missing 'import Mathlib' is flagged."""
        corrupt = (
            "namespace OAI\n\n"
            "theorem t : True := by sorry\n\n"
            "end OAI\n"
        )
        res = ArtifactValidator.validate_lean_source(corrupt)
        assert res.is_valid is False
        assert any("Mathlib" in e for e in res.errors)

    def test_missing_oai_namespace_detected(self):
        """Lean code missing 'namespace OAI' is flagged."""
        corrupt = (
            "import Mathlib\n\n"
            "namespace Custom\n\n"
            "theorem t : True := by sorry\n\n"
            "end Custom\n"
        )
        res = ArtifactValidator.validate_lean_source(corrupt)
        assert res.is_valid is False
        assert any("namespace OAI" in e for e in res.errors)

    def test_mismatched_namespace_count_detected(self):
        """Mismatched namespace open/close count is flagged."""
        corrupt = (
            "import Mathlib\n\n"
            "namespace OAI\n\n"
            "namespace Sub\n\n"
            "theorem t : True := by sorry\n\n"
            "end OAI\n"  # Only 1 end for 2 namespaces
        )
        res = ArtifactValidator.validate_lean_source(corrupt)
        assert res.is_valid is False
        assert any("namespace" in e.lower() for e in res.errors)

    def test_missing_theorem_declaration_detected(self):
        """Lean source with no theorem or def is flagged."""
        corrupt = (
            "import Mathlib\n\n"
            "namespace OAI\n\n"
            "-- No theorem\n\n"
            "end OAI\n"
        )
        res = ArtifactValidator.validate_lean_source(corrupt)
        assert res.is_valid is False
        assert any("theorem or def" in e.lower() for e in res.errors)

    def test_missing_sorry_placeholder_detected(self):
        """Lean formalization scaffold missing 'sorry' placeholder is flagged."""
        corrupt = (
            "import Mathlib\n\n"
            "namespace OAI\n\n"
            "theorem t : True := trivial\n\n"
            "end OAI\n"
        )
        res = ArtifactValidator.validate_lean_source(corrupt)
        assert res.is_valid is False
        assert any("sorry" in e.lower() for e in res.errors)

    def test_comparator_json_missing_keys_detected(self):
        """Comparator JSON missing required keys is flagged."""
        corrupt_json = json.dumps({
            "challenge_module": "ComparatorChallenges.Test",
            # Missing solution_module, theorem_names, etc.
        })
        res = ArtifactValidator.validate_lean_comparator_json(corrupt_json)
        assert res.is_valid is False
        assert any("missing required keys" in e.lower() for e in res.errors)

    def test_comparator_json_missing_classical_axioms_detected(self):
        """Comparator JSON missing classical axioms triad is flagged."""
        corrupt_json = json.dumps({
            "challenge_module": "ComparatorChallenges.Test",
            "solution_module": "OAI.Test.Main",
            "theorem_names": ["OAI.Test.t"],
            "definition_names": [],
            "permitted_axioms": ["Classical.choice"],  # Missing propext, Quot.sound
            "enable_nanoda": False,
        })
        res = ArtifactValidator.validate_lean_comparator_json(corrupt_json)
        assert res.is_valid is False
        assert any("classical axioms" in e.lower() for e in res.errors)

    def test_cross_file_theorem_name_mismatch_detected(self, tmp_path):
        """Theorem declared in JSON but missing in Lean source is flagged."""
        lean_file = tmp_path / "Mismatch.lean"
        lean_file.write_text(
            "import Mathlib\n\n"
            "namespace OAI\n\n"
            "namespace Mismatch\n\n"
            "theorem actual_theorem_name : True := by\n"
            "  sorry\n\n"
            "end Mismatch\n\n"
            "end OAI\n"
        )

        json_file = tmp_path / "Mismatch.json"
        json_file.write_text(json.dumps({
            "challenge_module": "ComparatorChallenges.Mismatch",
            "solution_module": "OAI.Mismatch.Main",
            "theorem_names": ["OAI.Mismatch.different_theorem_name"],  # Mismatch!
            "definition_names": [],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": False,
        }))

        res = ArtifactValidator.validate_lean(lean_file, json_file)
        assert res.is_valid is False
        assert any("different_theorem_name" in e for e in res.errors)


# ============================================================================
# 4. EXPORT BUNDLE VALIDATOR UNIT TESTS (FEATURE 15)
# ============================================================================

class TestArtifactValidatorExportBundle:
    """Tests for ArtifactValidator.validate_export_bundle across full delivery sets."""

    def test_valid_bundle_validation_succeeds(self, tmp_path, proven_proof_result):
        """Bundle containing valid LaTeX and Lean deliverables passes validation."""
        bundle_dir = tmp_path / "bundle"
        bundle_dir.mkdir()

        # Generate LaTeX
        latex_gen = LatexPreprintGenerator()
        latex_gen.generate(proven_proof_result, output_dir=bundle_dir / "paper")

        # Generate Lean
        lean_gen = LeanComparatorGenerator()
        lean_gen.generate(proven_proof_result, output_dir=bundle_dir / "lean")

        res = ArtifactValidator.validate_export_bundle(bundle_dir)
        assert res.is_valid is True
        assert len(res.errors) == 0

    def test_bundle_with_corrupt_latex_fails(self, tmp_path, proven_proof_result):
        """Bundle with corrupt LaTeX environment is rejected."""
        bundle_dir = tmp_path / "corrupt_latex_bundle"
        bundle_dir.mkdir()

        latex_gen = LatexPreprintGenerator()
        latex_dir = latex_gen.generate(proven_proof_result, output_dir=bundle_dir / "paper")

        lean_gen = LeanComparatorGenerator()
        lean_gen.generate(proven_proof_result, output_dir=bundle_dir / "lean")

        # Corrupt main.tex
        (latex_dir / "main.tex").write_text("\\begin{document}\n\\begin{theorem}\nClaim.\n\\end{document}")

        res = ArtifactValidator.validate_export_bundle(bundle_dir)
        assert res.is_valid is False
        assert any("theorem" in e.lower() for e in res.errors)

    def test_bundle_with_corrupt_lean_fails(self, tmp_path, proven_proof_result):
        """Bundle with corrupt Lean Mathlib import is rejected."""
        bundle_dir = tmp_path / "corrupt_lean_bundle"
        bundle_dir.mkdir()

        latex_gen = LatexPreprintGenerator()
        latex_gen.generate(proven_proof_result, output_dir=bundle_dir / "paper")

        lean_gen = LeanComparatorGenerator()
        _, lean_path = lean_gen.generate(proven_proof_result, output_dir=bundle_dir / "lean")

        # Corrupt Lean file (remove Mathlib import)
        content = lean_path.read_text().replace("import Mathlib", "-- removed import")
        lean_path.write_text(content)

        res = ArtifactValidator.validate_export_bundle(bundle_dir)
        assert res.is_valid is False
        assert any("Mathlib" in e for e in res.errors)

    def test_empty_bundle_directory_fails(self, tmp_path):
        """Empty bundle directory is rejected with descriptive error."""
        empty_dir = tmp_path / "empty_bundle"
        empty_dir.mkdir()

        res = ArtifactValidator.validate_export_bundle(empty_dir)
        assert res.is_valid is False
        assert any("No LaTeX or Lean export artifacts found" in e for e in res.errors)
