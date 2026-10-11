"""Unit tests for Feature 16 (Unified Orchestration CLI) and Feature 17 (Discovery Demos).

Verifies:
- All CLI subcommands: conjecture, sieve, prove, export, demo, discover.
- Flag parsing, default arguments, custom limits, guard predicates, and export formats.
- Polymorphic JSON input and output file generation.
- Runnable discovery scenarios: c5_refutation, greedy_coloring_bound, clique_chromatic_bound.
- Robust error handling: invalid flags, missing arguments, non-existent files, malformed JSON.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
from typing import Any, Dict, List
import pytest

from autonomous_math.cli.main import main
from autonomous_math.cli.demo import run_demo
from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
)
from autonomous_math.export.validator import ArtifactValidator
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    SieveResult,
    build_c5_counterexample_certificate,
)


# ============================================================================
# FIXTURES
# ============================================================================

@pytest.fixture
def sample_conjecture_dict() -> Dict[str, Any]:
    """Sample full AST conjecture serialized to dictionary."""
    conj = Conjecture(
        id="conj_greedy_bound",
        statement="chromatic_number <= max_degree + 1",
        lhs_expr=InvariantNode("chromatic_number"),
        rel="<=",
        rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
        complexity=3,
    )
    return conj.to_dict()


@pytest.fixture
def sample_sieve_result_dict(sample_conjecture_dict) -> Dict[str, Any]:
    """Sample serialized SieveResult dictionary."""
    return {
        "status": "SURVIVED",
        "conjecture": sample_conjecture_dict,
        "tested_instances_count": 50,
        "counterexample_certificate": None,
        "execution_time_ms": 1.5,
    }


@pytest.fixture
def sample_proof_result_dict(sample_conjecture_dict) -> Dict[str, Any]:
    """Sample serialized ProofResult dictionary."""
    return {
        "status": "PROVEN",
        "conjecture": sample_conjecture_dict,
        "minimal_proof_tree": [],
        "dag": {"root_node_id": "root"},
        "critique_summary": {"status": "approved", "reason": "Verified bound"},
    }


# ============================================================================
# 1. CONJECTURE SUBCOMMAND TESTS
# ============================================================================

class TestCliConjectureSubcommand:
    """Tests for `autonomous-math conjecture` subcommand."""

    def test_cli_conjecture_default_options(self, tmp_path):
        """Generates candidate conjectures with default limit (5) and writes to JSON."""
        out_file = tmp_path / "conjectures.json"
        exit_code = main(["conjecture", "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

        data = json.loads(out_file.read_text())
        assert isinstance(data, list)
        assert len(data) == 5
        for item in data:
            assert "id" in item
            assert "statement" in item
            assert "rel" in item
            assert "complexity" in item

    def test_cli_conjecture_custom_limit(self, tmp_path):
        """Parses custom --limit flag and limits generated candidates."""
        out_file = tmp_path / "conjectures_custom.json"
        exit_code = main(["conjecture", "--limit", "2", "--output", str(out_file)])
        assert exit_code == 0
        data = json.loads(out_file.read_text())
        assert len(data) == 2

    def test_cli_conjecture_guard_predicate_filtering(self, tmp_path):
        """Filters generated conjectures by premise guard predicate."""
        out_file = tmp_path / "conjectures_triangle_free.json"
        exit_code = main([
            "conjecture", "--limit", "5", "--guard", "is_triangle_free", "--output", str(out_file)
        ])
        assert exit_code == 0
        data = json.loads(out_file.read_text())
        assert len(data) > 0
        for item in data:
            guard = item.get("guard_predicate")
            assert guard == "is_triangle_free" or (
                isinstance(guard, dict) and guard.get("property_name") == "is_triangle_free"
            ) or "triangle_free" in item.get("statement", "").lower()

    def test_cli_conjecture_archetypes_strategy(self, tmp_path):
        """Generates foundational mathematical archetypes (Brooks, Turan, Ramsey)."""
        out_file = tmp_path / "archetypes.json"
        exit_code = main(["conjecture", "--strategy", "archetypes", "--output", str(out_file)])
        assert exit_code == 0
        data = json.loads(out_file.read_text())
        assert len(data) >= 5
        statements = [item["statement"] for item in data]
        assert any("max_degree" in s or "Delta" in s for s in statements)

    def test_cli_conjecture_stdout_fallback(self, capsys):
        """Outputs JSON to stdout when --output is omitted."""
        exit_code = main(["conjecture", "--limit", "2"])
        assert exit_code == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert isinstance(data, list)
        assert len(data) == 2


# ============================================================================
# 2. SIEVE SUBCOMMAND TESTS
# ============================================================================

class TestCliSieveSubcommand:
    """Tests for `autonomous-math sieve` subcommand."""

    def test_cli_sieve_with_full_ast_conjecture_list(self, tmp_path, sample_conjecture_dict):
        """Ingests list of full AST conjectures and produces SieveResult models."""
        in_file = tmp_path / "conjectures.json"
        in_file.write_text(json.dumps([sample_conjecture_dict]))
        out_file = tmp_path / "sieve_results.json"

        exit_code = main(["sieve", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

        results = json.loads(out_file.read_text())
        assert isinstance(results, list)
        assert len(results) == 1
        assert results[0]["status"] == "SURVIVED"
        assert results[0]["tested_instances_count"] > 0

    def test_cli_sieve_with_single_conjecture_object(self, tmp_path, sample_conjecture_dict):
        """Supports polymorphic input where file contains a single JSON object (not a list)."""
        in_file = tmp_path / "single_conj.json"
        in_file.write_text(json.dumps(sample_conjecture_dict))
        out_file = tmp_path / "sieve_results_single.json"

        exit_code = main(["sieve", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        results = json.loads(out_file.read_text())
        assert isinstance(results, list)
        assert len(results) == 1

    def test_cli_sieve_with_minimal_statement_conjecture(self, tmp_path):
        """Ingests minimal dict representation and falsifies false conjecture."""
        in_file = tmp_path / "minimal_conj.json"
        in_file.write_text(json.dumps([
            {"id": "c1", "statement": "alpha * omega >= n", "rel": ">=", "complexity": 3}
        ]))
        out_file = tmp_path / "sieve_refuted.json"

        exit_code = main(["sieve", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

        results = json.loads(out_file.read_text())
        assert len(results) == 1
        assert results[0]["status"] == "REFUTED"
        assert results[0]["counterexample_certificate"] is not None
        cert = results[0]["counterexample_certificate"]
        assert "adjacency_matrix" in cert
        assert cert["graph_order"] in {5, 10}  # Refuted on C5 or Petersen

    def test_cli_sieve_tier1_only_mode(self, tmp_path, sample_conjecture_dict):
        """Executes fast Tier 1 database sieve when --tier1-only is supplied."""
        in_file = tmp_path / "tier1_in.json"
        in_file.write_text(json.dumps([sample_conjecture_dict]))
        out_file = tmp_path / "tier1_out.json"

        exit_code = main(["sieve", "--input", str(in_file), "--output", str(out_file), "--tier1-only"])
        assert exit_code == 0
        assert out_file.exists()

    def test_cli_sieve_cegar_max_rounds(self, tmp_path, sample_conjecture_dict):
        """Accepts and parses --cegar-max-rounds configuration."""
        in_file = tmp_path / "cegar_in.json"
        in_file.write_text(json.dumps([sample_conjecture_dict]))
        out_file = tmp_path / "cegar_out.json"

        exit_code = main([
            "sieve", "--input", str(in_file), "--output", str(out_file), "--cegar-max-rounds", "3"
        ])
        assert exit_code == 0


# ============================================================================
# 3. PROVE SUBCOMMAND TESTS
# ============================================================================

class TestCliProveSubcommand:
    """Tests for `autonomous-math prove` subcommand."""

    def test_cli_prove_single_conjecture(self, tmp_path):
        """Ingests target conjecture and synthesizes deductive proof."""
        in_file = tmp_path / "to_prove.json"
        in_file.write_text(json.dumps({
            "id": "c_prove", "statement": "chi <= Delta + 1", "rel": "<=", "complexity": 3
        }))
        out_file = tmp_path / "proof.json"

        exit_code = main(["prove", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

        result = json.loads(out_file.read_text())
        assert result["status"] == "PROVEN"
        assert len(result["minimal_proof_tree"]) > 0

    def test_cli_prove_with_conjecture_list(self, tmp_path, sample_conjecture_dict):
        """Ingests list of candidate conjectures for batch proof search."""
        in_file = tmp_path / "conjectures_batch.json"
        in_file.write_text(json.dumps([sample_conjecture_dict]))
        out_file = tmp_path / "proofs_batch.json"

        exit_code = main(["prove", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        results = json.loads(out_file.read_text())
        assert isinstance(results, (list, dict))

    def test_cli_prove_from_sieve_result_input(self, tmp_path, sample_sieve_result_dict):
        """Accepts SieveResult JSON and extracts surviving conjecture."""
        in_file = tmp_path / "sieve_res.json"
        in_file.write_text(json.dumps(sample_sieve_result_dict))
        out_file = tmp_path / "proof_from_sieve.json"

        exit_code = main(["prove", "--input", str(in_file), "--output", str(out_file)])
        assert exit_code == 0
        result = json.loads(out_file.read_text())
        assert result["status"] == "PROVEN"

    def test_cli_prove_max_depth_and_timeout_parameters(self, tmp_path):
        """Passes search depth and timeout parameters cleanly."""
        in_file = tmp_path / "to_prove_params.json"
        in_file.write_text(json.dumps({
            "id": "c_params", "statement": "chi <= Delta + 1", "rel": "<=", "complexity": 3
        }))
        out_file = tmp_path / "proof_params.json"

        exit_code = main([
            "prove", "--input", str(in_file), "--output", str(out_file),
            "--max-depth", "4", "--timeout", "5.0"
        ])
        assert exit_code == 0

    def test_cli_prove_unproven_bound_handled_cleanly(self, tmp_path):
        """Handles unproven or budget-exhausted bounds without crash."""
        in_file = tmp_path / "hard_bound.json"
        in_file.write_text(json.dumps({
            "id": "c_hard", "statement": "algebraic_connectivity >= diameter", "rel": ">=", "complexity": 3
        }))
        out_file = tmp_path / "proof_unproven.json"

        exit_code = main(["prove", "--input", str(in_file), "--output", str(out_file), "--max-depth", "1"])
        assert exit_code == 0
        result = json.loads(out_file.read_text())
        assert result["status"] in {"UNPROVEN", "REFUTED"}


# ============================================================================
# 4. EXPORT SUBCOMMAND TESTS
# ============================================================================

class TestCliExportSubcommand:
    """Tests for `autonomous-math export` subcommand."""

    def test_cli_export_from_proof_result(self, tmp_path):
        """Exports LaTeX preprint and Lean 4 artifacts from proof result."""
        res_file = tmp_path / "proof_result.json"
        res_file.write_text(json.dumps({
            "conjecture": {"id": "c_export", "statement": "chi <= Delta + 1"},
            "status": "PROVEN",
            "minimal_proof_tree": []
        }))
        out_dir = tmp_path / "exports"

        exit_code = main(["export", "--input", str(res_file), "--output-dir", str(out_dir)])
        assert exit_code == 0
        assert (out_dir / "main.tex").exists()
        assert (out_dir / "preamble.tex").exists()
        assert (out_dir / "sections").is_dir()
        assert len(list(out_dir.rglob("*.lean"))) > 0

    def test_cli_export_from_sieve_refuted_result(self, tmp_path):
        """Exports C5 counterexample certificate table in LaTeX and Lean challenge."""
        cert = build_c5_counterexample_certificate("conj_triangle_free_2col")
        sieve_res = SieveResult(
            status="REFUTED",
            conjecture=Conjecture(
                id="conj_triangle_free_2col",
                statement="is_triangle_free ==> chi <= 2",
                lhs_expr=InvariantNode("chromatic_number"),
                rel="<=",
                rhs_expr=ConstantNode(2.0),
                guard_predicate="is_triangle_free",
                complexity=2,
            ),
            tested_instances_count=50,
            counterexample_certificate=cert,
        )
        res_file = tmp_path / "sieve_refuted.json"
        res_file.write_text(sieve_res.to_json())
        out_dir = tmp_path / "c5_exports"

        exit_code = main(["export", "--input", str(res_file), "--output-dir", str(out_dir)])
        assert exit_code == 0

        cert_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "pmatrix" in cert_tex or "matrix" in cert_tex
        lean_files = list(out_dir.rglob("*.lean"))
        assert len(lean_files) > 0
        assert "CliqueFree 3" in lean_files[0].read_text() or "triangle" in lean_files[0].read_text().lower()

    def test_cli_export_format_selection(self, tmp_path, sample_proof_result_dict):
        """Supports --format latex, --format lean, and --format all."""
        res_file = tmp_path / "pr.json"
        res_file.write_text(json.dumps(sample_proof_result_dict))

        # LaTeX only
        latex_dir = tmp_path / "only_latex"
        exit_code = main(["export", "--input", str(res_file), "--output-dir", str(latex_dir), "--format", "latex"])
        assert exit_code == 0
        assert (latex_dir / "main.tex").exists()
        assert len(list(latex_dir.rglob("*.lean"))) == 0

        # Lean only
        lean_dir = tmp_path / "only_lean"
        exit_code = main(["export", "--input", str(res_file), "--output-dir", str(lean_dir), "--format", "lean"])
        assert exit_code == 0
        assert len(list(lean_dir.rglob("*.lean"))) > 0
        assert not (lean_dir / "main.tex").exists()

    def test_cli_export_validates_cleanly_with_artifact_validator(self, tmp_path, sample_proof_result_dict):
        """Verifies that export bundle validates 100% cleanly under ArtifactValidator."""
        res_file = tmp_path / "pr_valid.json"
        res_file.write_text(json.dumps(sample_proof_result_dict))
        out_dir = tmp_path / "validated_bundle"

        exit_code = main(["export", "--input", str(res_file), "--output-dir", str(out_dir)])
        assert exit_code == 0
        val_res = ArtifactValidator.validate_export_bundle(out_dir)
        assert val_res.is_valid is True, f"Validation errors: {val_res.errors}"


# ============================================================================
# 5. DEMO SUBCOMMAND TESTS
# ============================================================================

class TestCliDemoSubcommand:
    """Tests for `autonomous-math demo` discovery scenarios (Feature 17)."""

    def test_cli_demo_c5_refutation_exits_zero(self):
        """Executes full C5 refutation discovery demo and exits with code 0."""
        exit_code = main(["demo", "--scenario", "c5_refutation"])
        assert exit_code == 0

    def test_cli_demo_c5_refutation_with_output_dir(self, tmp_path):
        """Executes C5 refutation demo and populates output directory."""
        demo_dir = tmp_path / "c5_demo_out"
        exit_code = main(["demo", "--scenario", "c5_refutation", "--output-dir", str(demo_dir)])
        assert exit_code == 0
        val_res = ArtifactValidator.validate_export_bundle(demo_dir)
        assert val_res.is_valid is True

    def test_cli_demo_greedy_coloring_bound_exits_zero(self):
        """Executes greedy coloring bound proof demo and exits with code 0."""
        exit_code = main(["demo", "--scenario", "greedy_coloring_bound"])
        assert exit_code == 0

    def test_cli_demo_greedy_coloring_bound_with_output_dir(self, tmp_path):
        """Executes greedy coloring bound demo and writes validated deliverables."""
        demo_dir = tmp_path / "greedy_demo_out"
        exit_code = main(["demo", "--scenario", "greedy_coloring_bound", "--output-dir", str(demo_dir)])
        assert exit_code == 0
        val_res = ArtifactValidator.validate_export_bundle(demo_dir)
        assert val_res.is_valid is True

    def test_cli_demo_clique_chromatic_bound(self):
        """Executes clique-chromatic bound scenario and exits with code 0."""
        exit_code = main(["demo", "--scenario", "clique_chromatic_bound"])
        assert exit_code == 0

    def test_cli_demo_unknown_scenario_returns_nonzero(self):
        """Rejects unknown demo scenario with non-zero exit code."""
        exit_code = main(["demo", "--scenario", "nonexistent_scenario_12345"])
        assert exit_code != 0


# ============================================================================
# 6. DISCOVER SUBCOMMAND TESTS
# ============================================================================

class TestCliDiscoverSubcommand:
    """Tests for `autonomous-math discover` end-to-end loop."""

    def test_cli_discover_end_to_end_loop(self, tmp_path):
        """Runs conjecture -> sieve -> prove -> export end-to-end autonomous loop."""
        out_dir = tmp_path / "discovery_run"
        exit_code = main(["discover", "--conjectures-limit", "3", "--output-dir", str(out_dir)])
        assert exit_code == 0
        assert (out_dir / "conjectures.json").exists()
        assert (out_dir / "sieve_results.json").exists()
        assert (out_dir / "proof_results.json").exists()

    def test_cli_discover_with_guard_filter(self, tmp_path):
        """Runs autonomous discovery loop focusing on triangle-free graphs."""
        out_dir = tmp_path / "discovery_tf"
        exit_code = main([
            "discover", "--conjectures-limit", "2", "--guard", "is_triangle_free", "--output-dir", str(out_dir)
        ])
        assert exit_code == 0
        assert (out_dir / "conjectures.json").exists()


# ============================================================================
# 7. ERROR HANDLING & ARGPARSE TESTS
# ============================================================================

class TestCliErrorHandling:
    """Tests argument parsing validation, error codes, and exception boundaries."""

    def test_cli_unknown_global_flag_raises_system_exit(self):
        """Unknown global flag raises SystemExit with non-zero exit code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["--unknown-flag-12345"])
        assert exc_info.value.code != 0

    def test_cli_unknown_subcommand_flag_raises_system_exit(self):
        """Unknown subcommand flag raises SystemExit with non-zero exit code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["conjecture", "--invalid-option-foo"])
        assert exc_info.value.code != 0

    def test_cli_no_arguments_raises_system_exit(self):
        """Invoking CLI with no arguments raises SystemExit with non-zero exit code."""
        with pytest.raises(SystemExit) as exc_info:
            main([])
        assert exc_info.value.code != 0

    def test_cli_sieve_missing_input_raises_system_exit(self, tmp_path):
        """Omitting required --input for sieve raises SystemExit with non-zero code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["sieve", "--output", str(tmp_path / "out.json")])
        assert exc_info.value.code != 0

    def test_cli_prove_missing_input_raises_system_exit(self, tmp_path):
        """Omitting required --input for prove raises SystemExit with non-zero code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["prove", "--output", str(tmp_path / "out.json")])
        assert exc_info.value.code != 0

    def test_cli_export_missing_output_dir_raises_system_exit(self, tmp_path):
        """Omitting required --output-dir for export raises SystemExit with non-zero code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["export", "--input", str(tmp_path / "in.json")])
        assert exc_info.value.code != 0

    def test_cli_demo_missing_scenario_raises_system_exit(self):
        """Omitting required --scenario for demo raises SystemExit with non-zero code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["demo"])
        assert exc_info.value.code != 0

    def test_cli_nonexistent_input_file_returns_nonzero(self, tmp_path):
        """Non-existent input file returns non-zero exit code without uncaught exception."""
        missing = tmp_path / "does_not_exist_999.json"
        exit_code = main(["sieve", "--input", str(missing), "--output", str(tmp_path / "out.json")])
        assert exit_code != 0

    def test_cli_malformed_json_input_file_returns_nonzero(self, tmp_path):
        """Malformed JSON file returns non-zero exit code without crashing."""
        corrupt = tmp_path / "corrupt.json"
        corrupt.write_text("{ unclosed bad json content")
        exit_code = main(["sieve", "--input", str(corrupt), "--output", str(tmp_path / "out.json")])
        assert exit_code != 0

    def test_cli_invalid_type_for_int_flag_raises_system_exit(self):
        """Passing non-integer string to --limit raises SystemExit with non-zero code."""
        with pytest.raises(SystemExit) as exc_info:
            main(["conjecture", "--limit", "not_a_number"])
        assert exc_info.value.code != 0


# ============================================================================
# 8. DIRECT MODULE EXECUTION TESTS
# ============================================================================

class TestCliDirectModuleExecution:
    """Tests execution via sys.argv and direct helper methods."""

    def test_main_default_sys_argv(self, monkeypatch, tmp_path):
        """Calling main() with args=None parses sys.argv cleanly."""
        out_file = tmp_path / "sys_argv_test.json"
        monkeypatch.setattr(
            sys, "argv", ["autonomous_math", "conjecture", "--limit", "1", "--output", str(out_file)]
        )
        exit_code = main()
        assert exit_code == 0
        assert out_file.exists()
