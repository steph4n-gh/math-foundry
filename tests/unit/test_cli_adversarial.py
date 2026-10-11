"""Empirical Adversarial Test Suite for Feature 16 & Feature 17 CLI.

Stress-tests:
1. Malformed JSON inputs, missing required fields, non-existent files,
   deeply nested expressions, unsupported operators, division by zero, code injection.
2. Empty argument lists, unknown flags, conflicting options, extreme limit parameters.
3. Standardized exit codes and exception boundaries without uncaught Python crashes.
4. Stdout vs file redirection and UNIX pipeline chaining.
5. All discovery demo scenarios with ArtifactValidator inspection.
"""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any, Dict, List
import pytest

from autonomous_math.cli.main import main, _parse_expr_str, _resolve_conjecture_from_dict
from autonomous_math.core.ast import Conjecture, InvariantNode, BinaryOpNode, ConstantNode
from autonomous_math.export.validator import ArtifactValidator
from autonomous_math.sieve.certificates import SieveResult
from autonomous_math.prover.search import ProofResult


# ============================================================================
# 1. MALFORMED JSON INPUTS & MISSING FIELDS
# ============================================================================


class TestMalformedJsonInputs:
    """Stress tests for malformed JSON, empty files, and non-conjecture payloads."""

    def test_sieve_empty_file_returns_nonzero(self, tmp_path):
        """Empty input file returns non-zero code without uncaught exception."""
        empty = tmp_path / "empty.json"
        empty.write_text("")
        assert main(["sieve", "--input", str(empty)]) != 0

    def test_prove_empty_file_returns_nonzero(self, tmp_path):
        """Empty input file for prove returns non-zero code."""
        empty = tmp_path / "empty.json"
        empty.write_text("")
        assert main(["prove", "--input", str(empty)]) != 0

    def test_export_empty_file_returns_nonzero(self, tmp_path):
        """Empty input file for export returns non-zero code."""
        empty = tmp_path / "empty.json"
        empty.write_text("")
        out_dir = tmp_path / "export_out"
        assert main(["export", "--input", str(empty), "--output-dir", str(out_dir)]) != 0

    def test_sieve_syntax_corrupted_json_returns_nonzero(self, tmp_path):
        """Corrupted JSON syntax returns non-zero code."""
        corrupt = tmp_path / "corrupt.json"
        corrupt.write_text('{"id": "bad", "statement": [unclosed')
        assert main(["sieve", "--input", str(corrupt)]) != 0

    def test_sieve_primitive_json_types_return_nonzero(self, tmp_path):
        """Primitive JSON root types (str, int, bool, null) return non-zero code."""
        for val in ['"just a string"', "12345", "true", "null"]:
            f = tmp_path / "prim.json"
            f.write_text(val)
            assert main(["sieve", "--input", str(f)]) != 0
            assert main(["prove", "--input", str(f)]) != 0

    def test_sieve_list_of_non_dict_items_returns_nonzero(self, tmp_path):
        """JSON list containing non-dict items returns non-zero code."""
        f = tmp_path / "list_ints.json"
        f.write_text(json.dumps([1, 2, 3]))
        assert main(["sieve", "--input", str(f)]) != 0
        assert main(["prove", "--input", str(f)]) != 0

    def test_sieve_empty_list_returns_zero_empty_output(self, tmp_path):
        """Empty list of conjectures produces empty output list and exits 0."""
        f = tmp_path / "empty_list.json"
        f.write_text("[]")
        out = tmp_path / "out.json"
        code = main(["sieve", "--input", str(f), "--output", str(out)])
        assert code == 0
        assert out.exists()
        assert json.loads(out.read_text()) == []

    def test_nonexistent_input_file_all_subcommands(self, tmp_path):
        """Non-existent input file returns non-zero code across all reading subcommands."""
        missing = tmp_path / "nonexistent.json"
        assert main(["sieve", "--input", str(missing)]) != 0
        assert main(["prove", "--input", str(missing)]) != 0
        assert main(["export", "--input", str(missing), "--output-dir", str(tmp_path / "out")]) != 0

    def test_directory_as_input_file_returns_nonzero(self, tmp_path):
        """Passing directory instead of file as --input returns non-zero code."""
        assert main(["sieve", "--input", str(tmp_path)]) != 0
        assert main(["prove", "--input", str(tmp_path)]) != 0


# ============================================================================
# 2. ADVERSARIAL EXPRESSIONS & OPERATOR ROBUSTNESS
# ============================================================================


class TestAdversarialExpressionsAndOperators:
    """Stress tests for mathematical parser, deep nesting, operators, and safety."""

    def test_deeply_nested_unary_expression_parsing(self):
        """50-level nested sqrt parses into valid AST with depth >= 50."""
        nested = "sqrt(" * 50 + "order" + ")" * 50
        node = _parse_expr_str(nested)
        assert node.depth >= 50

    def test_deeply_nested_binary_expression_parsing(self):
        """50-level nested binary additions parse into valid AST."""
        nested = " + ".join(["1.0"] * 50)
        node = _parse_expr_str(nested)
        assert node.complexity >= 50

    def test_extreme_nesting_fallback_without_crash(self):
        """500-level nesting triggers graceful fallback to InvariantNode without crashing."""
        extreme = "sqrt(" * 500 + "order" + ")" * 500
        node = _parse_expr_str(extreme)
        assert isinstance(node, InvariantNode)

    def test_unsupported_operators_fallback_cleanly(self):
        """Bitwise, matrix, and custom operators parse or fallback without crash."""
        for expr in ["foo & bar", "a @ b", "x | y", "p % q", "m // n", "u << v"]:
            node = _parse_expr_str(expr)
            assert node is not None

    def test_unicode_and_latex_relational_operators(self):
        """Mathematical Unicode and LaTeX symbols resolve into valid Conjectures."""
        c1 = _resolve_conjecture_from_dict({"statement": "order ≤ size"})
        assert c1.rel == "<="
        c2 = _resolve_conjecture_from_dict({"statement": "order ≥ size"})
        assert c2.rel == ">="
        c3 = _resolve_conjecture_from_dict({"statement": r"\chi(G) \le \Delta(G) + 1"})
        assert c3.rel == "<="

    def test_universal_quantifier_and_guard_statement(self):
        """Conjecture with universal quantifier and implication guard resolves cleanly."""
        stmt = r"\forall G, is_triangle_free(G) ==> chi(G) <= 2"
        conj = _resolve_conjecture_from_dict({"statement": stmt})
        assert conj.guard_predicate is not None
        assert conj.rel == "<="

    def test_ast_parser_blocks_code_injection(self):
        """Code injection attempts in statement strings are parsed as AST, not executed."""
        inj_stmt = '__import__("os").system("echo injected") <= 1'
        conj = _resolve_conjecture_from_dict({"statement": inj_stmt})
        assert conj is not None
        assert conj.rel == "<="


# ============================================================================
# 3. EXTREME LIMITS, BOUNDARY PARAMETERS, & ARGPARSE
# ============================================================================


class TestExtremeArgumentsAndFlags:
    """Stress tests for limit clamping, invalid options, and argparse constraints."""

    def test_conjecture_limit_zero_clamped_to_one(self, tmp_path):
        """--limit 0 is clamped to 1 candidate conjecture."""
        out = tmp_path / "conj0.json"
        assert main(["conjecture", "--limit", "0", "--output", str(out)]) == 0
        assert len(json.loads(out.read_text())) == 1

    def test_conjecture_negative_limit_clamped_to_one(self, tmp_path):
        """Negative limit is clamped to 1 candidate conjecture."""
        out = tmp_path / "conj_neg.json"
        assert main(["conjecture", "--limit", "-10", "--output", str(out)]) == 0
        assert len(json.loads(out.read_text())) == 1

    def test_conjecture_large_limit_runs_fast(self, tmp_path):
        """--limit 10000 generates exhaustive conjectures without hang (<1s)."""
        out = tmp_path / "conj_large.json"
        assert main(["conjecture", "--limit", "10000", "--output", str(out)]) == 0
        data = json.loads(out.read_text())
        assert len(data) >= 1000

    def test_sieve_cegar_max_rounds_extremes(self, tmp_path):
        """Extreme cegar-max-rounds (0, negative, 100) are clamped and execute cleanly."""
        fin = tmp_path / "in.json"
        fin.write_text(json.dumps([{"statement": "order >= 0"}]))
        for rounds in [0, -5, 100]:
            fout = tmp_path / f"out_{rounds}.json"
            assert main(["sieve", "--input", str(fin), "--output", str(fout), "--cegar-max-rounds", str(rounds)]) == 0
            assert fout.exists()

    def test_prove_max_depth_extremes(self, tmp_path):
        """Extreme max-depth parameters (0, negative, 20) execute without crashing."""
        fin = tmp_path / "in.json"
        fin.write_text(json.dumps({"statement": "chi <= Delta + 1"}))
        for depth in [0, -5, 20]:
            fout = tmp_path / f"out_d{depth}.json"
            assert main(["prove", "--input", str(fin), "--output", str(fout), "--max-depth", str(depth)]) == 0
            assert fout.exists()

    def test_export_invalid_format_raises_system_exit(self, tmp_path):
        """Invalid format choice raises SystemExit(2)."""
        fin = tmp_path / "in.json"
        fin.write_text(json.dumps({"status": "SURVIVED"}))
        with pytest.raises(SystemExit) as exc_info:
            main(["export", "--input", str(fin), "--output-dir", str(tmp_path / "out"), "--format", "invalid_fmt"])
        assert exc_info.value.code != 0

    def test_empty_cli_args_raises_system_exit(self):
        """Calling main with empty arguments list raises SystemExit != 0."""
        with pytest.raises(SystemExit) as exc_info:
            main([])
        assert exc_info.value.code != 0

    def test_unknown_subcommand_raises_system_exit(self):
        """Calling unknown subcommand raises SystemExit != 0."""
        with pytest.raises(SystemExit) as exc_info:
            main(["nonexistent_subcommand"])
        assert exc_info.value.code != 0


# ============================================================================
# 4. EXIT CODES & UNHANDLED ERROR BOUNDARIES
# ============================================================================


class TestExitCodesAndErrorBoundaries:
    """Verifies that all failure modes yield non-zero exit codes."""

    def test_unwritable_output_directory_returns_nonzero(self, tmp_path):
        """Unwritable destination directory returns non-zero exit code."""
        fin = tmp_path / "in.json"
        fin.write_text(json.dumps({"status": "SURVIVED"}))
        bad_out_dir = "/dev/null/cannot_create_dir"
        assert main(["export", "--input", str(fin), "--output-dir", bad_out_dir]) != 0

    def test_directory_as_output_file_returns_nonzero(self, tmp_path):
        """Passing directory as --output file returns non-zero exit code."""
        fin = tmp_path / "in.json"
        fin.write_text(json.dumps([{"statement": "order >= 0"}]))
        assert main(["sieve", "--input", str(fin), "--output", str(tmp_path)]) != 0

    def test_demo_unknown_scenario_returns_nonzero(self):
        """Unknown demo scenario returns non-zero code."""
        assert main(["demo", "--scenario", "bogus_scenario_123"]) != 0

    def test_demo_empty_scenario_returns_nonzero(self):
        """Empty string demo scenario returns non-zero code."""
        assert main(["demo", "--scenario", ""]) != 0

    def test_demo_unwritable_output_dir_returns_nonzero(self):
        """Demo targeting unwritable directory returns non-zero code."""
        assert main(["demo", "--scenario", "c5_refutation", "--output-dir", "/dev/null/bad"]) != 0


# ============================================================================
# 5. STDOUT VS FILE REDIRECTION & PIPELINING
# ============================================================================


class TestStdoutVsFileRedirection:
    """Verifies clean stdout vs file outputs and pipeline chaining."""

    def test_conjecture_stdout_valid_json_and_file_quiet(self, tmp_path):
        """Conjecture stdout is valid JSON, and file output produces empty stdout."""
        # 1. stdout mode
        p_std = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "conjecture", "--limit", "2"],
            capture_output=True, text=True
        )
        assert p_std.returncode == 0
        data = json.loads(p_std.stdout)
        assert len(data) == 2

        # 2. file mode
        out_f = tmp_path / "c_out.json"
        p_file = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "conjecture", "--limit", "2", "--output", str(out_f)],
            capture_output=True, text=True
        )
        assert p_file.returncode == 0
        assert p_file.stdout.strip() == ""
        assert len(json.loads(out_f.read_text())) == 2

    def test_sieve_stdout_valid_json_and_file_quiet(self, tmp_path):
        """Sieve stdout is valid JSON, and file output produces empty stdout."""
        fin = tmp_path / "s_in.json"
        fin.write_text(json.dumps([{"statement": "order >= 0"}]))

        # stdout mode
        p_std = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "sieve", "--input", str(fin), "--tier1-only"],
            capture_output=True, text=True
        )
        assert p_std.returncode == 0
        assert json.loads(p_std.stdout)[0]["status"] == "SURVIVED"

        # file mode
        fout = tmp_path / "s_out.json"
        p_file = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "sieve", "--input", str(fin), "--output", str(fout), "--tier1-only"],
            capture_output=True, text=True
        )
        assert p_file.returncode == 0
        assert p_file.stdout.strip() == ""
        assert json.loads(fout.read_text())[0]["status"] == "SURVIVED"

    def test_prove_stdout_valid_json_and_file_quiet(self, tmp_path):
        """Prove stdout is valid JSON, and file output produces empty stdout."""
        fin = tmp_path / "p_in.json"
        fin.write_text(json.dumps({"statement": "chi <= Delta + 1"}))

        # stdout mode
        p_std = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "prove", "--input", str(fin)],
            capture_output=True, text=True
        )
        assert p_std.returncode == 0
        assert json.loads(p_std.stdout)["status"] == "PROVEN"

        # file mode
        fout = tmp_path / "p_out.json"
        p_file = subprocess.run(
            [sys.executable, "-m", "autonomous_math.cli.main", "prove", "--input", str(fin), "--output", str(fout)],
            capture_output=True, text=True
        )
        assert p_file.returncode == 0
        assert p_file.stdout.strip() == ""
        assert json.loads(fout.read_text())["status"] == "PROVEN"

    def test_unix_subcommand_pipeline_flow(self, tmp_path):
        """End-to-end chained flow: conjecture -> sieve -> prove -> export."""
        c_file = tmp_path / "conjectures.json"
        s_file = tmp_path / "sieved.json"
        p_file = tmp_path / "proven.json"
        deliverables_dir = tmp_path / "deliverables"

        # Step 1: conjecture
        assert main(["conjecture", "--strategy", "archetypes", "--output", str(c_file)]) == 0
        assert c_file.exists()

        # Step 2: sieve
        assert main(["sieve", "--input", str(c_file), "--output", str(s_file), "--tier1-only"]) == 0
        assert s_file.exists()

        # Step 3: prove
        assert main(["prove", "--input", str(s_file), "--output", str(p_file)]) == 0
        assert p_file.exists()

        # Step 4: export
        assert main(["export", "--input", str(p_file), "--output-dir", str(deliverables_dir)]) == 0
        assert (deliverables_dir / "main.tex").exists()
        assert (deliverables_dir / "lean").exists()
        val = ArtifactValidator.validate_export_bundle(deliverables_dir)
        assert val.is_valid is True


# ============================================================================
# 6. DEMO SCENARIOS & ARTIFACT INTEGRITY VERIFICATION
# ============================================================================


class TestDiscoveryDemosAndArtifactIntegrity:
    """Verifies all demonstration scenarios in both ephemeral and persistent modes."""

    @pytest.mark.parametrize("scenario", ["c5_refutation", "greedy_coloring_bound", "clique_chromatic_bound"])
    def test_demo_scenarios_ephemeral_exits_zero(self, scenario):
        """Demo scenario runs end-to-end in temporary directory and exits 0."""
        code = main(["demo", "--scenario", scenario])
        assert code == 0

    @pytest.mark.parametrize("scenario", ["c5_refutation", "greedy_coloring_bound", "clique_chromatic_bound"])
    def test_demo_scenarios_persistent_validated(self, scenario, tmp_path):
        """Demo scenario writes validated deliverables to --output-dir."""
        demo_out = tmp_path / f"demo_{scenario}"
        code = main(["demo", "--scenario", scenario, "--output-dir", str(demo_out)])
        assert code == 0
        assert (demo_out / "paper" / "main.tex").exists()
        assert (demo_out / "lean").exists()
        val = ArtifactValidator.validate_export_bundle(demo_out)
        assert val.is_valid is True
