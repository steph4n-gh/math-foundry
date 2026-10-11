"""Feature 15: Artifact Syntax & Completeness Validator.

Provides standalone, zero-external-dependency validation for:
1. LaTeX Academic Preprint manuscripts:
   - File/directory structure (main.tex, preamble.tex, references.bib, figures/lemma_dag.tex, sections/*.tex)
   - Balanced LaTeX environments (\\begin{env} ... \\end{env})
   - Balanced curly braces ({ and }) accounting for escaped braces and comments
   - TikZ environment syntax integrity (\\begin{tikzpicture} ... \\end{tikzpicture})
2. Lean 4 Formalization Artifacts:
   - Mathlib import (import Mathlib)
   - Root namespace (namespace OAI)
   - Balanced namespace open and close tags
   - Theorem / definition declarations
   - Presence of sorry placeholders
3. openai/math Comparator Challenge JSON specs:
   - Strict schema compliance with ComparatorChallengeSpec
   - Classical axioms triad (propext, Quot.sound, Classical.choice)
   - Cross-validation between JSON metadata and Lean source declarations
4. Dual Export Bundle Validation:
   - Combined LaTeX and Lean verification over bundle directories
"""

from __future__ import annotations

from collections import Counter
import json
import logging
from pathlib import Path
import re
from typing import Any, Dict, Iterator, List, Optional, Set, Tuple, Union

from pydantic import BaseModel, ConfigDict, Field

logger = logging.getLogger(__name__)


# ============================================================================
# 1. VALIDATION RESULT DATA MODEL
# ============================================================================

class ArtifactValidationResult(BaseModel):
    """Encapsulates validation outcome for exported artifacts.

    Supports both object attribute access (.is_valid, .errors, .warnings, .details)
    and transparent 2-tuple unpacking (`valid, errs = result`) for 100%
    backwards-compatibility with existing test suites.
    """

    model_config = ConfigDict(arbitrary_types_allowed=True, extra="allow")

    is_valid: bool
    errors: List[str] = Field(default_factory=list)
    warnings: List[str] = Field(default_factory=list)
    details: Dict[str, Any] = Field(default_factory=dict)

    def __bool__(self) -> bool:
        """Evaluate truthiness by validity."""
        return self.is_valid

    def __iter__(self) -> Iterator[Any]:
        """Support 2-tuple unpacking: `is_valid, errors = result`."""
        yield self.is_valid
        yield self.errors

    def __getitem__(self, index: int) -> Any:
        """Support index subscripting: result[0] -> is_valid, result[1] -> errors."""
        if index == 0:
            return self.is_valid
        elif index == 1:
            return self.errors
        raise IndexError(
            f"Index {index} out of range for ArtifactValidationResult (supports 0: is_valid, 1: errors)"
        )

    def __len__(self) -> int:
        return 2

    def to_dict(self) -> Dict[str, Any]:
        """Convert result to dictionary representation."""
        return {
            "is_valid": self.is_valid,
            "errors": list(self.errors),
            "warnings": list(self.warnings),
            "details": dict(self.details),
        }

    @classmethod
    def valid(
        cls,
        details: Optional[Dict[str, Any]] = None,
        warnings: Optional[List[str]] = None,
    ) -> ArtifactValidationResult:
        """Factory for a successful validation outcome."""
        return cls(is_valid=True, errors=[], warnings=warnings or [], details=details or {})

    @classmethod
    def invalid(
        cls,
        errors: List[str],
        details: Optional[Dict[str, Any]] = None,
        warnings: Optional[List[str]] = None,
    ) -> ArtifactValidationResult:
        """Factory for an unsuccessful validation outcome."""
        return cls(is_valid=False, errors=errors, warnings=warnings or [], details=details or {})

    def merge(self, other: ArtifactValidationResult) -> ArtifactValidationResult:
        """Combine this result with another validation result."""
        merged_errors = list(self.errors) + list(other.errors)
        merged_warnings = list(self.warnings) + list(other.warnings)
        merged_details = dict(self.details)
        merged_details.update(other.details)
        return ArtifactValidationResult(
            is_valid=self.is_valid and other.is_valid and (len(merged_errors) == 0),
            errors=merged_errors,
            warnings=merged_warnings,
            details=merged_details,
        )


# ============================================================================
# 2. LATEX SYNTAX PARSING UTILITIES
# ============================================================================

def strip_latex_comments(content: str) -> str:
    """Strip LaTeX comments (% to end of line), preserving escaped \\%."""
    placeholder = "\x00PERCENT_ESCAPED\x00"
    # Replace literal \% with sentinel
    clean = re.sub(r"(?<!\\)\\%", placeholder, content)
    # Remove % and remainder of line
    clean = re.sub(r"%.*$", "", clean, flags=re.MULTILINE)
    # Restore literal \%
    return clean.replace(placeholder, r"\%")


def check_latex_brace_balance(content: str) -> Tuple[bool, List[str]]:
    """Verify that curly braces { and } are balanced in LaTeX content.

    Correctly handles escaped braces \\{ and \\} and comments.
    """
    errors: List[str] = []
    clean = strip_latex_comments(content)

    # Replace double backslashes (linebreaks / escaped backslashes) with sentinel
    clean = clean.replace(r"\\", "\x00DOUBLE_SLASH\x00")

    # Replace escaped braces \{ and \} which represent literal brackets
    clean = clean.replace(r"\{", "\x00ESC_OPEN\x00").replace(r"\}", "\x00ESC_CLOSE\x00")

    depth = 0
    unmatched_open: List[Tuple[int, int]] = []  # (line, col)

    for line_idx, line in enumerate(clean.splitlines(), start=1):
        for col_idx, char in enumerate(line, start=1):
            if char == "{":
                depth += 1
                unmatched_open.append((line_idx, col_idx))
            elif char == "}":
                if depth <= 0:
                    errors.append(f"Unmatched closing brace '}}' at line {line_idx}:{col_idx}")
                else:
                    depth -= 1
                    unmatched_open.pop()

    if depth > 0:
        first_line, first_col = unmatched_open[0]
        errors.append(
            f"Unbalanced braces: {depth} unclosed '{{' brace(s) (first opened at line {first_line}:{first_col})"
        )

    return len(errors) == 0, errors


def check_latex_environments(content: str) -> Tuple[bool, List[str]]:
    """Verify balanced LaTeX environments using stack-based nesting and count matching."""
    errors: List[str] = []
    clean = strip_latex_comments(content)

    # 1. Stack-based nesting check
    env_regex = re.compile(r"\\(begin|end)\{([a-zA-Z0-9*]+)\}")
    stack: List[Tuple[str, int]] = []  # (env_name, line_num)

    for match in env_regex.finditer(clean):
        tag, env_name = match.group(1), match.group(2)
        line_num = clean[: match.start()].count("\n") + 1
        if tag == "begin":
            stack.append((env_name, line_num))
        else:
            if not stack:
                errors.append(f"Unexpected '\\end{{{env_name}}}' at line {line_num} with no matching '\\begin'")
            elif stack[-1][0] != env_name:
                top_env, top_line = stack.pop()
                errors.append(
                    f"Mismatched LaTeX environment at line {line_num}: "
                    f"expected '\\end{{{top_env}}}' (opened line {top_line}), got '\\end{{{env_name}}}'"
                )
            else:
                stack.pop()

    if stack:
        for env_name, line_num in stack:
            errors.append(f"Unclosed LaTeX environment '\\begin{{{env_name}}}' opened at line {line_num}")

    # 2. Per-environment count check matching ReferenceArtifactValidator oracle
    begins = [m.group(1) for m in re.finditer(r"\\begin\{([a-zA-Z0-9*]+)\}", clean)]
    ends = [m.group(1) for m in re.finditer(r"\\end\{([a-zA-Z0-9*]+)\}", clean)]
    cb = Counter(begins)
    ce = Counter(ends)
    for env in sorted(set(cb.keys()) | set(ce.keys())):
        if cb[env] != ce[env]:
            msg = f"Unbalanced LaTeX environment '\\begin{{{env}}}' ({cb[env]}) vs '\\end{{{env}}}' ({ce[env]})"
            if not any(env in e for e in errors):
                errors.append(msg)

    return len(errors) == 0, errors


def check_tikz_environments(content: str) -> Tuple[bool, List[str]]:
    """Verify TikZ environment syntax integrity."""
    errors: List[str] = []
    clean = strip_latex_comments(content)

    tikz_begins = len(re.findall(r"\\begin\{tikzpicture\}", clean))
    tikz_ends = len(re.findall(r"\\end\{tikzpicture\}", clean))

    if tikz_begins != tikz_ends:
        errors.append(
            f"Unbalanced TikZ environment: {tikz_begins} '\\begin{{tikzpicture}}' vs {tikz_ends} '\\end{{tikzpicture}}'"
        )
        return False, errors

    if tikz_begins > 0:
        matches = re.finditer(r"\\begin\{tikzpicture\}(.*?)\\end\{tikzpicture\}", clean, re.DOTALL)
        for idx, match in enumerate(matches, start=1):
            body = match.group(1)
            node_count = len(re.findall(r"\\node\b", body))
            draw_count = len(re.findall(r"\\draw\b", body))
            semi_count = body.count(";")
            if (node_count + draw_count > 0) and semi_count == 0:
                errors.append(f"TikZ environment #{idx} contains \\node/\\draw without terminating semicolon ';'")

    return len(errors) == 0, errors


REQUIRED_LATEX_DIR_FILES = [
    "main.tex",
    "preamble.tex",
    "references.bib",
]


def validate_latex_directory_structure(tex_dir: Path) -> Tuple[bool, List[str]]:
    """Verify presence of required preprint files and section inputs."""
    errors: List[str] = []
    if not tex_dir.exists() or not tex_dir.is_dir():
        return False, [f"LaTeX directory does not exist: {tex_dir}"]

    for req in REQUIRED_LATEX_DIR_FILES:
        if not (tex_dir / req).exists():
            errors.append(f"Missing required LaTeX artifact: '{req}'")

    # Figure check: figures/lemma_dag.tex or valid .tex inside figures/
    fig_file = tex_dir / "figures" / "lemma_dag.tex"
    fig_dir = tex_dir / "figures"
    if not fig_file.exists():
        if not (fig_dir.exists() and any(fig_dir.glob("*.tex"))):
            errors.append("Missing required TikZ figure artifact: 'figures/lemma_dag.tex'")

    # Validate \input references in main.tex
    main_file = tex_dir / "main.tex"
    if main_file.exists():
        main_text = main_file.read_text(encoding="utf-8", errors="replace")
        input_refs = re.findall(r"\\input\{([^}]+)\}", main_text)
        for ref in input_refs:
            ref_path = tex_dir / ref
            ref_tex = tex_dir / f"{ref}.tex"
            if not ref_path.exists() and not ref_tex.exists():
                errors.append(f"Referenced LaTeX input file not found: '{ref}'")

    return len(errors) == 0, errors


# ============================================================================
# 3. LEAN 4 SYNTAX & COMPARATOR JSON UTILITIES
# ============================================================================

def strip_lean_comments(code: str) -> str:
    """Remove single-line (-- ...) and block (/- ... -/) comments from Lean source."""
    code = re.sub(r"/-\s*.*?\s*-/", "", code, flags=re.DOTALL)
    code = re.sub(r"--.*$", "", code, flags=re.MULTILINE)
    return code


def check_lean_syntax(lean_code: str) -> Tuple[bool, List[str]]:
    """Validate Lean 4 source syntax and required structure."""
    errors: List[str] = []

    if "import Mathlib" not in lean_code:
        errors.append("Missing required import: 'import Mathlib'")

    if "namespace OAI" not in lean_code:
        errors.append("Missing required root namespace: 'namespace OAI'")

    clean_code = strip_lean_comments(lean_code)

    if not re.search(r"\b(theorem|def|lemma)\b", clean_code):
        errors.append("No theorem or def declared in Lean source")

    if "sorry" not in clean_code:
        errors.append("Lean formalization scaffold must contain 'sorry' placeholder")

    # Stack-based namespace verification
    ns_tokens = re.finditer(r"\b(namespace|end)\b(?:\s+([a-zA-Z0-9_.]+))?", clean_code)
    stack: List[str] = []
    for match in ns_tokens:
        kw, name = match.group(1), match.group(2)
        if kw == "namespace":
            stack.append(name if name else "anonymous")
        elif kw == "end":
            if not stack:
                errors.append("Unexpected 'end' with no open namespace")
            else:
                top = stack.pop()
                if name and top != "anonymous" and name != top:
                    errors.append(f"Namespace mismatch: opened '{top}', closed with 'end {name}'")

    if stack:
        errors.append(f"Unclosed namespace(s): {', '.join(stack)}")

    # Count matching oracle check
    if lean_code.count("namespace") != lean_code.count("end"):
        if not any("open/close count" in e for e in errors):
            errors.append("Mismatched namespace open/close count")

    return len(errors) == 0, errors


def check_comparator_json_schema(json_str: str) -> Tuple[bool, List[str], Dict[str, Any]]:
    """Validate openai/math comparator challenge JSON schema."""
    errors: List[str] = []
    try:
        data = json.loads(json_str)
    except Exception as e:
        return False, [f"Invalid JSON syntax in comparator file: {e}"], {}

    if not isinstance(data, dict):
        return False, ["Comparator JSON must be a top-level JSON object"], {}

    required_keys = {
        "challenge_module",
        "solution_module",
        "theorem_names",
        "definition_names",
        "permitted_axioms",
        "enable_nanoda",
    }
    missing = required_keys - set(data.keys())
    if missing:
        errors.append(f"Missing required keys in comparator JSON: {sorted(missing)}")

    if "challenge_module" in data and (
        not isinstance(data["challenge_module"], str) or not data["challenge_module"].strip()
    ):
        errors.append("'challenge_module' must be a non-empty string")

    if "solution_module" in data and (
        not isinstance(data["solution_module"], str) or not data["solution_module"].strip()
    ):
        errors.append("'solution_module' must be a non-empty string")

    if "theorem_names" in data:
        if not isinstance(data["theorem_names"], list):
            errors.append("'theorem_names' must be a list")
        elif len(data["theorem_names"]) == 0:
            errors.append("'theorem_names' must not be empty")
        elif not all(isinstance(t, str) and t.strip() for t in data["theorem_names"]):
            errors.append("All items in 'theorem_names' must be non-empty strings")

    if "definition_names" in data and not isinstance(data["definition_names"], list):
        errors.append("'definition_names' must be a list")

    if "permitted_axioms" in data:
        if not isinstance(data["permitted_axioms"], list):
            errors.append("'permitted_axioms' must be a list")
        else:
            required_axioms = {"propext", "Quot.sound", "Classical.choice"}
            missing_axioms = required_axioms - set(data["permitted_axioms"])
            if missing_axioms:
                errors.append(f"Missing classical axioms in 'permitted_axioms': {sorted(missing_axioms)}")

    if "enable_nanoda" in data and not isinstance(data["enable_nanoda"], bool):
        errors.append("'enable_nanoda' must be a boolean")

    return len(errors) == 0, errors, data


# ============================================================================
# 4. PRIMARY ARTIFACT VALIDATOR ENGINE
# ============================================================================

class ArtifactValidator:
    """Artifact Syntax & Completeness Validator for Autonomous Math Pipeline."""

    @classmethod
    def validate_latex(cls, latex_dir_or_file: Union[str, Path]) -> ArtifactValidationResult:
        """Validate a LaTeX manuscript directory or single .tex file."""
        target = Path(latex_dir_or_file)
        if not target.exists():
            return ArtifactValidationResult.invalid(
                errors=[f"Target LaTeX path does not exist: {target}"],
                details={"target": str(target)},
            )

        all_errors: List[str] = []
        details: Dict[str, Any] = {"target": str(target)}

        if target.is_dir():
            struct_valid, struct_errs = validate_latex_directory_structure(target)
            all_errors.extend(struct_errs)

            tex_files = list(target.rglob("*.tex"))
            details["tex_files_found"] = [str(f.relative_to(target)) for f in tex_files]

            for f in tex_files:
                rel = str(f.relative_to(target))
                content = f.read_text(encoding="utf-8", errors="replace")

                env_ok, env_errs = check_latex_environments(content)
                for err in env_errs:
                    all_errors.append(f"[{rel}] {err}")

                br_ok, br_errs = check_latex_brace_balance(content)
                for err in br_errs:
                    all_errors.append(f"[{rel}] {err}")

                if "\\begin{tikzpicture}" in content:
                    tz_ok, tz_errs = check_tikz_environments(content)
                    for err in tz_errs:
                        all_errors.append(f"[{rel}] {err}")

        else:
            content = target.read_text(encoding="utf-8", errors="replace")
            env_ok, env_errs = check_latex_environments(content)
            all_errors.extend(env_errs)

            br_ok, br_errs = check_latex_brace_balance(content)
            all_errors.extend(br_errs)

            if "\\begin{tikzpicture}" in content:
                tz_ok, tz_errs = check_tikz_environments(content)
                all_errors.extend(tz_errs)

        is_valid = len(all_errors) == 0
        return ArtifactValidationResult(is_valid=is_valid, errors=all_errors, details=details)

    @classmethod
    def validate_lean(
        cls, lean_file: Union[str, Path], json_file: Optional[Union[str, Path]] = None
    ) -> ArtifactValidationResult:
        """Validate Lean 4 source file and companion comparator JSON schema."""
        l_path = Path(lean_file)
        if not l_path.exists():
            return ArtifactValidationResult.invalid(
                errors=[f"Lean source file does not exist: {l_path}"]
            )

        all_errors: List[str] = []
        warnings: List[str] = []
        details: Dict[str, Any] = {"lean_file": str(l_path)}

        lean_text = l_path.read_text(encoding="utf-8", errors="replace")
        syntax_ok, syntax_errs = check_lean_syntax(lean_text)
        all_errors.extend(syntax_errs)

        # Auto-discover companion JSON if not explicitly provided
        j_path: Optional[Path] = None
        if json_file is not None:
            j_path = Path(json_file)
        else:
            candidate = l_path.with_suffix(".json")
            if candidate.exists():
                j_path = candidate

        if j_path is not None:
            details["json_file"] = str(j_path)
            if not j_path.exists():
                all_errors.append(f"Companion JSON file does not exist: {j_path}")
            else:
                json_text = j_path.read_text(encoding="utf-8", errors="replace")
                j_ok, j_errs, j_data = check_comparator_json_schema(json_text)
                all_errors.extend(j_errs)

                # Cross-check declared theorems against Lean source
                if j_ok and "theorem_names" in j_data:
                    stripped_lean = strip_lean_comments(lean_text)
                    declared_theorems = set(re.findall(r"\btheorem\s+([a-zA-Z0-9_]+)", stripped_lean))
                    for th_full in j_data["theorem_names"]:
                        th_leaf = th_full.split(".")[-1]
                        if th_leaf not in declared_theorems:
                            all_errors.append(
                                f"Theorem '{th_full}' specified in JSON was not declared in Lean source (found: {sorted(declared_theorems)})"
                            )

        is_valid = len(all_errors) == 0
        return ArtifactValidationResult(
            is_valid=is_valid, errors=all_errors, warnings=warnings, details=details
        )

    @classmethod
    def validate_export_bundle(cls, output_dir: Union[str, Path]) -> ArtifactValidationResult:
        """Validate both LaTeX manuscript and Lean 4 artifacts in an export directory."""
        out = Path(output_dir)
        if not out.exists() or not out.is_dir():
            return ArtifactValidationResult.invalid(errors=[f"Bundle directory does not exist: {out}"])

        all_errors: List[str] = []
        warnings: List[str] = []
        details: Dict[str, Any] = {"bundle_dir": str(out)}
        artifacts_checked = 0

        # 1. LaTeX manuscript validation
        latex_candidates = [out, out / "paper", out / "latex"]
        latex_dir: Optional[Path] = None
        for cand in latex_candidates:
            if (cand / "main.tex").exists():
                latex_dir = cand
                break

        if latex_dir is not None:
            artifacts_checked += 1
            tex_res = cls.validate_latex(latex_dir)
            all_errors.extend(tex_res.errors)
            warnings.extend(tex_res.warnings)
            details["latex_validation"] = tex_res.to_dict()
        else:
            tex_files = list(out.rglob("*.tex"))
            if tex_files:
                artifacts_checked += 1
                for tf in tex_files:
                    res = cls.validate_latex(tf)
                    all_errors.extend(res.errors)

        # 2. Lean 4 formalization artifacts validation
        lean_files = list(out.rglob("*.lean"))
        if lean_files:
            artifacts_checked += 1
            details["lean_files_found"] = [str(lf.relative_to(out)) for lf in lean_files]
            for lf in lean_files:
                jf = lf.with_suffix(".json")
                res = cls.validate_lean(lf, jf if jf.exists() else None)
                all_errors.extend(res.errors)
                warnings.extend(res.warnings)

        if artifacts_checked == 0:
            all_errors.append(f"No LaTeX or Lean export artifacts found in bundle directory: {out}")

        is_valid = len(all_errors) == 0
        return ArtifactValidationResult(
            is_valid=is_valid, errors=all_errors, warnings=warnings, details=details
        )

    # ------------------------------------------------------------------------
    # Backward-Compatible Static Interface for E2E Tests
    # ------------------------------------------------------------------------

    @classmethod
    def validate_latex_content(cls, content: str) -> ArtifactValidationResult:
        """Validate a raw LaTeX source string."""
        errors: List[str] = []
        env_ok, env_errs = check_latex_environments(content)
        errors.extend(env_errs)
        br_ok, br_errs = check_latex_brace_balance(content)
        errors.extend(br_errs)
        if "\\begin{tikzpicture}" in content:
            tz_ok, tz_errs = check_tikz_environments(content)
            errors.extend(tz_errs)
        return ArtifactValidationResult(is_valid=(len(errors) == 0), errors=errors)

    @classmethod
    def validate_latex_directory(cls, dir_path: Union[str, Path]) -> ArtifactValidationResult:
        """Validate an entire LaTeX preprint directory."""
        return cls.validate_latex(dir_path)

    @classmethod
    def validate_lean_source(cls, lean_code: str) -> ArtifactValidationResult:
        """Validate a raw Lean 4 source string."""
        syntax_ok, syntax_errs = check_lean_syntax(lean_code)
        return ArtifactValidationResult(is_valid=syntax_ok, errors=syntax_errs)

    @classmethod
    def validate_lean_comparator_json(cls, json_str: str) -> ArtifactValidationResult:
        """Validate a raw comparator JSON string."""
        j_ok, j_errs, _ = check_comparator_json_schema(json_str)
        return ArtifactValidationResult(is_valid=j_ok, errors=j_errs)


# Compatibility alias used by test suites
OutputSyntaxValidator = ArtifactValidator
