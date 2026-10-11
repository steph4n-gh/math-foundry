"""Closed-Loop Formal Lean 4 Prover and Tactic Search Engine.

Bridges empirical conjecture discovery and formal mathematical verification by
ingesting Lean 4 challenge specifications, orchestrating systematic tactic search
(`omega`, `linarith`, `nlinarith`, `aesop`, `positivity`, and genuine Mathlib
lemmas), compiling against the Lean 4 kernel, and certifying structured
targets as MACHINE_CHECKED_PROVEN.
"""

from __future__ import annotations

import logging
import fcntl
import hashlib
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
import time
import textwrap
import uuid
from typing import Any, Dict, List, Literal, Optional, Sequence, Tuple, Union
from pydantic import BaseModel, ConfigDict, Field
from autonomous_math.prover.codex_synthesis import SynthesisError, terminate_process_group, validate_synthesis_response

logger = logging.getLogger(__name__)


def _target_axiom_report(stdout, full_name):
    """Read only the unique final report emitted by our exact #print command.

    Tactics can print arbitrary text. A generic first 'depends on axioms' match
    would let a forged trace hide a later real native-decision axiom report.
    """
    prefix = r"(?m)^'" + re.escape(full_name) + r"' "
    if len(re.findall(prefix, stdout)) != 1:
        return [], "Expected exactly one authoritative report for the target theorem"
    pattern = prefix + r"(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)[ \t]*$"
    match = re.search(pattern, stdout)
    if match is None or stdout[match.end():].strip():
        return [], "The final compiler output is not the exact target's axiom report"
    axioms = [name.strip().strip("'") for name in (match[1] or "").split(",") if name.strip()]
    return axioms, None

# Verification Status Types
VerificationStatus = Literal[
    "MACHINE_CHECKED_PROVEN",
    "REFUTED",
    "UNRESOLVED",
    "FAILED",
    "ERROR",
    "TOOLCHAIN_UNAVAILABLE",
]


class LeanProofScript(BaseModel):
    """Specification of a candidate tactic or proof script."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    name: str
    tactic_code: str
    category: str = "general"
    description: str = ""


class LeanVerificationResult(BaseModel):
    """Encapsulates the complete outcome of Lean 4 formal verification."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    status: VerificationStatus
    is_machine_checked: bool
    theorem_name: str
    conjecture_id: str
    successful_tactic: Optional[str] = None
    verified_lean_code: Optional[str] = None
    verified_file_path: Optional[Path] = None
    attempts_count: int = 0
    verification_time_ms: float = 0.0
    lean_version: Optional[str] = None
    diagnostics: List[Dict[str, Any]] = Field(default_factory=list)
    error_message: Optional[str] = None
    receipt_path: Optional[Path] = None
    search_key: Optional[str] = None
    proof_origin: Optional[str] = None
    explanation: Optional[str] = None
    synthesis_attempts: List[Dict[str, Any]] = Field(default_factory=list)
    counterexample_certificate: Optional[Dict[str, Any]] = None
    used_lemma_ids: List[str] = Field(default_factory=list)
    transitive_used_lemma_ids: List[str] = Field(default_factory=list)
    context_lemma_ids: List[str] = Field(default_factory=list)
    missing_lemmas: List[Dict[str, Any]] = Field(default_factory=list)
    reference_tracking: str = "source_identifier_references"

    @property
    def is_proven(self) -> bool:
        return self.status == "MACHINE_CHECKED_PROVEN" and self.is_machine_checked

    def to_dict(self) -> Dict[str, Any]:
        return {
            "status": self.status,
            "is_machine_checked": self.is_machine_checked,
            "theorem_name": self.theorem_name,
            "conjecture_id": self.conjecture_id,
            "successful_tactic": self.successful_tactic,
            "verified_file_path": str(self.verified_file_path) if self.verified_file_path else None,
            "attempts_count": self.attempts_count,
            "verification_time_ms": self.verification_time_ms,
            "lean_version": self.lean_version,
            "error_message": self.error_message,
            "receipt_path": str(self.receipt_path) if self.receipt_path else None,
            "diagnostics": self.diagnostics,
            "search_key": self.search_key,
            "proof_origin": self.proof_origin,
            "explanation": self.explanation,
            "synthesis_attempts": self.synthesis_attempts,
            "counterexample_certificate": self.counterexample_certificate,
            "used_lemma_ids": self.used_lemma_ids,
            "transitive_used_lemma_ids": self.transitive_used_lemma_ids,
            "context_lemma_ids": self.context_lemma_ids,
            "missing_lemmas": self.missing_lemmas,
            "reference_tracking": self.reference_tracking,
        }


class LeanToolchain:
    """Manages discovery and invocation of the local Lean 4 and Lake toolchain."""

    # Proof workers may synthesize concurrently; their memory-heavy compiler
    # subprocesses share two host slots, including independent replay.
    COMPILER_SLOTS = 2

    def __init__(
        self,
        lean_bin: Optional[Union[str, Path]] = None,
        lake_bin: Optional[Union[str, Path]] = None,
        workspace_dir: Optional[Union[str, Path]] = None,
    ) -> None:
        self.lean_bin = Path(lean_bin) if lean_bin else self._find_binary("lean")
        self.lake_bin = Path(lake_bin) if lake_bin else self._find_binary("lake")
        self.workspace_dir = (
            Path(workspace_dir).resolve()
            if workspace_dir
            else self._find_default_workspace()
        )
        self._lean_version: Optional[str] = None
        self._active_process = None
        self._cancelled = threading.Event()
        self._process_lock = threading.Lock()
        self._admission_handle = None
        self.last_run_metadata: Dict[str, Any] = {}

    def cancel(self):
        with self._process_lock:
            self._cancelled.set()
            terminate_process_group(self._active_process)
            self._active_process = None
            if self._admission_handle is not None:
                self._admission_handle.close()
                self._admission_handle = None

    def active_process_groups(self):
        return [self._active_process.pid] if self._active_process is not None else []

    @staticmethod
    def _find_binary(name: str) -> Optional[Path]:
        """Search ~/.elan/bin, PATH, and toolchain paths for binary without resolving symlinks."""
        # 1. Prefer ~/.elan/bin
        elan_candidate = Path.home() / ".elan" / "bin" / name
        if elan_candidate.is_file() and os.access(elan_candidate, os.X_OK):
            return elan_candidate

        # 2. Check PATH
        which_path = shutil.which(name)
        if which_path:
            return Path(which_path)

        # 3. Check ~/.elan/toolchains/*/bin
        toolchains_dir = Path.home() / ".elan" / "toolchains"
        if toolchains_dir.is_dir():
            for tc in sorted(toolchains_dir.iterdir(), reverse=True):
                candidate = tc / "bin" / name
                if candidate.is_file() and os.access(candidate, os.X_OK):
                    return candidate

        # 4. Check /opt/homebrew/bin or /usr/local/bin
        for prefix in [Path("/opt/homebrew/bin"), Path("/usr/local/bin")]:
            p = prefix / name
            if p.is_file() and os.access(p, os.X_OK):
                return p

        return None

    @staticmethod
    def _find_default_workspace() -> Path:
        """Locate default lean_workspace in repo."""
        repo_root = Path(__file__).resolve().parent.parent.parent
        return repo_root / "certified_lean"

    @property
    def is_available(self) -> bool:
        """True if Lean compiler is found and executable."""
        return self.lean_bin is not None and self.lean_bin.is_file()

    def get_version(self) -> str:
        """Return the detected Lean 4 version string."""
        if self._lean_version:
            return self._lean_version
        if not self.is_available or self.lean_bin is None:
            return "Unavailable"
        try:
            res = subprocess.run(
                [str(self.lean_bin), "--version"],
                cwd=self.workspace_dir,
                capture_output=True,
                text=True,
                timeout=5,
            )
            self._lean_version = res.stdout.strip() or res.stderr.strip()
            return self._lean_version
        except Exception as e:
            logger.warning("Failed to determine Lean version: %s", e)
            return "Unknown"

    def ensure_workspace_built(self) -> bool:
        """Only a pinned genuine Mathlib installation can certify research."""
        import json
        try:
            manifest = json.loads((self.workspace_dir / "lake-manifest.json").read_text())
            packages = manifest["packages"]
            mathlib = self.workspace_dir / ".lake/packages/mathlib"
            expected = "d13f23b723b8a846827a245b89c10fc7d3f11612"
            if not (any(p["name"] == "mathlib" and p.get("rev") == expected
                        and p.get("url") == "https://github.com/leanprover-community/mathlib4.git" for p in packages)
                    and not (self.workspace_dir / "Mathlib.lean").exists()
                    and (mathlib / ".lake/build/lib/lean/Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.olean").is_file()):
                return False
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=mathlib, capture_output=True, text=True, timeout=5, check=True)
            changes = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no"], cwd=mathlib,
                                     capture_output=True, text=True, timeout=5, check=True)
            return head.stdout.strip() == expected and not changes.stdout.strip()
        except (OSError, ValueError, KeyError, subprocess.SubprocessError):
            return False

    def run_lean_code(self, lean_code: str, timeout: float = 10.0) -> Tuple[int, str, str]:
        if not math.isfinite(timeout) or timeout <= 0:
            raise ValueError("Lean verification timeout must be finite and positive")
        started = time.monotonic()
        deadline = started + timeout
        self.last_run_metadata = {"compiler_launched": False, "compiler_slots": self.COMPILER_SLOTS,
                                  "admission_wait_sec": 0.0, "compiler_execution_sec": 0.0}
        if self._cancelled.is_set():
            raise InterruptedError("Lean verification cancelled before toolchain checks")
        available = self.is_available and self.lake_bin and self.ensure_workspace_built()
        if self._cancelled.is_set():
            raise InterruptedError("Lean verification cancelled during toolchain checks")
        if not available:
            return 1, "", "Pinned genuine Mathlib toolchain is unavailable; run lake update in certified_lean"
        if time.monotonic() >= deadline:
            self.last_run_metadata["failure_kind"] = "toolchain_check_timeout"
            return 124, "", "Lean verification budget exhausted during toolchain checks"
        key = hashlib.sha256(str(self.workspace_dir.resolve()).encode()).hexdigest()
        slots = Path(tempfile.gettempdir()) / f"math-foundry-lean-{os.getuid()}-{key}"
        slots.mkdir(mode=0o700, exist_ok=True)
        admitted = None
        waiting = time.monotonic()
        try:
            while admitted is None:
                if self._cancelled.is_set():
                    raise InterruptedError("Lean verification cancelled during compiler admission")
                if time.monotonic() >= deadline:
                    self.last_run_metadata["failure_kind"] = "compiler_admission_timeout"
                    return 124, "", "Lean compiler admission timed out; no compiler was launched"
                for index in range(self.COMPILER_SLOTS):
                    handle = (slots / f"{index}.lock").open("a")
                    try:
                        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except BlockingIOError:
                        handle.close()
                    except BaseException:
                        handle.close()
                        raise
                    else:
                        admitted = handle
                        break
                if admitted is None:
                    self._cancelled.wait(min(0.05, max(0.0, deadline - time.monotonic())))
            self.last_run_metadata["admission_wait_sec"] = time.monotonic() - waiting
            env = dict(os.environ)
            env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env.get("PATH", "")
            # Ignore inherited LEAN_PATH: a legacy shim must never shadow Mathlib.
            env.pop("LEAN_PATH", None)
            with self._process_lock:
                if self._cancelled.is_set():
                    raise InterruptedError("Lean verification cancelled before compiler launch")
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    self.last_run_metadata["failure_kind"] = "compiler_admission_timeout"
                    return 124, "", "Lean compiler admission timed out; no compiler was launched"
                self._admission_handle = admitted
                process = subprocess.Popen([str(self.lake_bin), "env", "lean", "--stdin"],
                    cwd=self.workspace_dir, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE, text=True, start_new_session=True)
                self._active_process = process
                self.last_run_metadata.update(compiler_launched=True, compiler_execution_budget_sec=remaining)
            executing = time.monotonic()
            try:
                if self._cancelled.is_set():
                    raise InterruptedError("Lean verification cancelled during compiler launch")
                remaining = deadline - time.monotonic()
                self.last_run_metadata["compiler_execution_budget_sec"] = max(0.0, remaining)
                if remaining <= 0:
                    raise subprocess.TimeoutExpired("Lean", timeout)
                stdout, stderr = process.communicate(lean_code, timeout=remaining)
                if self._cancelled.is_set():
                    raise InterruptedError("Lean verification cancelled during compilation")
                return process.returncode, stdout, stderr
            except subprocess.TimeoutExpired:
                self.last_run_metadata["failure_kind"] = "compiler_timeout"
                with self._process_lock:
                    if self._active_process is process:
                        terminate_process_group(process)
                    stdout, stderr = process.communicate()
                    self._active_process = None
                if self._cancelled.is_set():
                    raise InterruptedError("Lean verification cancelled during compiler timeout cleanup")
                return 124, stdout, stderr + "\nLean verification timed out"
            finally:
                with self._process_lock:
                    if self._active_process is process:
                        terminate_process_group(process)
                        self._active_process = None
                self.last_run_metadata["compiler_execution_sec"] = time.monotonic() - executing
        finally:
            if admitted is None:
                self.last_run_metadata["admission_wait_sec"] = time.monotonic() - waiting
            else:
                # Keep the slot until owned process-group cleanup has completed.
                # Never unlink lock files: competing processes must use one inode.
                with self._process_lock:
                    if self._active_process is None:
                        admitted.close()
                        self._admission_handle = None


class LeanProofSearch:
    """Automated tactic search engine and closed-loop formal prover for Lean 4."""

    REUSE_LIMIT = 6
    MAX_REUSE_BYTES = 96000
    GENERATED_RETRY_TIMEOUT_SEC = 30.0
    SEARCH_POLICY = "checked-candidate-context-guard-repair-helpers-v4"

    def __init__(
        self,
        toolchain: Optional[LeanToolchain] = None,
        workspace_dir: Optional[Union[str, Path]] = None,
        lean_bin: Optional[Union[str, Path]] = None,
        lake_bin: Optional[Union[str, Path]] = None,
        max_attempts: int = 35,
        timeout_per_attempt: float = 10.0,
        flywheel: Optional[Any] = None,
        auto_register_flywheel: bool = True,
        synthesizer: Optional[Any] = None,
        total_timeout_sec: Optional[float] = None,
    ) -> None:
        self.toolchain = toolchain or LeanToolchain(
            lean_bin=lean_bin,
            lake_bin=lake_bin,
            workspace_dir=workspace_dir,
        )
        self.max_attempts = max_attempts
        self.timeout_per_attempt = timeout_per_attempt
        if not isinstance(max_attempts, int) or max_attempts < 0 or not math.isfinite(timeout_per_attempt) or timeout_per_attempt <= 0:
            raise ValueError("Fixed tactic attempts and per-attempt timeouts must be finite and nonnegative/positive")
        self.flywheel = flywheel
        self.auto_register_flywheel = auto_register_flywheel
        self.synthesizer = synthesizer
        self.total_timeout_sec = total_timeout_sec
        if total_timeout_sec is not None and (not math.isfinite(total_timeout_sec) or total_timeout_sec <= 0):
            raise ValueError("The shared proof-search budget must be finite and positive")

        if self.toolchain.is_available:
            self.toolchain.ensure_workspace_built()

    def is_available(self) -> bool:
        """Check if formal proof search engine has an active Lean 4 compiler."""
        return self.toolchain.is_available

    def cancel(self):
        if self.synthesizer is not None:
            self.synthesizer.cancel()
        self.toolchain.cancel()

    def active_process_groups(self):
        return self.toolchain.active_process_groups() + (self.synthesizer.active_process_groups() if self.synthesizer else [])

    @staticmethod
    def _guard_key(conjecture):
        from autonomous_math.prover.trusted_lean import render_guard
        return render_guard(getattr(conjecture, "guard_predicate", None))

    def generate_candidate_scripts(self, lean_code, conjecture=None):
        from autonomous_math.prover.trusted_lean import GENERAL_TACTICS, TRUSTED_TACTICS, goal_specific_tactics
        tactics = goal_specific_tactics(conjecture) + GENERAL_TACTICS if conjecture is not None else TRUSTED_TACTICS
        return [LeanProofScript(name=f"trusted_{i}", tactic_code=t, category="mathlib")
                for i,t in enumerate(tactics)]

    def _checked_library(self):
        """Validate receipts before using their statements or source declarations."""
        if self.flywheel is None:
            return []
        from autonomous_math.core.ast import Conjecture
        from autonomous_math.research_state import validate_receipt
        receipts, fingerprints = [], {}
        for lemma in self.flywheel.lemmas.values():
            receipt, _ = validate_receipt(getattr(lemma, "receipt_path", ""), lemma.lemma_id, fingerprints)
            if receipt and receipt.get("conjecture"):
                previous = Conjecture.from_dict(receipt["conjecture"])
                if previous.id == receipt["conjecture_id"]:
                    receipts.append(dict(receipt, receipt_path=str(lemma.receipt_path),
                                         helper_for=getattr(lemma, "helper_for", [])))
        return receipts

    @staticmethod
    def _oriented_bound(conjecture):
        if conjecture.rel == "<=":
            return conjecture.lhs_expr, conjecture.rhs_expr
        if conjecture.rel == ">=":
            return conjecture.rhs_expr, conjecture.lhs_expr
        return None

    @classmethod
    def _composition_parents(cls, conjecture, receipts):
        """Metadata suggests parents; exact checked ASTs must establish the chain."""
        from autonomous_math.core.ast import Conjecture
        metadata = getattr(conjecture, "metadata", {})
        parents = metadata.get("parents")
        if (metadata.get("origin") != "checked_transitivity" or not isinstance(parents, list)
                or len(parents) != 2 or any(not isinstance(p, str) for p in parents)
                or len(set(parents)) != 2 or conjecture.id in parents or cls._oriented_bound(conjecture) is None):
            return []
        by_id = {r.get("conjecture_id"): r for r in receipts}
        if any(p not in by_id for p in parents):
            return []
        selected = [by_id[p] for p in parents]
        bounds = []
        for receipt in selected:
            previous = Conjecture.from_dict(receipt["conjecture"])
            guard = cls._guard_key(previous)
            if guard is not None and guard != cls._guard_key(conjecture):
                return []
            bound = cls._oriented_bound(previous)
            if bound is None:
                return []
            bounds.append(bound)
        left, right = cls._oriented_bound(conjecture)
        if (left.to_dict() != bounds[0][0].to_dict()
                or bounds[0][1].to_dict() != bounds[1][0].to_dict()
                or right.to_dict() != bounds[1][1].to_dict()):
            return []
        return selected

    @staticmethod
    def _subexpressions(node):
        result = {node.canonical_key}
        for attribute in ("left", "right", "child"):
            child = getattr(node, attribute, None)
            if child is not None:
                result.update(LeanProofSearch._subexpressions(child))
        return result

    def _select_reuse(self, conjecture, library, theorem_name=None):
        from autonomous_math.core.ast import Conjecture
        from autonomous_math.prover.trusted_lean import bound_signature
        if theorem_name is None and conjecture is not None:
            theorem_name = re.sub(r"[^a-zA-Z0-9_]", "_", conjecture.id)
            if not theorem_name or theorem_name[0].isdigit():
                theorem_name = "thm_" + theorem_name
        variables = (conjecture.lhs_expr.variables | conjecture.rhs_expr.variables) if conjecture is not None else None
        subexpressions = (self._subexpressions(conjecture.lhs_expr) | self._subexpressions(conjecture.rhs_expr)
                          if conjecture is not None else set())
        endpoints = ({conjecture.lhs_expr.canonical_key, conjecture.rhs_expr.canonical_key}
                     if conjecture is not None else set())
        parents = self._composition_parents(conjecture, library) if conjecture is not None else []
        if parents:
            return parents
        # Proposal metadata can prioritize an already checked declaration. It
        # cannot admit a new theorem or supply that theorem's guard premises.
        from autonomous_math.conjecturing.model_proposals import proposal_statement_key
        bindings = ((conjecture.metadata.get("spectral_refinement") or {}).get("parent_bindings", [])
                    if conjecture is not None else [])
        refinement_parents = set()
        if isinstance(bindings, list) and len(bindings) <= 2:
            for binding in bindings:
                if not isinstance(binding, dict):
                    continue
                for receipt in library:
                    if (binding.get("parent_id") == receipt.get("conjecture_id")
                            and all(binding.get(key) is not None and binding[key] == receipt.get(key) for key in
                                ("receipt_path", "theorem_name", "source_sha256", "challenge_sha256",
                                 "workspace_sha256", "lean_binary_sha256"))
                            and binding.get("statement_key") == proposal_statement_key(Conjecture.from_dict(receipt["conjecture"]))):
                        refinement_parents.add(receipt["conjecture_id"])
        receipts = []
        for receipt in library:
            if receipt["theorem_name"] == theorem_name:
                continue
            previous = Conjecture.from_dict(receipt["conjecture"])
            previous_guard = self._guard_key(previous)
            # Declarations retain their own guards. Merely retrieving a theorem
            # never supplies its premises; applications still need a kernel proof.
            guard_mismatch = previous_guard is not None and previous_guard != self._guard_key(conjecture)
            helper_for_target = conjecture is not None and conjecture.id in (
                previous.metadata.get("helper_for", []) + receipt.get("helper_for", []))
            previous_variables = previous.lhs_expr.variables | previous.rhs_expr.variables
            if variables is not None and not (variables & previous_variables) and not helper_for_target:
                continue
            exact = conjecture is not None and bound_signature(previous) == bound_signature(conjecture)
            shared = len(variables & previous_variables) if variables is not None else 0
            previous_endpoints = {previous.lhs_expr.canonical_key, previous.rhs_expr.canonical_key}
            structural = len(subexpressions & previous_endpoints)
            receipts.append((not exact, receipt["conjecture_id"] not in refinement_parents, not helper_for_target,
                -len(endpoints & previous_endpoints), -structural, -shared, guard_mismatch,
                len(previous_variables - (variables or set())), receipt["theorem_name"], receipt))
        # Variable overlap is the bounded fallback when no endpoint/subexpression matches.
        ranked = sorted(receipts, key=lambda item: item[:-1])
        if ranked and not ranked[0][0]:
            return [ranked[0][-1]]
        return [item[-1] for item in ranked][:self.REUSE_LIMIT]

    def _validated_reuse(self, conjecture=None, theorem_name=None):
        return self._select_reuse(conjecture, self._checked_library(), theorem_name)

    @staticmethod
    def _identifier_references(body, names):
        # This is observed text, not a claim that any premise was logically necessary.
        code, index = [], 0
        while index < len(body):
            if body.startswith("--", index):
                end = body.find("\n", index)
                index = len(body) if end < 0 else end
                code.append(" ")
            elif body.startswith("/-", index):
                depth, index = 1, index + 2
                while index < len(body) and depth:
                    if body.startswith("/-", index):
                        depth, index = depth + 1, index + 2
                    elif body.startswith("-/", index):
                        depth, index = depth - 1, index + 2
                    else:
                        index += 1
                code.append(" ")
            elif body[index] == '"':
                index += 1
                while index < len(body):
                    if body[index] == "\\":
                        index += 2
                    elif body[index] == '"':
                        index += 1
                        break
                    else:
                        index += 1
                code.append(" ")
            else:
                code.append(body[index])
                index += 1
        tokens = {token.removeprefix("_root_.") for token in
                  re.findall(r"[a-zA-Z_][a-zA-Z0-9_'.]*", "".join(code))}
        return set(names) & tokens

    @classmethod
    def _reuse_context(cls, challenge, receipts, library=()):
        """Keep selected declarations and their checked source dependency closure."""
        base_challenge = challenge
        declarations, imports, scopes = {}, set(re.findall(r"^import .+$", challenge, re.MULTILINE)), set()
        for receipt in receipts:
            previous = Path(receipt["source_path"]).read_text()
            imports.update(re.findall(r"^import .+$", previous, re.MULTILINE))
            body = re.sub(r"^import .+$", "", previous, flags=re.MULTILINE)
            scopes.update(re.findall(r"^open scoped BigOperators$", body, re.MULTILINE))
            body = re.sub(r"^open scoped BigOperators$", "", body, flags=re.MULTILINE)
            for block in re.split(r"(?=^theorem )", body, flags=re.MULTILINE):
                block = block.strip()
                if not block:
                    continue
                match = re.match(r"theorem\s+([a-zA-Z0-9_]+)\s", block)
                if not match:
                    raise ValueError("Only generated self-contained graph proofs may be reused")
                name = match[1]
                if name in declarations and declarations[name] != block:
                    raise ValueError(f"Conflicting checked lemma declarations: {name}")
                declarations.setdefault(name, block)
        dependencies = {name: cls._identifier_references(block.split(":= by", 1)[-1], declarations) - {name}
                        for name, block in declarations.items()}
        ordered, visiting = [], set()
        def include(name):
            if name in ordered:
                return
            if name in visiting or name not in declarations:
                raise ValueError("Missing or cyclic checked lemma dependency")
            visiting.add(name)
            for dependency in sorted(dependencies[name]):
                include(dependency)
            visiting.remove(name)
            ordered.append(name)
        for receipt in receipts:
            include(receipt["theorem_name"])
        names_to_ids = {receipt["theorem_name"]: receipt["conjecture_id"] for receipt in library}
        context = {"dependencies": dependencies, "names_to_ids": names_to_ids,
                   "names": set(ordered), "selected_count": len(receipts),
                   "selected_names": {receipt["theorem_name"] for receipt in receipts}}
        if ordered:
            challenge = "\n".join(sorted(imports)) + "\n" + re.sub(r"^import .+$", "", challenge, flags=re.MULTILINE)
            index = challenge.index("theorem ")
            prelude = "".join(line + "\n" for line in sorted(scopes) if line not in challenge[:index].splitlines())
            challenge = challenge[:index] + prelude + "\n\n".join(declarations[name] for name in ordered) + "\n" + challenge[index:]
        if len(challenge.encode()) > cls.MAX_REUSE_BYTES and receipts:
            return cls._reuse_context(base_challenge, receipts[:-1], library)
        return challenge, context

    @classmethod
    def _prune_context(cls, challenge, theorem_name, body, context):
        """Compile referenced checked proofs, preserving imports and the exact target."""
        names = context["names"]
        if not names or re.search(
                r"\b(?:exact|apply)\?|\b(?:library_search|aesop|simp_all|solve_by_elim|apply_rules|"
                r"run_tac|run_elab|run_meta|run_cmd|mkConst|eval_tactic)\b|\bLean\.", body):
            return challenge, context
        needed, visiting = set(), set()
        def include(name):
            if name in visiting or name not in names:
                raise ValueError("Missing or cyclic checked candidate dependency")
            if name in needed:
                return
            if name not in context.get("dependencies", {}):
                raise ValueError("Missing checked candidate dependency graph")
            visiting.add(name)
            for parent in context["dependencies"][name]:
                include(parent)
            visiting.remove(name)
            needed.add(name)
        for name in cls._identifier_references(body, names):
            include(name)
        declarations = list(re.finditer(r"(?m)^theorem\s+([a-zA-Z0-9_]+)\s", challenge))
        if (not declarations or declarations[-1][1] != theorem_name
                or len(declarations) != len(names) + 1
                or {m[1] for m in declarations[:-1]} != names):
            raise ValueError("Checked candidate context declarations changed")
        pieces = [challenge[:declarations[0].start()]]
        for index, declaration in enumerate(declarations[:-1]):
            if declaration[1] in needed:
                pieces.append(challenge[declaration.start():declarations[index+1].start()])
        pieces.append(challenge[declarations[-1].start():])
        selected = context.get("selected_names", names) & needed
        actual = dict(context, names=needed, selected_names=selected, selected_count=len(selected))
        return "".join(pieces), actual

    @classmethod
    def _reference_tracking(cls, candidate, theorem_name, context):
        offset = candidate.rindex(f"theorem {theorem_name} ")
        body = candidate[offset:].split(":= by", 1)[-1]
        direct = cls._identifier_references(body, context["names"])
        all_used = set(direct)
        pending = list(direct)
        while pending:
            for dependency in context["dependencies"].get(pending.pop(), ()):
                if dependency not in all_used:
                    all_used.add(dependency)
                    pending.append(dependency)
        ids = context["names_to_ids"]
        return {"used_lemma_ids": sorted({ids[name] for name in direct if name in ids}),
                "transitive_used_lemma_ids": sorted({ids[name] for name in all_used - direct if name in ids}),
                "context_lemma_ids": sorted({ids[name] for name in context["names"] if name in ids}),
                "reference_tracking": "source_identifier_references"}

    @classmethod
    def _reuse_tactics(cls, receipts, conjecture=None):
        from autonomous_math.core.ast import Conjecture
        applications = []
        for receipt in receipts:
            previous = Conjecture.from_dict(receipt["conjecture"]) if receipt.get("conjecture") else None
            guard = cls._guard_key(previous)
            premise = ""
            if guard is not None:
                premise = " h_guard" if guard == cls._guard_key(conjecture) else " (by first | aesop | linarith)"
            applications.append(receipt["theorem_name"] + " G" + premise)
        # Nonnegative natural invariants make polynomial consequences of checked
        # inequalities available without adding unverified graph assumptions.
        naturals = ("Fintype.card V", "G.edgeFinset.card", "G.maxDegree", "G.cliqueNum", "G.chromaticNumber.toNat")
        nonnegative = ", ".join(f"(show (0 : ℝ) ≤ ({value} : ℝ) from Nat.cast_nonneg _)" for value in naturals)
        finish = f"nlinarith [{nonnegative}]"
        tactics = []
        if len(applications) > 1:
            tactics.append("; ".join(f"have checked_{i} := {application}" for i, application in enumerate(applications)) + "; " + finish)
        for application in applications:
            tactics.extend([f"have h := {application}; {finish}", f"exact {application}"])
        return tactics

    def candidate_tactics(self, conjecture=None, receipts=()):
        """Reserve a fair share of a small budget for fresh tactic search."""
        from autonomous_math.prover.trusted_lean import GENERAL_TACTICS, goal_specific_tactics
        direct = goal_specific_tactics(conjecture)
        reuse = self._reuse_tactics(receipts, conjecture)
        parents = self._composition_parents(conjecture, receipts) if conjecture is not None else []
        transitivity = []
        if parents:
            from autonomous_math.core.ast import Conjecture
            applications = [receipt["theorem_name"] + " G" +
                            (" h_guard" if self._guard_key(Conjecture.from_dict(receipt["conjecture"])) is not None else "")
                            for receipt in parents]
            transitivity = [f"exact le_trans ({applications[0]}) ({applications[1]})"]
        scheduled = transitivity + list(direct)
        for index in range(max(len(reuse), len(GENERAL_TACTICS))):
            if index < len(reuse):
                scheduled.append(reuse[index])
            if index < len(GENERAL_TACTICS):
                scheduled.append(GENERAL_TACTICS[index])
        return list(dict.fromkeys(scheduled))[:max(0, self.max_attempts)]

    def search_key(self, conjecture):
        """Bind negative search caching to the goal, actual proofs and toolchain."""
        import hashlib
        import json
        from autonomous_math.prover import trusted_lean
        from autonomous_math.research_state import sha256, workspace_fingerprint
        receipts = self._validated_reuse(conjecture)
        actual_bin = subprocess.run([str(Path.home()/".elan/bin/elan"), "which", "lean"],
            cwd=self.toolchain.workspace_dir, capture_output=True, text=True, timeout=5, check=True).stdout.strip()
        payload = {
            "goal": {"lhs": conjecture.lhs_expr.to_dict(), "rel": conjecture.rel,
                     "rhs": conjecture.rhs_expr.to_dict(), "guard": conjecture.to_dict()["guard_predicate"]},
            "tactics": self.candidate_tactics(conjecture, receipts),
            "reused_proofs": [{key: receipt[key] for key in
                               ("theorem_name", "source_sha256", "challenge_sha256", "workspace_sha256")}
                              for receipt in receipts],
            "max_attempts": self.max_attempts, "timeout_per_attempt": self.timeout_per_attempt,
            "total_timeout_sec": self.total_timeout_sec,
            "synthesizer": self.synthesizer.configuration_fingerprint() if self.synthesizer else None,
            "policy": {"revision": self.SEARCH_POLICY, "reuse_limit": self.REUSE_LIMIT,
                       "first_fixed_timeout_retry": True,
                       "generated_timeout_retry_sec": self.GENERATED_RETRY_TIMEOUT_SEC},
            "compiler": sha256(Path(actual_bin)),
            "dependencies": workspace_fingerprint(self.toolchain.workspace_dir),
            "counterexample_checker": sha256(Path(__file__).resolve().parents[1] / "sieve/model_counterexamples.py"),
            "translator": sha256(Path(trusted_lean.__file__)), "search": sha256(Path(__file__)),
        }
        return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()

    @staticmethod
    def _repair_progress(diagnostics):
        rounds = {}
        for d in diagnostics:
            if d.get("phase", "").startswith("codex_synthesis"):
                # Exact-byte retry belongs to the same model attempt.
                if d["phase"] == "codex_synthesis":
                    rounds[len(rounds)] = d
                elif rounds:
                    rounds[max(rounds)] = d
        if len(rounds) < 2:
            return False
        before, after = list(rounds.values())[-2:]
        if after.get("failure_kind") != "compiler_rejection":
            return False
        a, b = before.get("error_count", 0), after.get("error_count", 0)
        # Different candidate dependency closures must not manufacture progress
        # merely by moving the target farther down the source file.
        line = lambda row: row.get("first_target_error_line", row.get("first_error_line")) or 0
        return (a > b > 0 or (0 < b <= a and line(after) > line(before)))

    def prove_challenge(self, target, output_dir=None, conjecture_id=None,
                        save_verified_artifact=True, conjecture=None, total_timeout_sec=None) -> LeanVerificationResult:
        """Check the exact translated target and its transitive kernel axioms."""
        import hashlib
        import json
        from autonomous_math.prover.trusted_lean import render_challenge
        from autonomous_math.research_state import ALLOWED_AXIOMS, atomic_save_json, sha256, workspace_fingerprint
        t0 = time.monotonic()
        obj = conjecture or (getattr(target, "conjecture", target) if not isinstance(target, (str, Path)) else None)
        cid = conjecture_id or getattr(obj, "id", "lean_challenge")
        theorem_name = "main_theorem"
        diagnostics = []
        synthesis_attempts = []
        search_key = None
        context = {"dependencies": {}, "names_to_ids": {}, "names": set(), "selected_count": 0}
        configured_budget = self.total_timeout_sec
        if configured_budget is None and self.synthesizer is not None:
            configured_budget = (self.max_attempts * self.timeout_per_attempt +
                self.synthesizer.max_rounds * (self.synthesizer.timeout_per_request + self.timeout_per_attempt))
        budget = total_timeout_sec if total_timeout_sec is not None else configured_budget
        if budget is not None and (not math.isfinite(budget) or budget <= 0):
            raise ValueError("The shared proof-search budget must be finite and positive")
        deadline = t0 + budget if budget is not None else math.inf
        def outcome(status, error=None, **kw):
            return LeanVerificationResult(status=status, is_machine_checked=status == "MACHINE_CHECKED_PROVEN",
                theorem_name=theorem_name, conjecture_id=cid,
                verification_time_ms=(time.monotonic()-t0)*1000, diagnostics=diagnostics,
                error_message=error, search_key=search_key, synthesis_attempts=synthesis_attempts, **kw)

        def exhausted(tactic, stage):
            if not diagnostics or diagnostics[-1].get("phase") != "shared_budget":
                diagnostics.append({"exit_code": 124, "phase": "shared_budget", "stage": stage,
                    "tactic": tactic, "success": False, "compiler_launched": False,
                    "stdout": "", "stderr": "Shared proof-search budget exhausted before compiler launch", "axioms": []})

        def verify(candidate, tactic, phase, attempt_dir=None, timeout=None, artifact_name="compiler.json", compiled_context=None):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                exhausted(tactic, phase)
                return False, []
            compiler_timeout = min(timeout if timeout is not None else self.timeout_per_attempt, remaining)
            compiler_started = time.monotonic()
            ret, stdout, stderr = self.toolchain.run_lean_code(
                candidate + f"\n#print axioms {full_name}\n", timeout=compiler_timeout)
            compiler_elapsed = time.monotonic() - compiler_started
            transport = getattr(self.toolchain, "last_run_metadata", {})
            axioms, audit_error = _target_axiom_report(stdout, full_name)
            valid = (ret == 0 and "error:" not in stdout+stderr and "declaration uses" not in stdout+stderr
                and audit_error is None and set(axioms).issubset(ALLOWED_AXIOMS))
            actual_context = context if compiled_context is None else compiled_context
            first_error_line = next((int(m) for m in re.findall(r"<stdin>:(\d+):\d+: error:", stdout)), None)
            target = list(re.finditer(r"\btheorem\s+" + re.escape(theorem_name) + r"(?=\s|[({:])", candidate))[-1]
            target_line = candidate[:target.start()].count("\n") + 1
            diagnostic = {"exit_code": ret, "tactic": tactic, "axioms": axioms, "phase": phase,
                          "stdout": stdout[-4000:], "stderr": stderr[-2000:], "success": valid,
                          "axiom_audit_error": audit_error, "compiler_launched": transport.get("compiler_launched", True),
                          "compiler_timeout_sec": compiler_timeout,
                          "verification_elapsed_sec": compiler_elapsed,
                          "compiler_elapsed_sec": transport.get("compiler_execution_sec", compiler_elapsed),
                          "compiler_admission_wait_sec": transport.get("admission_wait_sec", 0.0),
                          "compiler_execution_budget_sec": transport.get("compiler_execution_budget_sec", compiler_timeout),
                          "compiler_slots": transport.get("compiler_slots"), "candidate_bytes": len(candidate.encode()),
                          "error_count": len(re.findall(r"(?:^|\n).*?error:", stdout + stderr)),
                          "first_error_line": first_error_line,
                          "first_target_error_line": first_error_line - target_line + 1
                              if first_error_line is not None and first_error_line >= target_line else None,
                          "failure_kind": transport.get("failure_kind", "compiler_timeout") if ret == 124 else (None if valid else "compiler_rejection"),
                          "selected_lemma_count": actual_context["selected_count"], "context_declaration_count": len(actual_context["names"])}
            diagnostics.append(diagnostic)
            if attempt_dir is not None:
                atomic_save_json({**diagnostic, "stdout": stdout, "stderr": stderr}, attempt_dir / artifact_name)
            return valid, axioms

        def finish(candidate, checked_challenge, tactic, axioms, origin, explanation=None, compiled_context=None):
            tracking = self._reference_tracking(candidate, theorem_name, context if compiled_context is None else compiled_context)
            if not save_verified_artifact:
                return outcome("MACHINE_CHECKED_PROVEN", successful_tactic=tactic or "pre-existing_proof",
                    verified_lean_code=candidate, attempts_count=sum(d.get("compiler_launched", True) for d in diagnostics), lean_version=self.toolchain.get_version(),
                    proof_origin=origin, explanation=explanation, **tracking)
            out = Path(output_dir or "research_outputs/verified").resolve()
            out.mkdir(parents=True, exist_ok=True)
            key = hashlib.sha256(candidate.encode()).hexdigest()
            source = out / f"{key}.lean"
            trusted = out / f"{key}.challenge.lean"
            from autonomous_math.research_state import atomic_save_text
            atomic_save_text(candidate, source)
            atomic_save_text(checked_challenge, trusted)
            actual_bin = subprocess.run([str(Path.home()/".elan/bin/elan"), "which", "lean"],
                cwd=self.toolchain.workspace_dir, capture_output=True, text=True, timeout=5, check=True).stdout.strip()
            receipt = {"schema_version": 1, "status": "KERNEL_VERIFIED", "conjecture_id": cid,
                "theorem_name": full_name, "axioms": axioms, "statement_checked": True,
                "source_path": str(source), "source_sha256": sha256(source),
                "challenge_path": str(trusted), "challenge_sha256": sha256(trusted),
                "workspace": str(self.toolchain.workspace_dir),
                "workspace_sha256": workspace_fingerprint(self.toolchain.workspace_dir),
                "lean_binary": actual_bin, "lean_binary_sha256": sha256(Path(actual_bin)),
                "lean_version": self.toolchain.get_version(), "tactic": tactic or "pre-existing_proof",
                "duration_ms": (time.monotonic()-t0)*1000, "diagnostics": diagnostics,
                "conjecture": obj.to_dict() if obj is not None else None, "search_key": search_key,
                "proof_origin": origin, "synthesis_attempts": synthesis_attempts,
                "explanation": explanation, "explanation_status": "MODEL_GENERATED_UNREVIEWED" if explanation else None,
                **tracking}
            receipt_path = out / f"{key}.receipt.json"
            atomic_save_json(receipt, receipt_path)
            result = outcome("MACHINE_CHECKED_PROVEN", successful_tactic=tactic or "pre-existing_proof",
                verified_lean_code=candidate, verified_file_path=source, receipt_path=receipt_path,
                attempts_count=sum(d.get("compiler_launched", True) for d in diagnostics), lean_version=self.toolchain.get_version(),
                proof_origin=origin, explanation=explanation, **tracking)
            if self.flywheel is not None and self.auto_register_flywheel:
                self.flywheel.register_lemma(obj or cid, tactic=tactic or "pre-existing_proof",
                    conjecture_id=cid, theorem_name=full_name, receipt_path=receipt_path)
            return result
        try:
            if obj is not None:
                challenge, theorem_name = render_challenge(obj)
            elif isinstance(target, Path) or (isinstance(target, str) and "\n" not in target):
                challenge = Path(target).read_text()
                cid = conjecture_id or Path(target).stem
            else:
                challenge = str(target)
            declarations = re.findall(r"\btheorem\s+([a-zA-Z0-9_.]+)", challenge)
            if len(declarations) != 1:
                return outcome("UNRESOLVED", "Certification requires one explicit target theorem")
            theorem_name = declarations[0]
            namespaces = re.findall(r"^namespace\s+(\w+)", challenge, re.MULTILINE)
            full_name = ".".join(namespaces + [theorem_name])
            if not self.toolchain.ensure_workspace_built():
                return outcome("TOOLCHAIN_UNAVAILABLE", "Pinned genuine Mathlib installation is not ready")
            if obj is not None:
                search_key = self.search_key(obj)
            library = self._checked_library()
            receipts = self._select_reuse(obj, library, full_name)
            challenge, context = self._reuse_context(challenge, receipts, library)
            receipts = [r for r in receipts if r["theorem_name"] in context["names"]]
            scripts = self.candidate_tactics(obj, receipts) if re.search(r"\bsorry\b", challenge) else [None]
            for index, tactic in enumerate(scripts):
                if time.monotonic() >= deadline:
                    exhausted(tactic, "fixed_tactic")
                    break
                compiled_challenge, compiled_context = (self._prune_context(challenge, theorem_name, tactic, context)
                    if tactic is not None else (challenge, context))
                candidate = re.sub(r"\bsorry\b", lambda _: tactic or "", compiled_challenge, count=1) if tactic else compiled_challenge
                if re.search(r"\bsorry\b", candidate):
                    continue
                valid, axioms = verify(candidate, tactic, "fixed_tactic", compiled_context=compiled_context)
                if (not valid and index == 0
                        and diagnostics[-1].get("failure_kind") in {"compiler_timeout", "compiler_admission_timeout"}
                        and time.monotonic() < deadline
                        and self.GENERATED_RETRY_TIMEOUT_SEC > self.timeout_per_attempt):
                    valid, axioms = verify(candidate, tactic, "fixed_tactic_timeout_retry",
                        timeout=self.GENERATED_RETRY_TIMEOUT_SEC, compiled_context=compiled_context)
                if not valid:
                    continue
                return finish(candidate, compiled_challenge, tactic, axioms, "fixed_tactic" if tactic else "pre_existing", compiled_context=compiled_context)
            if self.synthesizer is not None and obj is not None and re.search(r"\bsorry\b", challenge):
                from autonomous_math.research_state import atomic_save_text
                synthesis_root = Path(output_dir or "research_outputs/verified").resolve() / "synthesis" / uuid.uuid4().hex
                feedback = list(diagnostics)
                self.synthesizer.conjecture = obj
                for round_index in range(self.synthesizer.max_rounds):
                    if round_index >= 2 and not self._repair_progress(diagnostics):
                        break  # Spend a third request only on demonstrated compiler progress.

                    if time.monotonic() >= deadline:
                        exhausted(None, "codex_synthesis")
                        break
                    attempt_dir = synthesis_root / f"round_{round_index + 1}"
                    trace = None
                    response_kind = None
                    try:
                        data, trace = self.synthesizer.generate_candidate(challenge, feedback, attempt_dir, deadline)
                        synthesis_attempts.append(trace)
                        response_kind = data.get("outcome") if isinstance(data, dict) else None
                        data = validate_synthesis_response(data, self.synthesizer.allowed_imports)
                        trace["response_outcome"] = data["outcome"]
                        if data["outcome"] == "unknown":
                            trace.update(status="MODEL_UNKNOWN")
                            atomic_save_json(trace, attempt_dir / "trace.json")
                            return outcome("UNRESOLVED", "Model returned unknown without a proof or counterexample",
                                attempts_count=sum(d.get("compiler_launched", True) for d in diagnostics),
                                explanation=data["explanation"], missing_lemmas=data.get("missing_lemmas", []))
                        if data["outcome"] == "counterexample":
                            from autonomous_math.sieve.model_counterexamples import verify_model_counterexample
                            if time.monotonic() >= deadline:
                                exhausted(None, "model_counterexample")
                                trace.update(status="COUNTEREXAMPLE_INCONCLUSIVE", error="Shared budget exhausted before graph verification")
                                atomic_save_json(trace, attempt_dir / "trace.json")
                                break
                            certificate = verify_model_counterexample(data["counterexample"], obj)
                            if time.monotonic() >= deadline:
                                exhausted(None, "model_counterexample")
                                trace.update(status="COUNTEREXAMPLE_INCONCLUSIVE", error="Shared budget exhausted during graph verification")
                                atomic_save_json(trace, attempt_dir / "trace.json")
                                break
                            certificate_data = json.loads(certificate.to_json())
                            certificate_path = attempt_dir / "counterexample.json"
                            atomic_save_json(certificate_data, certificate_path)
                            trace.update(status="COUNTEREXAMPLE_VERIFIED", counterexample_path=str(certificate_path),
                                counterexample_sha256=sha256(certificate_path))
                            atomic_save_json(trace, attempt_dir / "trace.json")
                            return outcome("REFUTED", counterexample_certificate=certificate_data,
                                attempts_count=sum(d.get("compiler_launched", True) for d in diagnostics),
                                explanation=data["explanation"])
                        imports = [f"import {module}" for module in data["imports"]
                                   if f"import {module}" not in challenge.splitlines()]
                        checked_challenge = ("\n".join(imports) + "\n" if imports else "") + challenge
                        body = data["proof_body"]
                        checked_challenge, compiled_context = self._prune_context(checked_challenge, theorem_name, body, context)
                        placeholders = list(re.finditer(r"(?m)^([ \t]*)sorry[ \t]*(?:\n|$)", checked_challenge))
                        if len(placeholders) != 1:
                            raise ValueError("Synthesis requires one isolated trusted proof placeholder")
                        placeholder = placeholders[0]
                        candidate = (checked_challenge[:placeholder.start()] + textwrap.indent(body, placeholder[1]) +
                                     "\n" + checked_challenge[placeholder.end():])
                        target_offset = checked_challenge.rindex(f"theorem {theorem_name} ")
                        delimiter = checked_challenge.index(":= by", target_offset)
                        if candidate[:delimiter] != checked_challenge[:delimiter]:
                            raise ValueError("Generated proof altered the trusted challenge prefix")
                        atomic_save_text(candidate, attempt_dir / "candidate.lean")
                        atomic_save_text(checked_challenge, attempt_dir / "challenge.lean")
                        retry_launched = False
                        valid, axioms = verify(candidate, body, "codex_synthesis", attempt_dir, compiled_context=compiled_context)
                        if (not valid and diagnostics[-1].get("failure_kind") in {"compiler_timeout", "compiler_admission_timeout"}
                                and time.monotonic() < deadline
                                and self.GENERATED_RETRY_TIMEOUT_SEC > self.timeout_per_attempt):
                            valid, axioms = verify(candidate, body, "codex_synthesis_timeout_retry", attempt_dir,
                                timeout=self.GENERATED_RETRY_TIMEOUT_SEC, artifact_name="compiler_retry.json", compiled_context=compiled_context)
                            retry_launched = diagnostics[-1].get("compiler_launched", False)
                        timed_out = not valid and diagnostics[-1].get("failure_kind") == "compiler_timeout"
                        admission_timeout = not valid and diagnostics[-1].get("failure_kind") == "compiler_admission_timeout"
                        trace.update(status="KERNEL_ACCEPTED" if valid else ("COMPILER_ADMISSION_TIMEOUT" if admission_timeout else "COMPILER_TIMEOUT" if timed_out else "KERNEL_REJECTED"),
                                     compiler_retry=retry_launched,
                                     candidate_sha256=hashlib.sha256(candidate.encode()).hexdigest())
                        atomic_save_json(trace, attempt_dir / "trace.json")
                        if valid:
                            return finish(candidate, checked_challenge, body, axioms, "codex_synthesis", data["explanation"], compiled_context=compiled_context)
                        feedback.append(diagnostics[-1] if diagnostics else {"error": "Compiler budget exhausted"})
                    except (SynthesisError, ValueError) as exc:
                        trace = (exc.trace if isinstance(exc, SynthesisError) and exc.trace else trace) or {}
                        trace.update(error=str(exc), artifact_path=str(attempt_dir))
                        if not isinstance(exc, SynthesisError):
                            trace["status"] = "COUNTEREXAMPLE_REJECTED" if response_kind == "counterexample" else "PROOF_BODY_REJECTED"
                        if not synthesis_attempts or synthesis_attempts[-1] is not trace:
                            synthesis_attempts.append(trace)
                        if attempt_dir.is_dir() and not attempt_dir.resolve().is_relative_to(self.toolchain.workspace_dir.resolve()):
                            atomic_save_json(trace, attempt_dir / "trace.json")
                        rejected = {"phase": "model_counterexample" if trace.get("status") == "COUNTEREXAMPLE_REJECTED" else "model_validation",
                            "error": str(exc), "success": False, "compiler_launched": False}
                        if rejected["phase"] == "model_counterexample":
                            diagnostics.append(rejected)
                        feedback.append(rejected)
            error = "Shared proof-search budget exhausted" if time.monotonic() >= deadline else "No proof with the required statement and permitted axioms"
            return outcome("UNRESOLVED", error, attempts_count=sum(d.get("compiler_launched", True) for d in diagnostics))
        except InterruptedError:
            raise
        except (OSError, subprocess.SubprocessError) as exc:
            return outcome("ERROR", str(exc), attempts_count=len(diagnostics))
        except (ValueError, TypeError) as exc:
            return outcome("UNRESOLVED", str(exc), attempts_count=len(diagnostics))

    def prove_conjecture(
        self,
        conjecture: Any,
        output_dir: Optional[Union[str, Path]] = None,
        total_timeout_sec: Optional[float] = None,
    ) -> LeanVerificationResult:
        """Prove a Conjecture AST or ProofResult object."""
        return self.prove_challenge(target=conjecture, output_dir=output_dir, conjecture=conjecture, total_timeout_sec=total_timeout_sec)

    def prove_all(
        self,
        targets: Sequence[Any],
        output_dir: Optional[Union[str, Path]] = None,
    ) -> List[LeanVerificationResult]:
        """Batch verify a collection of conjectures or challenge targets."""
        results = []
        for target in targets:
            res = self.prove_challenge(target=target, output_dir=output_dir)
            results.append(res)
        return results
