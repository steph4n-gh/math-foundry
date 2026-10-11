#!/usr/bin/env python3
"""Check portable result bindings, or replay exact proofs serially without AI.

Historical producer receipts are archival evidence. This command records fresh
local compiler/dependency identity and never writes a research atlas or receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from autonomous_math.core.ast import Conjecture
from autonomous_math.core import ast
from autonomous_math.export.research_packet import _read
from autonomous_math.prover import lean_prover, trusted_lean
from autonomous_math.prover.lean_prover import LeanToolchain, _target_axiom_report
from autonomous_math import research_state
from autonomous_math.research_state import ALLOWED_AXIOMS, sha256, workspace_fingerprint

LEAN_PIN = "leanprover/lean4:v4.34.1"
MATHLIB_PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
SEMANTIC_FIELDS = {"id", "lhs_expr", "rel", "rhs_expr", "guard_predicate"}


def _target_prefix(code, name):
    matches = list(re.finditer(r"\btheorem\s+" + re.escape(name) + r"(?=\s|[({:])", code))
    if len(matches) != 1:
        raise ValueError("Expected exactly one target theorem declaration")
    delimiter = code.find(":= by", matches[0].end())
    if delimiter < 0:
        raise ValueError("Missing target theorem proof delimiter")
    return code[:delimiter], code[matches[0].start():delimiter]


def check_record(record, root):
    """Bind exact retained bytes and the complete semantic AST, including guards."""
    identifier, name = record["id"], record["theorem_name"]
    semantic = record["conjecture"]
    if (not isinstance(identifier, str) or not identifier or not isinstance(name, str)
            or not isinstance(semantic, dict) or set(semantic) != SEMANTIC_FIELDS
            or semantic["id"] != identifier):
        raise ValueError("Malformed or mismatched semantic conjecture")
    # Native from_dict expects descriptive prose; it is not a semantic premise.
    conjecture = Conjecture.from_dict(dict(semantic, statement=""))
    expected, native_name = trusted_lean.render_challenge(conjecture)
    if name != native_name:
        raise ValueError("Target theorem name differs from the native AST renderer")
    contents = {}
    for kind in ("source", "challenge"):
        path, digest = record[kind + "_path"], record[kind + "_sha256"]
        if (not isinstance(path, str) or Path(path).is_absolute()
                or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)):
            raise ValueError("Expected a relative artifact path and SHA-256")
        raw = _read(path, root=root, suffix=".lean")
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("Changed " + kind + " artifact")
        contents[kind] = raw.decode("utf-8")
    source_prefix, source_target = _target_prefix(contents["source"], name)
    challenge_prefix, challenge_target = _target_prefix(contents["challenge"], name)
    _, expected_target = _target_prefix(expected, name)
    if source_prefix != challenge_prefix:
        raise ValueError("Proof and challenge have different statements or context")
    if challenge_target != expected_target or source_target != expected_target:
        raise ValueError("Target statement or complete premise differs from its AST")
    return contents["source"]


def load_catalog(path, root):
    raw = _read(path, root=root, suffix=".json")
    catalog = json.loads(raw)
    records = catalog.get("records")
    if catalog.get("schema_version") != 1 or not isinstance(records, list) or not records:
        raise ValueError("Expected a nonempty schema-version-1 result catalog")
    identities, names = set(), set()
    for record in records:
        if not isinstance(record, dict):
            raise ValueError("Malformed catalog record")
        if record.get("id") in identities or record.get("theorem_name") in names:
            raise ValueError("Duplicate catalog identity or target theorem name")
        check_record(record, root)
        identities.add(record["id"]); names.add(record["theorem_name"])
    return records, hashlib.sha256(raw).hexdigest()


def select_records(records, shard_index=0, shard_count=1, limit=None):
    if shard_count < 1 or not 0 <= shard_index < shard_count or (limit is not None and limit < 1):
        raise ValueError("Invalid shard or positive limit")
    selected = [record for index, record in enumerate(records) if index % shard_count == shard_index]
    if limit is not None:
        selected = selected[:limit]
    if not selected:
        raise ValueError("No records selected; refusing a vacuous replay")
    return selected


def _workspace_configuration(workspace):
    toolchain = _read(workspace / "lean-toolchain").decode().strip()
    manifest = json.loads(_read(workspace / "lake-manifest.json", suffix=".json"))
    if toolchain != LEAN_PIN or not any(
            p.get("name") == "mathlib" and p.get("rev") == MATHLIB_PIN
            and p.get("url") == "https://github.com/leanprover-community/mathlib4.git"
            for p in manifest.get("packages", [])):
        raise ValueError("Workspace does not select the published Lean/Mathlib pins")
    return {"lean_toolchain": toolchain, "mathlib_revision": MATHLIB_PIN,
            "configuration_hashes": {name: sha256(workspace / name) for name in
                ("lean-toolchain", "lakefile.lean", "lake-manifest.json")}}


def _compiler_identity(toolchain):
    version = toolchain.get_version()
    if not version.startswith("Lean (version 4.34.1,"):
        raise ValueError("Actual Lean compiler does not match the published version")
    actual = subprocess.run([str(Path.home() / ".elan/bin/elan"), "which", "lean"],
        cwd=toolchain.workspace_dir, capture_output=True, text=True, timeout=5, check=True)
    binary = Path(actual.stdout.strip()).resolve(strict=True)
    return {"version": version, "binary_sha256": sha256(binary), "binary": str(binary)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", type=Path, default=ROOT / "results/catalog.json")
    parser.add_argument("--check-only", action="store_true", help="Validate all bindings; invoke no Lean or AI")
    parser.add_argument("--workspace", type=Path, default=ROOT / "certified_lean")
    parser.add_argument("--timeout", type=float, default=60, help="Finite per-proof compiler cap, at most 120 seconds")
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--output", type=Path, default=ROOT / "runs/public-replay.json", help="Fresh report path; never overwrite")
    args = parser.parse_args(argv)
    if not args.catalog.is_absolute():
        args.catalog = ROOT / args.catalog
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 120:
        parser.error("--timeout must be finite, positive and at most 120 seconds")
    if args.shard_count < 1 or not 0 <= args.shard_index < args.shard_count or (args.limit is not None and args.limit < 1):
        parser.error("Invalid shard index/count or positive limit")
    if args.output.exists() or args.output.is_symlink():
        parser.error("--output already exists; choose a fresh report path")
    report = {"schema_version": 1, "status": "failed", "mode": "binding_check" if args.check_only else "kernel_replay",
        "model_requests": 0, "kernel_replay_performed": False, "started_at": time.time(),
        "timeout_sec": args.timeout, "shard_index": args.shard_index, "shard_count": args.shard_count,
        "limit": args.limit, "binding_checked_count": 0, "selected_count": 0, "records": [],
        "scope": "Exact result bytes/AST bindings and optional fresh local kernel replay; no originality or release qualification."}
    toolchain = None
    old_handler = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame):
        raise InterruptedError("Public replay interrupted by " + signal.Signals(signum).name)
    signal.signal(signal.SIGTERM, interrupted)
    exit_code = 1
    try:
        records, catalog_hash = load_catalog(args.catalog, ROOT)
        selected = select_records(records, args.shard_index, args.shard_count, args.limit)
        report.update(catalog_sha256=catalog_hash, binding_checked_count=len(records), selected_count=len(selected),
            validator_source_hashes={"script": sha256(Path(__file__)), "trusted_lean": sha256(Path(trusted_lean.__file__)),
                "lean_prover": sha256(Path(lean_prover.__file__)), "ast": sha256(Path(ast.__file__)),
                "research_state": sha256(Path(research_state.__file__))})
        workspace = args.workspace.resolve()
        report["workspace"] = _workspace_configuration(workspace)
        if not args.check_only:
            toolchain = LeanToolchain(workspace_dir=workspace)
            if not toolchain.ensure_workspace_built():
                raise ValueError("Pinned genuine Mathlib is not built; follow docs/verification.md setup")
            report["compiler"] = _compiler_identity(toolchain)
            report["workspace"]["dependency_sha256"] = workspace_fingerprint(workspace)
        for record in selected:
            source = check_record(record, ROOT)
            row = {"id": record["id"], "theorem_name": record["theorem_name"],
                "source_sha256": record["source_sha256"], "challenge_sha256": record["challenge_sha256"],
                "binding_passed": True, "kernel_passed": None, "state": "binding_passed"}
            report["records"].append(row)
            if args.check_only:
                continue
            started = time.monotonic()
            try:
                code, stdout, stderr = toolchain.run_lean_code(
                    source + "\n#print axioms " + record["theorem_name"] + "\n", timeout=args.timeout)
            except (InterruptedError, KeyboardInterrupt) as exc:
                row.update(state="interrupted", kernel_passed=False, error=str(exc) or "KeyboardInterrupt")
                raise
            except Exception as exc:
                row.update(state="failed", kernel_passed=False, error=str(exc))
                raise
            finally:
                row.update(elapsed_sec=time.monotonic() - started, timeout_sec=args.timeout,
                    compiler_transport=dict(toolchain.last_run_metadata))
                report["kernel_replay_performed"] |= bool(toolchain.last_run_metadata.get("compiler_launched"))
            axioms, error = _target_axiom_report(stdout, record["theorem_name"])
            passed = (code == 0 and error is None and set(axioms) <= ALLOWED_AXIOMS
                and "error:" not in stdout + stderr and "declaration uses" not in stdout + stderr)
            row.update(exit_code=code, stdout=stdout, stderr=stderr, axioms=axioms, axiom_audit_error=error,
                elapsed_sec=time.monotonic() - started, timeout_sec=args.timeout,
                compiler_transport=dict(toolchain.last_run_metadata), kernel_passed=passed,
                state="passed" if passed else "timeout" if code == 124 else "failed")
            try:
                if check_record(record, ROOT) != source:
                    raise ValueError("Proof bytes changed during kernel replay")
            except (OSError, ValueError, KeyError, TypeError) as exc:
                row.update(binding_passed=False, kernel_passed=False, state="failed", binding_error=str(exc))
        if sha256(args.catalog) != catalog_hash:
            raise ValueError("Catalog changed during replay")
        for record in records:
            check_record(record, ROOT)
        if toolchain and workspace_fingerprint(workspace) != report["workspace"]["dependency_sha256"]:
            raise ValueError("Proof dependencies changed during replay")
        if toolchain and _compiler_identity(toolchain) != report["compiler"]:
            raise ValueError("Actual Lean compiler changed during replay")
        if all(row["binding_passed"] and (args.check_only or row["kernel_passed"]) for row in report["records"]):
            report["status"] = "passed"; exit_code = 0
    except (InterruptedError, KeyboardInterrupt) as exc:
        report.update(status="interrupted", error=str(exc) or "KeyboardInterrupt"); exit_code = 130
    except Exception as exc:
        report.update(status="failed", error=str(exc)); exit_code = 1
    finally:
        try:
            if toolchain:
                toolchain.cancel()
                groups = toolchain.active_process_groups()
                report["remaining_owned_process_groups"] = groups
                if groups:
                    raise RuntimeError("Owned compiler processes remain after cleanup")
            report["cleanup"] = "complete"
        except Exception as exc:
            report.update(status="failed", cleanup="failed", cleanup_error=str(exc)); exit_code = 1
        signal.signal(signal.SIGTERM, old_handler)
        report["finished_at"] = time.time()
        report["kernel_passed_count"] = sum(row.get("kernel_passed") is True for row in report["records"])
        report["failed_count"] = sum(row.get("state") in {"failed", "timeout"} for row in report["records"])
        report["timeout_count"] = sum(row.get("state") == "timeout" for row in report["records"])
        report["interrupted_count"] = sum(row.get("state") == "interrupted" for row in report["records"])
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as stream:
            json.dump(report, stream, indent=2, allow_nan=False); stream.write("\n")
    result = ("check-only; Lean invocations 0" if args.check_only else
        f"{report['kernel_passed_count']}/{report['selected_count']} fresh kernel replays passed")
    print(f"{report['status']}: {report['binding_checked_count']} bindings checked; "
          f"{result}; AI requests 0. Report: {args.output}")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
