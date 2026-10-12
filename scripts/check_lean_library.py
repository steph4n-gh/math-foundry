#!/usr/bin/env python3
"""Build and audit an independent Git-based Lake consumer without AI.

The library must be committed. Archived proofs and adapted importable modules
remain separate artifacts; this check establishes packaging and kernel reuse,
not mathematical originality or release qualification.
"""
from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager
import hashlib
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from autonomous_math.export.research_packet import _read
from autonomous_math.prover.codex_synthesis import terminate_process_group
from autonomous_math.prover.lean_prover import LeanToolchain, _target_axiom_report
from autonomous_math.research_state import ALLOWED_AXIOMS
from scripts.replay_results import LEAN_PIN, MATHLIB_PIN, load_catalog

FOUNDATION_IDS = {
    "archetype_chi_ge_omega", "archetype_brooks_standard", "archetype_spectral_wilf",
    "mcclelland_graph_energy_upper", "cvetkovic_signless_laplacian_max_deg",
    "chung_normalized_laplacian_gap_upper", "parity_code_unique_neighbor_distance",
    "parity_code_dimension_le_order",
}
CONSUMER_TARGETS = (
    "FoundryConsumer.clique_bound",
    "FoundryConsumer.coloring_obstruction",
    "FoundryConsumer.chromatic_number_from_matching_bounds",
    "FoundryConsumer.adjacency_code_dimension_budget",
    "FoundryConsumer.no_three_coloring",
    "FoundryConsumer.four_colors_from_matching_bounds",
    "FoundryConsumer.sixteen_vertex_dimension_budget",
)
CLEANUP_TIMEOUT = 120


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load_library(root):
    records, catalog_hash = load_catalog(root / "results/catalog.json", root)
    raw = _read("certified_lean/MathFoundry/manifest.json", root=root, suffix=".json")
    manifest = json.loads(raw)
    rows, exports = manifest.get("records"), manifest.get("foundation_exports")
    if (manifest.get("schema_version") != 1 or manifest.get("catalog_path") != "results/catalog.json"
            or manifest.get("catalog_sha256") != catalog_hash or not isinstance(rows, list)
            or manifest.get("artifact_count") != len(records) or len(rows) != len(records)):
        raise ValueError("Library manifest does not bind the complete published catalog")
    originals = {r["id"]: r for r in records}
    seen = set()
    for row in rows:
        original = originals.get(row.get("id"))
        if original is None or row["id"] in seen:
            raise ValueError("Missing, duplicate or unknown library proof identity")
        seen.add(row["id"])
        for key in ("theorem_name", "source_path", "source_sha256", "challenge_sha256"):
            if row.get(key) != original[key]:
                raise ValueError("Library/archive binding changed: " + key)
        name = row["theorem_name"]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            raise ValueError("Unsupported theorem identifier")
        module = "MathFoundry.Archive." + name
        if (row.get("module") != module or row.get("qualified_theorem") != module + "." + name
                or row.get("module_path") != "certified_lean/" + module.replace(".", "/") + ".lean"):
            raise ValueError("Library target or module path changed")
        code = _read(row["module_path"], root=root, suffix=".lean")
        if digest(code) != row.get("module_sha256"):
            raise ValueError("Changed namespaced library module")
    if (not isinstance(exports, list) or len(exports) != len(FOUNDATION_IDS)
            or {r.get("id") for r in exports} != FOUNDATION_IDS):
        raise ValueError("Expected all eight documented Foundation exports")
    modules = {row["id"]: row for row in rows}
    for export in exports:
        row = modules[export["id"]]
        if (export.get("qualified_theorem") != "MathFoundry." + row["theorem_name"]
                or export.get("archive_theorem") != row["qualified_theorem"]):
            raise ValueError("Foundation alias does not bind its archived target")
    return manifest, digest(raw), catalog_hash


def consumer_manifest(pinned, repository, revision):
    """Seed the fresh consumer with locked revisions; never run lake update."""
    manifest = copy.deepcopy(pinned)
    manifest["name"] = "foundryConsumer"
    for package in manifest["packages"]:
        package["inherited"] = True
    manifest["packages"].insert(0, {
        "url": repository, "type": "git", "subDir": "certified_lean", "scope": "",
        "rev": revision, "name": "certifiedResearch", "manifestFile": "lake-manifest.json",
        "inputRev": revision, "inherited": False, "configFile": "lakefile.lean",
    })
    return manifest


def check_dependency_manifest(actual, pinned, repository, revision):
    packages = actual.get("packages", [])
    by_name = {p.get("name"): p for p in packages}
    if len(by_name) != len(packages) or len(packages) != len(pinned["packages"]) + 1:
        raise ValueError("Changed or duplicate consumer dependencies")
    library = by_name.get("certifiedResearch", {})
    if (library.get("type") != "git" or library.get("url") != repository
            or library.get("rev") != revision or library.get("subDir") != "certified_lean"):
        raise ValueError("Consumer is not using the exact Git package revision")
    for expected in pinned["packages"]:
        current = by_name.get(expected["name"], {})
        for key in ("type", "url", "rev", "subDir", "configFile"):
            if current.get(key) != expected.get(key):
                raise ValueError("Consumer dependency differs from pinned manifest: " + expected["name"])
    return by_name


def audit_axioms(stdout, queries, checks):
    """Require an ordered, complete stream of exact native target reports.

    Each block is then checked with the existing unique-final-report parser.
    Unexpected text, duplicate/omitted targets and forged earlier reports fail.
    """
    remaining = stdout
    for query in queries:
        target = query["canonical_name"]
        remaining = remaining.lstrip()
        prefix = "'" + target + "' "
        pattern = re.escape(prefix) + r"(?:depends on axioms:\s*\[[^]]*\]|does not depend on any axioms)[ \t]*(?:\n|$)"
        match = re.match(pattern, remaining)
        if match is None:
            raise ValueError("Missing or unexpected native axiom report: " + target)
        block = match.group(0)
        axioms, error = _target_axiom_report(block, target)
        passed = error is None and set(axioms) <= ALLOWED_AXIOMS
        checks.append({"queried_name": query["name"], "theorem": target,
                       "alias_resolved": query["name"] != target, "axioms": axioms, "raw_report": block,
                       "axiom_audit_error": error, "passed": passed})
        if not passed:
            raise ValueError("Disallowed transitive axioms: " + target)
        remaining = remaining[match.end():]
    if remaining.strip():
        raise ValueError("Unexpected output after the final native axiom report")


def group_snapshot(group):
    result = subprocess.run(["ps", "-eo", "pid=,pgid=,stat=,rss=,comm="],
        capture_output=True, text=True, timeout=2, check=True)
    members = []
    for line in result.stdout.splitlines():
        parts = line.split(None, 4)
        if (len(parts) == 5 and parts[1] == str(group)
                and not parts[2].startswith("Z") and "E" not in parts[2]):
            members.append({"pid": int(parts[0]), "rss_kib": int(parts[3]),
                            "is_lean": Path(parts[4]).name == "lean"})
    return members


@contextmanager
def deferred_interrupts():
    """Defer Python handlers until ownership or bounded cleanup is recorded.

    This does not block signals in a child process's inherited signal mask.
    """
    pending, previous = [], {}
    try:
        for signum in (signal.SIGINT, signal.SIGTERM):
            previous[signum] = signal.getsignal(signum)
            signal.signal(signum, lambda number, frame: pending.append(number))
        yield pending
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def run_command(report, command, cwd, cap, deadline, env):
    budget = min(cap, deadline - time.monotonic())
    if budget <= 0:
        raise TimeoutError("Library consumer enclosing deadline expired")
    row = {"command": [str(s) for s in command], "cwd": str(cwd), "timeout_sec": budget,
           "state": "running", "peak_group_rss_kib": 0, "peak_live_lean_processes": 0}
    report["commands"].append(row)
    started = time.monotonic()
    process, primary_error = None, None
    try:
        # A signal after Popen returns must not interrupt before its PID is
        # registered. The surrounding finally already owns cleanup at this point.
        with deferred_interrupts() as pending:
            process = subprocess.Popen(command, cwd=cwd, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
            row["owned_process_group"] = process.pid
        if pending:
            raise InterruptedError("Library consumer interrupted by " + signal.Signals(pending[0]).name)
        while True:
            remaining = budget - (time.monotonic() - started)
            if remaining <= 0:
                raise TimeoutError("Library consumer command reached its finite cap")
            try:
                stdout, stderr = process.communicate(timeout=min(0.5, remaining))
                break
            except subprocess.TimeoutExpired:
                members = group_snapshot(process.pid)
                row["peak_group_rss_kib"] = max(row["peak_group_rss_kib"], sum(m["rss_kib"] for m in members))
                row["peak_live_lean_processes"] = max(row["peak_live_lean_processes"], sum(m["is_lean"] for m in members))
        row.update(stdout=stdout, stderr=stderr, exit_code=process.returncode,
                   state="passed" if process.returncode == 0 else "failed")
        if process.returncode != 0:
            raise ValueError("Library consumer command failed: " + " ".join(map(str, command)))
        return row
    except BaseException as exc:
        primary_error = exc
        row["primary_error"] = type(exc).__name__ + ": " + str(exc)
        row["state"] = ("interrupted" if isinstance(exc, (KeyboardInterrupt, InterruptedError))
                        else "timeout" if isinstance(exc, TimeoutError) else "failed")
        raise
    finally:
        try:
            with deferred_interrupts() as pending:
                terminate_process_group(process)
                if process is not None:
                    if "stdout" not in row:
                        row["stdout"], row["stderr"] = process.communicate(timeout=2)
                    members = group_snapshot(process.pid)
                    row.update(exit_code=process.returncode, direct_child_reaped=process.poll() is not None,
                               remaining_owned_process_groups=[process.pid] if members else [])
                    if members:
                        raise RuntimeError("Owned library-consumer descendants remain after cleanup")
            if pending:
                row["cleanup_interrupts"] = [signal.Signals(number).name for number in pending]
                if primary_error is None:
                    row["state"] = "interrupted"
                    raise InterruptedError("Library consumer interrupted during owned cleanup")
        except InterruptedError:
            raise
        except BaseException as exc:
            row.update(cleanup_error=str(exc), state="failed")
            if primary_error is None:
                raise
        finally:
            row["elapsed_sec"] = time.monotonic() - started


def check_committed_files(root, revision, paths, run):
    output = run(["git", "ls-tree", "-r", revision, "--", *paths], root, 30)["stdout"]
    blobs = {line.split("\t", 1)[1]: line.split("\t", 1)[0].split()[2]
             for line in output.splitlines() if "\t" in line}
    for path in paths:
        raw = _read(path, root=root)
        git_hash = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if blobs.get(path) != git_hash:
            raise ValueError("Library must be committed at the selected Git revision: " + path)


@contextmanager
def consumer_workspace(report, env):
    # Resolve the host's /var -> /private/var prefix on macOS. Evidence below
    # this prefix must still pass the strict no-symlink reader.
    consumer = Path(tempfile.mkdtemp(prefix="math-foundry-consumer-")).resolve(strict=True)
    cleanup = {"path": str(consumer), "timeout_sec": CLEANUP_TIMEOUT, "status": "pending",
        "deadline_scope": "Separately bounded cleanup after the validation enclosing deadline."}
    report["temporary_consumer_cleanup"] = cleanup
    try:
        yield consumer
    finally:
        primary_error = sys.exc_info()[1]
        try:
            run_command(report, [sys.executable, "-c", "import shutil,sys; shutil.rmtree(sys.argv[1])", str(consumer)],
                ROOT, CLEANUP_TIMEOUT, time.monotonic() + CLEANUP_TIMEOUT, env)
            if consumer.exists():
                raise RuntimeError("Temporary consumer directory remains after deletion")
            cleanup["status"] = "complete"
        except BaseException as exc:
            cleanup.update(status="failed", error=type(exc).__name__ + ": " + str(exc),
                           retained_path=str(consumer) if consumer.exists() else None)
            # Keep the primary validation failure visible if cleanup also fails.
            if primary_error is None:
                raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git-repository", default=str(ROOT), help="Git URL or checkout path; cloned as a Git dependency")
    parser.add_argument("--revision", help="Exact 40-character commit SHA; defaults to this checkout's HEAD")
    parser.add_argument("--setup-timeout", type=float, default=600)
    parser.add_argument("--build-timeout", type=float, default=1800, help="One enclosing budget for all serial module builds")
    parser.add_argument("--audit-timeout", type=float, default=120)
    parser.add_argument("--timeout", type=float, default=2700, help="Finite enclosing deadline, at most 3000 seconds")
    parser.add_argument("--foundations-only", action="store_true", help="Narrow eight-module Git-import pilot, not full-library acceptance")
    parser.add_argument("--output", type=Path, default=ROOT / "runs/lean-library-consumer.json", help="Fresh report; never overwrite")
    args = parser.parse_args(argv)
    for key, maximum in (("setup_timeout", 900), ("build_timeout", 2400), ("audit_timeout", 120), ("timeout", 3000)):
        value = getattr(args, key)
        if not math.isfinite(value) or not 0 < value <= maximum:
            parser.error(key.replace("_", "-") + " must be finite, positive and at most " + str(maximum))
    if args.revision is not None and not re.fullmatch(r"[0-9a-f]{40}", args.revision):
        parser.error("--revision must be an exact lowercase 40-character Git commit SHA")
    if args.output.exists() or args.output.is_symlink():
        parser.error("--output already exists; choose a fresh report")
    report = {"schema_version": 1, "status": "failed", "model_requests": 0,
        "mode": "foundations_only" if args.foundations_only else "complete_library",
        "consumer_targets": list(CONSUMER_TARGETS),
        "started_at": time.time(), "commands": [], "axiom_checks": [],
        "budgets_sec": {key: getattr(args, key) for key in ("setup_timeout", "build_timeout", "audit_timeout", "timeout")},
        "scope": "Independent Git/Lake import, adapted library builds and transitive permitted-axiom checks; no originality or qualification."}
    report["budgets_sec"]["cleanup_timeout"] = CLEANUP_TIMEOUT
    deadline = time.monotonic() + args.timeout
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_OVERRIDE_LEAN"):
        env.pop(key, None)
    env["LEAN_NUM_THREADS"] = "2"
    report["runtime"] = {"LEAN_NUM_THREADS": "2", "external_LEAN_PATH_removed": True,
        "resource_observation": "Sampled owned-group RSS can double-count shared pages; Lean thread setting is not a measured hard process-admission cap."}
    run = lambda command, cwd, cap: run_command(report, command, cwd, cap, deadline, env)
    old_handler = signal.getsignal(signal.SIGTERM)
    def interrupted(signum, frame):
        raise InterruptedError("Library consumer interrupted by " + signal.Signals(signum).name)
    signal.signal(signal.SIGTERM, interrupted)
    exit_code = 1
    try:
        revision = args.revision or run(["git", "rev-parse", "HEAD"], ROOT, 5)["stdout"].strip()
        if not re.fullmatch(r"[0-9a-f]{40}", revision):
            raise ValueError("Expected an exact SHA-1 Git commit")
        report.update(revision=revision, git_repository=args.git_repository)
        # Fail before any native Lean request when the proposed package is not committed.
        manifest_path = "certified_lean/MathFoundry/manifest.json"
        run(["git", "cat-file", "-e", revision + ":" + manifest_path], ROOT, 5)
        run([sys.executable, str(ROOT / "scripts/package_lean_library.py"), "--check"], ROOT, 30)
        manifest, manifest_hash, catalog_hash = load_library(ROOT)
        pinned = json.loads(_read("certified_lean/lake-manifest.json", root=ROOT, suffix=".json"))
        if (len(pinned["packages"]) != 9 or _read("certified_lean/lean-toolchain", root=ROOT).decode().strip() != LEAN_PIN
                or not any(p["name"] == "mathlib" and p["rev"] == MATHLIB_PIN for p in pinned["packages"])):
            raise ValueError("Expected the existing exact Lean and nine Mathlib dependency pins")
        consumer_source = _read("examples/ImportFoundry.lean", root=ROOT, suffix=".lean")
        paths = [manifest_path, "results/catalog.json", "examples/ImportFoundry.lean",
            "certified_lean/MathFoundry.lean", "certified_lean/MathFoundry/Foundations.lean",
            *["certified_lean/" + name for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")],
            *[r["module_path"] for r in manifest["records"]],
            *[r["source_path"] for r in manifest["records"]]]
        check_committed_files(ROOT, revision, paths, run)
        report.update(catalog_sha256=catalog_hash, library_manifest_sha256=manifest_hash,
            artifact_count=len(manifest["records"]), foundation_export_count=len(manifest["foundation_exports"]),
            consumer_original_source_sha256=digest(consumer_source), checker_source_sha256=digest(Path(__file__).read_bytes()))
        if args.foundations_only:
            if consumer_source.count(b"import MathFoundry\n") != 1:
                raise ValueError("Narrow pilot requires exactly one full-library import to replace")
            consumer_source = consumer_source.replace(b"import MathFoundry\n", b"import MathFoundry.Foundations\n", 1)
            report["consumer_adaptation"] = "Only import MathFoundry becomes import MathFoundry.Foundations; this is a narrow pilot."
        report["consumer_source_sha256"] = digest(consumer_source)
        lake = LeanToolchain._find_binary("lake")
        if lake is None:
            raise ValueError("Pinned Lake is unavailable; follow the Lean setup instructions")
        with consumer_workspace(report, env) as consumer:
            (consumer / "lean-toolchain").write_text(LEAN_PIN + "\n")
            (consumer / "lakefile.lean").write_text(
                "import Lake\nopen Lake DSL\npackage foundryConsumer\n"
                "require certifiedResearch from git " + json.dumps(args.git_repository) + " @ " + json.dumps(revision) + " / \"certified_lean\"\n"
                "@[default_target]\nlean_lib Consumer\n")
            seeded = consumer_manifest(pinned, args.git_repository, revision)
            (consumer / "lake-manifest.json").write_text(json.dumps(seeded, indent=2) + "\n")
            (consumer / "Consumer.lean").write_bytes(consumer_source)
            report["consumer_lakefile"] = (consumer / "lakefile.lean").read_text()
            report["seeded_consumer_manifest"] = seeded
            run([str(lake), "exe", "cache", "get"], consumer, args.setup_timeout)
            resolved = json.loads((consumer / "lake-manifest.json").read_text())
            dependencies = check_dependency_manifest(resolved, pinned, args.git_repository, revision)
            actual_heads = {}
            for name, package in dependencies.items():
                checkout = consumer / ".lake/packages" / name
                actual = run(["git", "-C", str(checkout), "rev-parse", "HEAD"], consumer, 5)["stdout"].strip()
                if actual != package["rev"]:
                    raise ValueError("Actual consumer dependency checkout changed: " + name)
                actual_heads[name] = actual
            cloned = consumer / ".lake/packages/certifiedResearch"
            clone_manifest, clone_hash, _ = load_library(cloned)
            if clone_hash != manifest_hash or clone_manifest != manifest:
                raise ValueError("Git dependency library differs from the exact checked source")
            version = run([str(lake), "env", "lean", "--version"], consumer, 10)["stdout"].strip()
            if not version.startswith("Lean (version 4.34.1,"):
                raise ValueError("Actual consumer Lean compiler differs from the pin")
            elan = LeanToolchain._find_binary("elan")
            if elan is None:
                raise ValueError("Pinned compiler identity requires elan")
            binary = Path(run([str(elan), "which", "lean"], consumer, 5)["stdout"].strip()).resolve(strict=True)
            compiler_hash = digest(binary.read_bytes())
            report.update(resolved_consumer_manifest=resolved, dependency_revisions=actual_heads,
                compiler={"version": version, "binary": str(binary), "binary_sha256": compiler_hash})
            build_deadline = min(deadline, time.monotonic() + args.build_timeout)
            def build(target):
                return run([str(lake), "build", target], consumer, min(120, build_deadline - time.monotonic()))
            foundation_rows = [r for r in manifest["records"] if r["id"] in FOUNDATION_IDS]
            # Explicit standalone module targets keep first-party builds serial;
            # a full parallel Lake request has no hard compiler-process limit.
            for row in foundation_rows:
                build("certifiedResearch/+" + row["module"] + ":olean")
            build("certifiedResearch/+MathFoundry.Foundations:olean")
            report["foundation_preflight"] = {"built_archive_modules": len(foundation_rows),
                "native_builds_serial": True, "completed_at": time.time()}
            if not args.foundations_only:
                for row in manifest["records"]:
                    if row["id"] not in FOUNDATION_IDS:
                        build("certifiedResearch/+" + row["module"] + ":olean")
                build("certifiedResearch/MathFoundry")
            build("Consumer")
            report["built_archive_module_count"] = len(foundation_rows) if args.foundations_only else len(manifest["records"])
            queries = [] if args.foundations_only else [
                {"name": r["qualified_theorem"], "canonical_name": r["qualified_theorem"]}
                for r in manifest["records"]]
            # Lean export creates aliases rather than new constants. Native
            # #print reports their canonical archive names, bound by the manifest.
            queries += [{"name": r["qualified_theorem"], "canonical_name": r["archive_theorem"]}
                        for r in manifest["foundation_exports"]]
            queries += [{"name": target, "canonical_name": target} for target in CONSUMER_TARGETS]
            audit = "import Consumer\n" + "".join("#print axioms " + query["name"] + "\n" for query in queries)
            (consumer / "Audit.lean").write_text(audit)
            report["audit_source_sha256"] = digest(audit.encode())
            command = run([str(lake), "env", "lean", "Audit.lean"], consumer, args.audit_timeout)
            if "error:" in command["stdout"] + command["stderr"] or "declaration uses" in command["stdout"] + command["stderr"]:
                raise ValueError("Consumer compiler reported an error or untrusted declaration")
            audit_axioms(command["stdout"], queries, report["axiom_checks"])
            if digest(binary.read_bytes()) != compiler_hash:
                raise ValueError("Compiler bytes changed during consumer verification")
            final_manifest, final_hash, _ = load_library(cloned)
            if final_hash != manifest_hash or final_manifest != manifest:
                raise ValueError("Library source changed during consumer verification")
            check_dependency_manifest(json.loads((consumer / "lake-manifest.json").read_text()), pinned, args.git_repository, revision)
            for name, expected in actual_heads.items():
                actual = run(["git", "-C", str(consumer / ".lake/packages" / name), "rev-parse", "HEAD"], consumer, 5)["stdout"].strip()
                if actual != expected:
                    raise ValueError("Dependency changed during consumer verification: " + name)
            report.update(status="passed", native_axiom_queries_checked=len(queries),
                distinct_native_constants_checked=len({query["canonical_name"] for query in queries}),
                git_dependency_revision_checked=True, separate_consumer_import_checked=True)
        exit_code = 0
    except (KeyboardInterrupt, InterruptedError) as exc:
        report.update(status="interrupted", error=str(exc) or "KeyboardInterrupt")
        exit_code = 130
    except Exception as exc:
        message = str(exc)
        if any(row.get("command", [])[:3] == ["git", "cat-file", "-e"] and row.get("state") == "failed" for row in report["commands"]):
            message = "Library package is absent at the selected Git revision; commit the generated package before a Git-consumer check. " + message
        report.update(status="failed", error=message)
    finally:
        signal.signal(signal.SIGTERM, old_handler)
        groups = [group for row in report["commands"] for group in row.get("remaining_owned_process_groups", [])]
        cleanup_errors = [row["cleanup_error"] for row in report["commands"] if row.get("cleanup_error")]
        if report.get("temporary_consumer_cleanup", {}).get("status") == "failed":
            cleanup_errors.append(report["temporary_consumer_cleanup"]["error"])
        report.update(remaining_owned_process_groups=groups, cleanup="failed" if groups or cleanup_errors else "complete", finished_at=time.time())
        if groups or cleanup_errors:
            report.update(status="failed", cleanup_errors=cleanup_errors)
            exit_code = 1
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as stream:
            json.dump(report, stream, indent=2)
            stream.write("\n")
    print(json.dumps({"status": report["status"], "report": str(args.output),
        "axiom_targets_checked": len(report["axiom_checks"]), "model_requests": 0}))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
