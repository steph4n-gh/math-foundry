"""Git-consumer protocol failures must not become kernel acceptance."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import signal
import os
import subprocess
import sys
import time

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("library_consumer", ROOT / "scripts/check_lean_library.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
from scripts.replay_results import Conjecture, trusted_lean


@pytest.fixture
def library(tmp_path, monkeypatch):
    root = tmp_path / "checkout"
    root.mkdir()
    monkeypatch.setattr(checker, "ROOT", root)
    records, modules = [], []
    for name in sorted(checker.FOUNDATION_IDS):
        semantic = {"id": name, "lhs_expr": {"node_type": "invariant", "name": "order"},
                    "rel": ">=", "rhs_expr": {"node_type": "constant", "value": 0}, "guard_predicate": None}
        challenge, theorem = trusted_lean.render_challenge(Conjecture.from_dict(dict(semantic, statement="")))
        record = {"id": name, "theorem_name": theorem, "conjecture": semantic}
        for kind, code in [("source", challenge.replace("  sorry", "  positivity")), ("challenge", challenge)]:
            path = root / "results" / (kind + "-" + name + ".lean")
            path.parent.mkdir(exist_ok=True)
            path.write_text(code)
            record[kind + "_path"] = str(path.relative_to(root))
            record[kind + "_sha256"] = checker.digest(path.read_bytes())
        records.append(record)
        module = "MathFoundry.Archive." + theorem
        path = root / "certified_lean" / (module.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("-- isolated mocked native module\n")
        modules.append({**{k: record[k] for k in ("id", "theorem_name", "source_path", "source_sha256", "challenge_sha256")},
            "module": module, "qualified_theorem": module + "." + theorem,
            "module_path": str(path.relative_to(root)), "module_sha256": checker.digest(path.read_bytes())})
    catalog = root / "results/catalog.json"
    catalog.write_text(json.dumps({"schema_version": 1, "records": records}))
    manifest = {"schema_version": 1, "catalog_path": "results/catalog.json",
        "catalog_sha256": checker.digest(catalog.read_bytes()), "artifact_count": len(records), "records": modules,
        "foundation_exports": [{"id": r["id"], "qualified_theorem": "MathFoundry." + r["theorem_name"],
            "archive_theorem": r["qualified_theorem"]} for r in modules]}
    path = root / "certified_lean/MathFoundry/manifest.json"
    path.write_text(json.dumps(manifest))
    for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
        (root / "certified_lean" / name).write_bytes((ROOT / "certified_lean" / name).read_bytes())
    (root / "certified_lean/MathFoundry.lean").write_text("import MathFoundry.Foundations\n")
    (root / "certified_lean/MathFoundry/Foundations.lean").write_text("-- mock exports\n")
    (root / "examples").mkdir()
    (root / "examples/ImportFoundry.lean").write_text("import MathFoundry\nnamespace FoundryConsumer\nend FoundryConsumer\n")
    return root, manifest, path


@pytest.mark.parametrize("change", ["missing", "duplicate", "source", "challenge", "target", "module_path", "module_bytes", "alias", "empty_exports"])
def test_library_manifest_cannot_hide_incomplete_or_changed_bindings(library, change):
    root, manifest, path = library
    if change == "missing": manifest["records"].pop()
    elif change == "duplicate": manifest["records"][1] = copy.deepcopy(manifest["records"][0])
    elif change == "source": manifest["records"][0]["source_sha256"] = "0" * 64
    elif change == "challenge": manifest["records"][0]["challenge_sha256"] = "0" * 64
    elif change == "target": manifest["records"][0]["qualified_theorem"] += "_different"
    elif change == "module_path": manifest["records"][0]["module_path"] = "../outside.lean"
    elif change == "module_bytes": (root / manifest["records"][0]["module_path"]).write_text("changed")
    elif change == "alias": manifest["foundation_exports"][0]["archive_theorem"] = "Different.target"
    else: manifest["foundation_exports"] = []
    path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError): checker.load_library(root)


def test_valid_manifest_binds_all_native_targets_and_guards(library):
    root, manifest, _ = library
    result, _, _ = checker.load_library(root)
    assert result == manifest and len(result["records"]) == 8


@pytest.mark.parametrize("change", ["extra", "duplicate", "revision", "url", "subdir", "library_path"])
def test_consumer_dependency_drift_fails(library, change):
    root, _, _ = library
    pinned = json.loads((root / "certified_lean/lake-manifest.json").read_text())
    seeded = checker.consumer_manifest(pinned, str(root), "a" * 40)
    if change == "extra": seeded["packages"].append({"name": "unexpected"})
    elif change == "duplicate": seeded["packages"][2] = copy.deepcopy(seeded["packages"][1])
    elif change == "revision": seeded["packages"][1]["rev"] = "b" * 40
    elif change == "url": seeded["packages"][1]["url"] = "https://wrong.invalid/git"
    elif change == "subdir": seeded["packages"][0]["subDir"] = "wrong"
    else: seeded["packages"][0]["type"] = "path"
    with pytest.raises(ValueError): checker.check_dependency_manifest(seeded, pinned, str(root), "a" * 40)


def test_seed_preserves_every_exact_revision_without_mutating_source(library):
    root, _, _ = library
    pinned = json.loads((root / "certified_lean/lake-manifest.json").read_text())
    original = copy.deepcopy(pinned)
    seeded = checker.consumer_manifest(pinned, str(root), "a" * 40)
    assert pinned == original
    actual = checker.check_dependency_manifest(seeded, pinned, str(root), "a" * 40)
    assert len(actual) == 10
    assert {name: p["rev"] for name, p in actual.items() if name != "certifiedResearch"} == {
        p["name"]: p["rev"] for p in pinned["packages"]}


@pytest.mark.parametrize("stdout", [
    "'Archive.target' depends on axioms: [sorryAx]\n",
    "'Archive.target' depends on axioms: [propext]\nextra\n",
    "'Other.target' depends on axioms: [propext]\n",
    "'Archive.target' depends on axioms: [propext]\n'Archive.target' depends on axioms: [sorryAx]\n",
    "", "forged output\n'Archive.target' depends on axioms: [propext]\n",
])
def test_disallowed_missing_duplicate_or_forged_native_reports_fail(stdout):
    with pytest.raises(ValueError):
        checker.audit_axioms(stdout, [{"name": "Public.target", "canonical_name": "Archive.target"}], [])


def test_alias_queries_are_bound_to_canonical_ordered_reports():
    queries = [{"name": "Archive.target", "canonical_name": "Archive.target"},
               {"name": "Public.target", "canonical_name": "Archive.target"},
               {"name": "Consumer.target", "canonical_name": "Consumer.target"}]
    stdout = "'Archive.target' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n" * 2
    stdout += "'Consumer.target' does not depend on any axioms\n"
    checks = []
    checker.audit_axioms(stdout, queries, checks)
    assert len(checks) == 3 and all(r["passed"] for r in checks)
    assert checks[1]["queried_name"] == "Public.target" and checks[1]["alias_resolved"]
    assert checks[-1]["axioms"] == []


@pytest.mark.parametrize("option,value", [("--timeout", "nan"), ("--build-timeout", "inf"),
    ("--setup-timeout", "0"), ("--audit-timeout", "121"), ("--revision", "main")])
def test_cli_rejects_unbounded_caps_or_moving_revision(library, option, value):
    with pytest.raises(SystemExit): checker.main([option, value])


def fake_pipeline(library, monkeypatch, failure=None):
    root, manifest, _ = library
    binary = root / "fixture-lean"
    binary.write_bytes(b"mock compiler identity; no native calls")
    monkeypatch.setattr(checker.LeanToolchain, "_find_binary", lambda name: Path("fixture-" + name))
    canonical = {e["qualified_theorem"]: e["archive_theorem"] for e in manifest["foundation_exports"]}
    def run(report, command, cwd, cap, deadline, env):
        command = list(map(str, command))
        row = {"command": command, "state": "passed", "stdout": "", "stderr": "", "exit_code": 0,
               "remaining_owned_process_groups": [], "direct_child_reaped": True}
        report["commands"].append(row)
        if command[:3] == ["git", "rev-parse", "HEAD"]:
            row["stdout"] = "a" * 40 + "\n"
        elif command[:3] == ["git", "cat-file", "-e"] and failure == "uncommitted":
            row["state"] = "failed"
            raise ValueError("mock absent Git package")
        elif command[:3] == ["git", "ls-tree", "-r"]:
            rows = []
            for path in command[5:]:
                data = (root / path).read_bytes()
                blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                rows.append("100644 blob " + blob + "\t" + path)
            row["stdout"] = "\n".join(rows)
        elif command[1:4] == ["exe", "cache", "get"]:
            clone = cwd / ".lake/packages/certifiedResearch"
            clone.parent.mkdir(parents=True)
            shutil.copytree(root, clone)
            if failure == "clone_module":
                (clone / manifest["records"][0]["module_path"]).write_text("changed clone")
            if failure == "dependency":
                actual = json.loads((cwd / "lake-manifest.json").read_text())
                actual["packages"][1]["rev"] = "b" * 40
                (cwd / "lake-manifest.json").write_text(json.dumps(actual))
        elif command[0] == "git" and command[1] == "-C":
            name = Path(command[2]).name
            seeded = json.loads((cwd / "lake-manifest.json").read_text())
            row["stdout"] = next(p["rev"] for p in seeded["packages"] if p["name"] == name) + "\n"
        elif command[1:] == ["env", "lean", "--version"]:
            row["stdout"] = "Lean (version 4.34.1, fixture)\n"
        elif command[1:] == ["which", "lean"]:
            row["stdout"] = str(binary) + "\n"
        elif command[1:3] == ["build", "Consumer"]:
            assert (cwd / "Consumer.lean").read_bytes().startswith(b"import MathFoundry")
            if failure == "cancel": raise InterruptedError("mock cancelled native build")
        elif command[1:] == ["env", "lean", "Audit.lean"]:
            queries = re.findall(r"#print axioms (\S+)", (cwd / "Audit.lean").read_text())
            row["stdout"] = "".join("'" + canonical.get(name, name) + "' depends on axioms: [propext]\n" for name in queries)
            if failure == "axiom": row["stdout"] = row["stdout"].replace("[propext]", "[sorryAx]", 1)
            if failure == "cleanup": row.update(cleanup_error="mock reaping failure", state="failed")
        elif command[1:3] == ["-c", "import shutil,sys; shutil.rmtree(sys.argv[1])"]:
            shutil.rmtree(command[3])
        return row
    import re
    monkeypatch.setattr(checker, "run_command", run)


@pytest.mark.parametrize("failure", ["uncommitted", "dependency", "clone_module", "axiom", "cleanup", "cancel"])
def test_full_protocol_retains_failures_and_cannot_false_pass(library, monkeypatch, failure):
    root, _, _ = library
    fake_pipeline(library, monkeypatch, failure)
    output = root / "report.json"
    code = checker.main(["--output", str(output)])
    report = json.loads(output.read_text())
    assert code != 0 and report["status"] in {"failed", "interrupted"}
    assert report["model_requests"] == 0
    if failure == "uncommitted": assert "commit" in report["error"]
    if failure == "cleanup": assert report["cleanup"] == "failed"


@pytest.mark.parametrize("narrow", [False, True])
def test_complete_vs_narrow_protocol_reports_different_scope(library, monkeypatch, narrow):
    root, _, _ = library
    fake_pipeline(library, monkeypatch)
    output = root / "report.json"
    assert checker.main(["--output", str(output), *(["--foundations-only"] if narrow else [])]) == 0
    report = json.loads(output.read_text())
    assert report["native_axiom_queries_checked"] == (9 if narrow else 17)
    assert report["distinct_native_constants_checked"] == 9
    assert report["mode"] == ("foundations_only" if narrow else "complete_library")
    assert report["consumer_source_sha256"] != report["consumer_original_source_sha256"] if narrow else (
        report["consumer_source_sha256"] == report["consumer_original_source_sha256"])
    assert not any("update" in r["command"] for r in report["commands"])


def test_existing_report_is_never_overwritten(library):
    root, _, _ = library
    output = root / "report.json"
    output.write_text("original")
    with pytest.raises(SystemExit): checker.main(["--output", str(output)])
    assert output.read_text() == "original"


def test_finite_command_timeout_reaps_owned_group(tmp_path):
    report = {"commands": []}
    with pytest.raises(TimeoutError):
        checker.run_command(report, [sys.executable, "-c", "import time; time.sleep(30)"],
            tmp_path, 0.1, time.monotonic() + 3, {})
    row = report["commands"][0]
    assert row["state"] == "timeout" and row["direct_child_reaped"]
    assert row["remaining_owned_process_groups"] == []


def test_successful_parent_exit_does_not_leave_owned_child(tmp_path):
    report = {"commands": []}
    code = "import subprocess,sys; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);print(p.pid)"
    row = checker.run_command(report, [sys.executable, "-c", code], tmp_path, 3, time.monotonic() + 5, {})
    assert row["state"] == "passed" and row["direct_child_reaped"]
    assert row["remaining_owned_process_groups"] == []


@pytest.mark.parametrize("signum", [signal.SIGINT, signal.SIGTERM])
def test_post_spawn_interrupt_cannot_skip_owned_cleanup(tmp_path, monkeypatch, signum):
    popen = checker.subprocess.Popen
    def interrupted_spawn(*args, **kwargs):
        process = popen(*args, **kwargs)
        signal.getsignal(signum)(signum, None)
        return process
    monkeypatch.setattr(checker.subprocess, "Popen", interrupted_spawn)
    report = {"commands": []}
    with pytest.raises(InterruptedError):
        checker.run_command(report, [sys.executable, "-c", "import time; time.sleep(30)"],
            tmp_path, 3, time.monotonic() + 5, {})
    row = report["commands"][0]
    assert row["state"] == "interrupted" and row["direct_child_reaped"]
    assert row["remaining_owned_process_groups"] == []


def test_cleanup_interrupt_is_fatal_after_reaping(tmp_path, monkeypatch):
    terminate = checker.terminate_process_group
    def interrupted_cleanup(process):
        signal.getsignal(signal.SIGTERM)(signal.SIGTERM, None)
        terminate(process)
    monkeypatch.setattr(checker, "terminate_process_group", interrupted_cleanup)
    report = {"commands": []}
    with pytest.raises(InterruptedError):
        checker.run_command(report, [sys.executable, "-c", "pass"],
            tmp_path, 3, time.monotonic() + 5, {})
    row = report["commands"][0]
    assert row["state"] == "interrupted" and row["direct_child_reaped"]
    assert row["cleanup_interrupts"] == ["SIGTERM"]
    assert row["remaining_owned_process_groups"] == []


def test_temporary_consumer_cleanup_is_owned_and_bounded(tmp_path, monkeypatch):
    monkeypatch.setattr(checker, "ROOT", tmp_path)
    report = {"commands": []}
    with checker.consumer_workspace(report, os.environ.copy()) as consumer:
        (consumer / "fixture").write_text("temporary evidence")
    assert not consumer.exists()
    assert report["temporary_consumer_cleanup"]["status"] == "complete"
    row = report["commands"][0]
    assert row["direct_child_reaped"] and row["remaining_owned_process_groups"] == []
    assert 0 < row["timeout_sec"] <= checker.CLEANUP_TIMEOUT


@pytest.mark.parametrize("failure", ["timeout", "error"])
def test_temporary_cleanup_failure_retains_path_and_primary_error(tmp_path, monkeypatch, failure):
    monkeypatch.setattr(checker, "ROOT", tmp_path)
    monkeypatch.setattr(checker, "CLEANUP_TIMEOUT", 0.1 if failure == "timeout" else 3)
    run = checker.run_command
    def failed_cleanup(report, command, cwd, cap, deadline, env):
        code = "import time; time.sleep(30)" if failure == "timeout" else "raise RuntimeError('cleanup fixture')"
        return run(report, [sys.executable, "-c", code], cwd, cap, deadline, env)
    monkeypatch.setattr(checker, "run_command", failed_cleanup)
    report = {"commands": []}
    try:
        with pytest.raises(ValueError, match="primary fixture"):
            with checker.consumer_workspace(report, os.environ.copy()) as consumer:
                raise ValueError("primary fixture")
        cleanup = report["temporary_consumer_cleanup"]
        assert cleanup["status"] == "failed" and cleanup["retained_path"] == str(consumer)
        row = report["commands"][0]
        assert row["state"] == ("timeout" if failure == "timeout" else "failed")
        assert row["direct_child_reaped"] and row["remaining_owned_process_groups"] == []
    finally:
        shutil.rmtree(consumer)
