"""Portable replay binds the whole native premise and fails closed without AI."""
import hashlib
import importlib.util
import json
from pathlib import Path
import signal

import pytest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("public_replay", ROOT / "scripts/replay_results.py")
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)


@pytest.fixture
def collection(tmp_path, monkeypatch):
    monkeypatch.setattr(replay, "ROOT", tmp_path)
    records = []
    for index in range(3):
        semantic = {"id": f"portable_{index}", "lhs_expr": {"node_type": "invariant", "name": "order"},
            "rel": ">=", "rhs_expr": {"node_type": "constant", "value": 0}, "guard_predicate": None}
        challenge, name = replay.trusted_lean.render_challenge(replay.Conjecture.from_dict(dict(semantic, statement="")))
        source = challenge.replace("  sorry", "  positivity")
        record = {"id": semantic["id"], "theorem_name": name, "conjecture": semantic}
        for kind, text in (("source", source), ("challenge", challenge)):
            file = tmp_path / "results" / f"{kind}-{index}.lean"
            file.parent.mkdir(exist_ok=True)
            file.write_text(text)
            record[kind + "_path"] = str(file.relative_to(tmp_path))
            record[kind + "_sha256"] = hashlib.sha256(file.read_bytes()).hexdigest()
        records.append(record)
    catalog = tmp_path / "results/catalog.json"
    def save():
        catalog.write_text(json.dumps({"schema_version": 1, "records": records}))
    save()
    workspace = tmp_path / "certified_lean"
    workspace.mkdir()
    for name in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
        (workspace / name).write_bytes((ROOT / "certified_lean" / name).read_bytes())
    return tmp_path, records, catalog, save


def invoke(collection, *args):
    root, records, catalog, save = collection
    output = root / "report.json"
    code = replay.main(["--catalog", str(catalog), "--output", str(output), *args])
    return code, json.loads(output.read_text())


def change_artifact(root, record, kind, mutate):
    file = root / record[kind + "_path"]
    file.write_text(mutate(file.read_text()))
    record[kind + "_sha256"] = hashlib.sha256(file.read_bytes()).hexdigest()


def test_check_only_all_bindings_without_constructing_toolchain(collection, monkeypatch):
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("check-only invoked Lean"))
    code, report = invoke(collection, "--check-only", "--limit", "1")
    assert code == 0 and report["status"] == "passed"
    assert report["binding_checked_count"] == 3 and report["selected_count"] == 1
    assert report["kernel_replay_performed"] is False and report["model_requests"] == 0
    assert report["kernel_passed_count"] == 0 and report["records"][0]["kernel_passed"] is None


def test_tamper_in_unselected_record_fails_before_compiler(collection, monkeypatch):
    root, records, _, _ = collection
    (root / records[2]["source_path"]).write_text("tampered")
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("tamper invoked Lean"))
    code, report = invoke(collection, "--limit", "1")
    assert code == 1 and report["status"] == "failed" and "Changed source" in report["error"]


def test_updated_hash_does_not_hide_changed_target_or_premise(collection):
    root, records, _, save = collection
    # Rehash both artifacts so their complete prefixes still agree; the native AST must reject them.
    for artifact_kind in ("source", "challenge"):
        change_artifact(root, records[0], artifact_kind,
            lambda text: text.replace("(G : SimpleGraph V)", "(G : SimpleGraph V) (hFalse : False)"))
    save()
    code, report = invoke(collection, "--check-only")
    assert code == 1 and "complete premise differs" in report["error"]


def test_changed_semantic_guard_is_rejected(collection):
    _, records, _, save = collection
    records[0]["conjecture"]["guard_predicate"] = {"node_type": "guard", "predicate_type": "property",
        "property_name": "is_connected", "negated": False}
    save()
    code, report = invoke(collection, "--check-only")
    assert code == 1 and "complete premise differs" in report["error"]


@pytest.mark.parametrize("change", ["name", "id", "duplicate", "absolute", "traversal", "symlink"])
def test_identity_and_artifact_path_fail_closed(collection, change):
    root, records, _, save = collection
    if change == "name": records[0]["theorem_name"] = "different_target"
    elif change == "id": records[0]["conjecture"]["id"] = "different_id"
    elif change == "duplicate": records[1] = records[0].copy()
    elif change == "absolute": records[0]["source_path"] = str(root / records[0]["source_path"])
    elif change == "traversal": records[0]["source_path"] = "results/../" + records[0]["source_path"]
    else:
        file = root / records[0]["source_path"]
        target = file.with_suffix(".original")
        file.rename(target); file.symlink_to(target)
    save()
    code, report = invoke(collection, "--check-only")
    assert code == 1 and report["status"] == "failed"


def test_shards_are_disjoint_complete_and_limit_is_applied_after_shard(collection):
    _, records, _, _ = collection
    left = replay.select_records(records, 0, 2)
    right = replay.select_records(records, 1, 2)
    assert [r["id"] for r in left] == ["portable_0", "portable_2"]
    assert [r["id"] for r in right] == ["portable_1"]
    assert set(r["id"] for r in left).isdisjoint(r["id"] for r in right)
    assert len(left) + len(right) == len(records)
    assert replay.select_records(records, 0, 2, 1) == left[:1]


def test_repeated_id_cli_preserves_catalog_order_and_full_binding_checks(collection, monkeypatch):
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("check-only invoked Lean"))
    code, report = invoke(collection, "--check-only", "--id", "portable_2", "--id", "portable_0")
    assert code == 0 and report["binding_checked_count"] == 3 and report["selected_count"] == 2
    assert report["requested_ids"] == ["portable_2", "portable_0"]
    assert [row["id"] for row in report["records"]] == ["portable_0", "portable_2"]
    assert report["model_requests"] == 0 and report["kernel_replay_performed"] is False


def test_id_filter_preserves_catalog_position_shards_then_applies_limit(collection):
    code, report = invoke(collection, "--check-only", "--id", "portable_1", "--id", "portable_2",
        "--shard-index", "0", "--shard-count", "2", "--limit", "1")
    assert code == 0 and [row["id"] for row in report["records"]] == ["portable_2"]
    assert report["binding_checked_count"] == 3


@pytest.mark.parametrize("selection", [["missing"], ["portable_0", "missing"], [""]])
def test_unknown_or_empty_id_cli_fails_before_compiler_even_with_limit(collection, monkeypatch, selection):
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("unknown ID invoked Lean"))
    args = [part for identifier in selection for part in ("--id", identifier)]
    code, report = invoke(collection, "--limit", "1", *args)
    assert code == 1 and report["status"] == "failed" and "Unknown theorem ID" in report["error"]
    assert report["selected_count"] == 0 and not report["kernel_replay_performed"]
    assert report["binding_checked_count"] == 3


def test_known_id_outside_requested_shard_refuses_empty_result(collection, monkeypatch):
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("empty selection invoked Lean"))
    code, report = invoke(collection, "--id", "portable_1", "--shard-index", "0", "--shard-count", "2")
    assert code == 1 and "No records selected" in report["error"]


def test_named_selection_cannot_ignore_tampered_unselected_proof(collection, monkeypatch):
    root, records, _, _ = collection
    (root / records[2]["challenge_path"]).write_text("tampered unselected challenge")
    monkeypatch.setattr(replay, "LeanToolchain", lambda **kw: pytest.fail("tamper invoked Lean"))
    code, report = invoke(collection, "--id", "portable_0")
    assert code == 1 and "Changed challenge" in report["error"]


def test_empty_explicit_id_collection_is_not_equivalent_to_select_all(collection):
    with pytest.raises(ValueError, match="At least one theorem ID"):
        replay.select_records(collection[1], ids=[])


@pytest.mark.parametrize("args", [(0, 0, None), (2, 2, None), (-1, 2, None), (0, 1, 0), (3, 4, None)])
def test_invalid_or_empty_shards_do_not_report_vacuous_success(collection, args):
    with pytest.raises(ValueError): replay.select_records(collection[1], *args)


@pytest.mark.parametrize("value", ["0", "-1", "121", "inf", "nan"])
def test_cli_rejects_unbounded_or_nonpositive_compiler_timeout(collection, value):
    with pytest.raises(SystemExit) as exc:
        replay.main(["--timeout", value, "--output", str(collection[0] / "invalid.json")])
    assert exc.value.code == 2 and not (collection[0] / "invalid.json").exists()


def test_existing_output_is_never_overwritten(collection):
    output = collection[0] / "report.json"
    output.write_text("preserve")
    with pytest.raises(SystemExit): invoke(collection, "--check-only")
    assert output.read_text() == "preserve"


def fake_toolchain(monkeypatch, behavior):
    instances = []
    class Toolchain:
        def __init__(self, workspace_dir):
            self.workspace_dir = workspace_dir; self.calls = []; self.cancelled = False
            self.last_run_metadata = {"compiler_launched": True}
            instances.append(self)
        def ensure_workspace_built(self): return True
        def run_lean_code(self, source, timeout):
            self.calls.append((source, timeout)); return behavior(source, timeout)
        def cancel(self): self.cancelled = True
        def active_process_groups(self): return []
    monkeypatch.setattr(replay, "LeanToolchain", Toolchain)
    monkeypatch.setattr(replay, "_compiler_identity", lambda tc: {"version": "Fixture", "binary_sha256": "a" * 64})
    return instances


def test_duplicate_requested_id_replays_once_with_unchanged_cap_and_cleanup(collection, monkeypatch):
    instances = fake_toolchain(monkeypatch, lambda source, timeout:
        (0, "'portable_1' depends on axioms: [propext]\n", ""))
    code, report = invoke(collection, "--id", "portable_1", "--id", "portable_1", "--timeout", "19")
    assert code == 0 and report["selected_count"] == 1 and report["binding_checked_count"] == 3
    assert report["records"][0]["id"] == "portable_1" and report["kernel_passed_count"] == 1
    assert len(instances[0].calls) == 1 and instances[0].calls[0][1] == 19 and instances[0].cancelled


@pytest.mark.parametrize("result,expected", [
    ((0, "'portable_0' depends on axioms: [propext, Classical.choice, Quot.sound]\n", ""), True),
    ((0, "'portable_0' depends on axioms: [sorryAx]\n", ""), False),
    ((0, "'wrong_target' depends on axioms: [propext]\n", ""), False),
    ((0, "'portable_0' depends on axioms: []\n'portable_0' depends on axioms: [sorryAx]\n", ""), False),
    ((0, "'portable_0' depends on axioms: []\ntrailing forged output\n", ""), False),
    ((1, "'portable_0' depends on axioms: []\n", "error: compilation failed"), False),
    ((124, "partial output", "timed out"), False),
])
def test_kernel_outcome_requires_exact_final_allowed_axiom_report(collection, monkeypatch, result, expected):
    instances = fake_toolchain(monkeypatch, lambda source, timeout: result)
    code, report = invoke(collection, "--limit", "1", "--timeout", "17")
    assert code == (0 if expected else 1)
    assert report["records"][0]["kernel_passed"] is expected
    assert report["kernel_passed_count"] == int(expected)
    assert instances[0].cancelled and len(instances[0].calls) == 1
    source, timeout = instances[0].calls[0]
    assert source.endswith("\n#print axioms portable_0\n") and timeout == 17
    assert report["remaining_owned_process_groups"] == [] and report["model_requests"] == 0


def test_changed_bytes_during_replay_invalidate_acceptance(collection, monkeypatch):
    root, records, _, _ = collection
    def mutate(source, timeout):
        (root / records[0]["source_path"]).write_text("changed during replay")
        return 0, "'portable_0' depends on axioms: [propext]\n", ""
    instances = fake_toolchain(monkeypatch, mutate)
    code, report = invoke(collection, "--limit", "1")
    assert code == 1 and report["records"][0]["binding_passed"] is False
    assert report["kernel_passed_count"] == 0 and instances[0].cancelled


def test_cancellation_stops_serial_replay_and_cleans_owned_toolchain(collection, monkeypatch):
    def cancelled(source, timeout): raise InterruptedError("cancelled fixture")
    instances = fake_toolchain(monkeypatch, cancelled)
    code, report = invoke(collection)
    assert code == 130 and report["status"] == "interrupted"
    assert len(instances[0].calls) == 1 and instances[0].cancelled and report["cleanup"] == "complete"
    assert report["kernel_replay_performed"] is True and report["interrupted_count"] == 1


def test_final_compiler_identity_change_invalidates_report(collection, monkeypatch):
    fake_toolchain(monkeypatch, lambda source, timeout:
        (0, "'portable_0' depends on axioms: [propext]\n", ""))
    identities = iter([{"version": "Fixture", "binary_sha256": "a" * 64},
        {"version": "Fixture", "binary_sha256": "b" * 64}])
    monkeypatch.setattr(replay, "_compiler_identity", lambda tc: next(identities))
    code, report = invoke(collection, "--limit", "1")
    assert code == 1 and report["status"] == "failed" and "compiler changed" in report["error"]


def test_unselected_artifact_changed_during_replay_invalidates_whole_binding_report(collection, monkeypatch):
    root, records, _, _ = collection
    def mutate(source, timeout):
        (root / records[2]["source_path"]).write_text("changed unselected proof")
        return 0, "'portable_0' depends on axioms: [propext]\n", ""
    fake_toolchain(monkeypatch, mutate)
    code, report = invoke(collection, "--limit", "1")
    assert code == 1 and report["status"] == "failed" and "Changed source" in report["error"]


def test_relative_catalog_is_bound_to_collection_root(collection):
    root = collection[0]
    output = root / "relative-report.json"
    assert replay.main(["--catalog", "results/catalog.json", "--check-only", "--output", str(output)]) == 0
    assert json.loads(output.read_text())["binding_checked_count"] == 3


def test_cleanup_failure_cannot_leave_passed_report(collection, monkeypatch):
    instances = fake_toolchain(monkeypatch, lambda source, timeout:
        (0, "'portable_0' depends on axioms: [propext]\n", ""))
    original = replay.LeanToolchain.cancel
    def fail(self): original(self); raise RuntimeError("fixture cleanup failure")
    monkeypatch.setattr(replay.LeanToolchain, "cancel", fail)
    code, report = invoke(collection, "--limit", "1")
    assert code == 1 and report["status"] == "failed" and report["cleanup"] == "failed"


def test_sigterm_uses_interrupted_cleanup_and_restores_handler(collection, monkeypatch):
    handlers = {}
    previous = signal.getsignal(signal.SIGTERM)
    def install(sig, handler): handlers[sig] = handler
    monkeypatch.setattr(replay.signal, "signal", install)
    def terminated(source, timeout): handlers[signal.SIGTERM](signal.SIGTERM, None)
    instances = fake_toolchain(monkeypatch, terminated)
    code, report = invoke(collection, "--limit", "1")
    assert code == 130 and "SIGTERM" in report["error"] and instances[0].cancelled
    assert handlers[signal.SIGTERM] == previous
