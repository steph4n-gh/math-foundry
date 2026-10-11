"""Bounded compiler admission uses real locks and mocked Lean subprocesses.

These cases invoke no Lean or model service. Cross-process owners hold only
temporary flock files and always exit or are explicitly joined by the fixture.
"""
import fcntl
from concurrent.futures import ThreadPoolExecutor
import hashlib
import multiprocessing
import os
from pathlib import Path
import subprocess
import threading
import time

import pytest

from autonomous_math.prover.lean_prover import LeanProofSearch, LeanToolchain
from tests.unit.test_compiler_context_pruning import fixture_prover


def slot_directory(tool, temporary_root):
    key = hashlib.sha256(str(tool.workspace_dir.resolve()).encode()).hexdigest()
    return temporary_root / f"math-foundry-lean-{os.getuid()}-{key}"


def hold_slots(directory, count=None):
    count = LeanToolchain.COMPILER_SLOTS if count is None else count
    directory.mkdir(parents=True, exist_ok=True)
    handles = []
    for index in range(count):
        handle = (directory / f"{index}.lock").open("a")
        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        handles.append(handle)
    return handles


def busy_slots(directory, count=None):
    count = LeanToolchain.COMPILER_SLOTS if count is None else count
    busy = 0
    for index in range(count):
        with (directory / f"{index}.lock").open("a") as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                busy += 1
    return busy


def child_lock_owner(directory, ready, release):
    handles = hold_slots(Path(directory))
    try:
        ready.set()
        release.wait(8)
    finally:
        for handle in handles:
            handle.close()


def tool_fixture(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module

    workspace = tmp_path / "pinned-workspace"
    workspace.mkdir()
    lean, lake = tmp_path / "lean-not-executed", tmp_path / "lake-not-executed"
    lean.write_text("mock compiler binary")
    lake.write_text("mock Lake binary")
    temporary_root = tmp_path / "external-locks"
    temporary_root.mkdir()
    monkeypatch.setattr(module.tempfile, "gettempdir", lambda: str(temporary_root))
    tool = LeanToolchain(lean_bin=lean, lake_bin=lake, workspace_dir=workspace)
    monkeypatch.setattr(tool, "ensure_workspace_built", lambda: True)
    spawned, cleaned = [], []

    class ProcessDouble:
        pid = 123456789
        returncode = 0

        def __init__(self):
            self.calls = []
            self.action = None

        def communicate(self, source=None, timeout=None):
            assert tool._active_process is self
            self.calls.append((source, timeout))
            if self.action is not None:
                return self.action(source, timeout)
            return "bounded compiler stdout", "bounded compiler stderr"

    process = ProcessDouble()

    def popen(args, **kwargs):
        spawned.append((args, kwargs))
        return process

    monkeypatch.setattr(module.subprocess, "Popen", popen)
    monkeypatch.setattr(module, "terminate_process_group", lambda owned: cleaned.append(owned))
    return module, tool, process, spawned, cleaned, temporary_root


@pytest.mark.parametrize("timeout", [0, -1, float("nan"), float("inf")])
def test_nonfinite_or_nonpositive_budget_is_rejected_before_admission(tmp_path, monkeypatch, timeout):
    _, tool, _, spawned, _, root = tool_fixture(tmp_path, monkeypatch)
    with pytest.raises(ValueError, match="finite and positive"):
        tool.run_lean_code("not launched", timeout=timeout)
    assert not spawned and not list(root.iterdir())


def test_spawn_preserves_exact_stdin_pinned_workspace_environment_and_cap(tmp_path, monkeypatch):
    _, tool, process, spawned, cleaned, root = tool_fixture(tmp_path, monkeypatch)
    monkeypatch.setenv("LEAN_PATH", "/untrusted/shadow")
    monkeypatch.setenv("PRESERVED_COMPILER_SETTING", "standard")
    source = "theorem exact_transport : True := by trivial\n"
    assert tool.run_lean_code(source, timeout=10)[0] == 0
    args, options = spawned[0]
    assert args == [str(tool.lake_bin), "env", "lean", "--stdin"]
    assert options["cwd"] == tool.workspace_dir
    assert options["start_new_session"] is True and options["text"] is True
    assert options["stdin"] == options["stdout"] == options["stderr"] == subprocess.PIPE
    assert "LEAN_PATH" not in options["env"]
    assert options["env"]["PATH"].startswith(str(Path.home() / ".elan/bin") + ":")
    assert options["env"]["PRESERVED_COMPILER_SETTING"] == "standard"
    assert process.calls[0][0] == source and 0 < process.calls[0][1] <= 10
    assert cleaned == [process] and not tool.active_process_groups()
    assert tool.last_run_metadata["compiler_launched"] is True
    assert tool.last_run_metadata["compiler_slots"] == LeanToolchain.COMPILER_SLOTS
    assert busy_slots(slot_directory(tool, root)) == 0
    assert not any("lock" in path.name for path in tool.workspace_dir.rglob("*"))


def test_sixteen_independent_workers_never_exceed_configured_compiler_slots(tmp_path, monkeypatch):
    module, first, _, _, _, _ = tool_fixture(tmp_path, monkeypatch)
    tools = [LeanToolchain(lean_bin=first.lean_bin, lake_bin=first.lake_bin,
                          workspace_dir=first.workspace_dir) for _ in range(16)]
    for tool in tools:
        monkeypatch.setattr(tool, "ensure_workspace_built", lambda: True)
    lock, admission_full, release = threading.Lock(), threading.Event(), threading.Event()
    counts = {"active": 0, "peak": 0, "spawned": 0}

    class Process:
        returncode = 0

        def __init__(self):
            with lock:
                counts["spawned"] += 1
                counts["active"] += 1
                counts["peak"] = max(counts["peak"], counts["active"])
                self.pid = 123450000 + counts["spawned"]
                self.active = True
                if counts["active"] == LeanToolchain.COMPILER_SLOTS:
                    admission_full.set()

        def communicate(self, source=None, timeout=None):
            assert release.wait(2)
            return "", ""

    def cleanup(process):
        if process is not None:
            with lock:
                if process.active:
                    counts["active"] -= 1
                    process.active = False

    monkeypatch.setattr(module.subprocess, "Popen", lambda *args, **kw: Process())
    monkeypatch.setattr(module, "terminate_process_group", cleanup)
    with ThreadPoolExecutor(max_workers=16) as executor:
        futures = [executor.submit(tool.run_lean_code, "same bytes", 10) for tool in tools]
        try:
            assert admission_full.wait(2)
            time.sleep(0.04)
            assert counts["spawned"] == counts["active"] == LeanToolchain.COMPILER_SLOTS
        finally:
            release.set()
        assert all(future.result(timeout=3)[0] == 0 for future in futures)
    assert counts == {"active": 0, "peak": LeanToolchain.COMPILER_SLOTS, "spawned": 16}
    assert all(not tool.active_process_groups() for tool in tools)


@pytest.mark.parametrize("kill_owner", [False, True])
def test_cross_process_contention_releases_on_exit_and_process_death(tmp_path, monkeypatch, kill_owner):
    _, tool, _, spawned, _, root = tool_fixture(tmp_path, monkeypatch)
    context = multiprocessing.get_context("spawn")
    ready, release = context.Event(), context.Event()
    owner = context.Process(target=child_lock_owner,
                            args=(str(slot_directory(tool, root)), ready, release))
    owner.start()
    try:
        assert ready.wait(5), "temporary lock owner did not become ready"
        assert busy_slots(slot_directory(tool, root)) == LeanToolchain.COMPILER_SLOTS
        ret, _, error = tool.run_lean_code("must remain queued", timeout=0.04)
        assert ret == 124 and "admission" in error
        assert not spawned and tool.last_run_metadata["compiler_launched"] is False
        assert tool.last_run_metadata["failure_kind"] == "compiler_admission_timeout"
        if kill_owner:
            owner.terminate()
        else:
            release.set()
        owner.join(5)
        assert not owner.is_alive()
        assert busy_slots(slot_directory(tool, root)) == 0
        assert tool.run_lean_code("same exact source", timeout=10)[0] == 0
    finally:
        # A killed child may die while holding the Event condition mutex.
        # Do not touch that synchronization object after process death.
        if owner.is_alive():
            release.set()
        owner.join(2)
        if owner.is_alive():
            owner.terminate()
            owner.join(2)


def test_symlinked_workspace_shares_slots_and_distinct_workspace_does_not(tmp_path, monkeypatch):
    module, tool, _, spawned, _, root = tool_fixture(tmp_path, monkeypatch)
    alias = tmp_path / "alias"
    alias.symlink_to(tool.workspace_dir, target_is_directory=True)
    same = LeanToolchain(lean_bin=tool.lean_bin, lake_bin=tool.lake_bin, workspace_dir=alias)
    separate_path = tmp_path / "different-workspace"
    separate_path.mkdir()
    separate = LeanToolchain(lean_bin=tool.lean_bin, lake_bin=tool.lake_bin, workspace_dir=separate_path)
    monkeypatch.setattr(same, "ensure_workspace_built", lambda: True)
    monkeypatch.setattr(separate, "ensure_workspace_built", lambda: True)
    held = hold_slots(slot_directory(tool, root))
    try:
        assert slot_directory(same, root) == slot_directory(tool, root)
        assert same.run_lean_code("same workspace blocked", timeout=0.02)[0] == 124
        # A different pinned workspace has a separate resource identity.
        monkeypatch.setattr(module.subprocess, "Popen", lambda *args, **kw: type("Process", (), {
            "pid": 123456790, "returncode": 0,
            "communicate": lambda self, source=None, timeout=None: ("", "")})())
        assert separate.run_lean_code("independent workspace", timeout=10)[0] == 0
        assert not spawned
    finally:
        for handle in held:
            handle.close()


def test_workspace_check_and_queue_wait_are_inside_same_compiler_deadline(tmp_path, monkeypatch):
    module, tool, process, _, _, root = tool_fixture(tmp_path, monkeypatch)
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])

    def checked():
        clock[0] += 3
        return True

    monkeypatch.setattr(tool, "ensure_workspace_built", checked)
    held = hold_slots(slot_directory(tool, root))

    def release_after_wait(duration):
        clock[0] += 2
        for handle in held:
            handle.close()

    monkeypatch.setattr(tool._cancelled, "wait", release_after_wait)
    try:
        assert tool.run_lean_code("exact bounded bytes", timeout=10)[0] == 0
        assert process.calls == [("exact bounded bytes", 5)]
        assert tool.last_run_metadata["admission_wait_sec"] == 2
        assert tool.last_run_metadata["compiler_execution_budget_sec"] == 5
    finally:
        for handle in held:
            handle.close()


def test_queue_deadline_expiry_records_no_launched_compiler(tmp_path, monkeypatch):
    module, tool, process, spawned, _, root = tool_fixture(tmp_path, monkeypatch)
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    held = hold_slots(slot_directory(tool, root))
    monkeypatch.setattr(tool._cancelled, "wait", lambda duration: clock.__setitem__(0, clock[0] + duration))
    try:
        assert tool.run_lean_code("never compiled", timeout=0.1)[0] == 124
        assert not spawned and not process.calls
        assert tool.last_run_metadata["compiler_launched"] is False
        assert tool.last_run_metadata["failure_kind"] == "compiler_admission_timeout"
        assert tool.last_run_metadata["admission_wait_sec"] == pytest.approx(0.1)
        assert tool.last_run_metadata["compiler_execution_sec"] == 0
    finally:
        for handle in held:
            handle.close()


def test_toolchain_check_expiry_is_not_mislabeled_as_admission_or_kernel_timeout(tmp_path, monkeypatch):
    module, tool, _, spawned, _, _ = tool_fixture(tmp_path, monkeypatch)
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])

    def checked():
        clock[0] += 10
        return True

    monkeypatch.setattr(tool, "ensure_workspace_built", checked)
    assert tool.run_lean_code("not launched", timeout=10)[0] == 124
    assert not spawned and tool.last_run_metadata["compiler_launched"] is False
    assert tool.last_run_metadata["failure_kind"] == "toolchain_check_timeout"


def test_cancellation_during_toolchain_check_is_fatal_before_admission(tmp_path, monkeypatch):
    _, tool, _, spawned, _, root = tool_fixture(tmp_path, monkeypatch)

    def cancelled_check():
        tool.cancel()
        return True

    monkeypatch.setattr(tool, "ensure_workspace_built", cancelled_check)
    with pytest.raises(InterruptedError):
        tool.run_lean_code("not launched", timeout=10)
    assert not spawned and not list(root.iterdir())


def test_cancelled_queued_attempt_never_spawns_or_resets_cancel_for_retry(tmp_path, monkeypatch):
    _, tool, _, spawned, _, root = tool_fixture(tmp_path, monkeypatch)
    held = hold_slots(slot_directory(tool, root))
    waiting = threading.Event()
    original_wait = tool._cancelled.wait
    errors = []

    def queue_wait(timeout):
        waiting.set()
        return original_wait(timeout)

    monkeypatch.setattr(tool._cancelled, "wait", queue_wait)

    def run():
        try:
            tool.run_lean_code("cancelled queued source", timeout=10)
        except BaseException as error:
            errors.append(error)

    thread = threading.Thread(target=run)
    thread.start()
    try:
        assert waiting.wait(2)
        tool.cancel()
        thread.join(2)
        assert not thread.is_alive() and len(errors) == 1
        assert isinstance(errors[0], InterruptedError) and not spawned
        with pytest.raises(InterruptedError):
            tool.run_lean_code("retry after cancellation", timeout=30)
        assert not spawned
    finally:
        tool.cancel()
        for handle in held:
            handle.close()
        thread.join(2)


def test_launch_ownership_assignment_cannot_race_completed_cancel(tmp_path, monkeypatch):
    module, tool, process, _, cleaned, _ = tool_fixture(tmp_path, monkeypatch)
    spawning, release_spawn, cancel_finished = threading.Event(), threading.Event(), threading.Event()
    errors = []

    def popen(*args, **kwargs):
        spawning.set()
        assert release_spawn.wait(2)
        return process

    monkeypatch.setattr(module.subprocess, "Popen", popen)

    def communicate(source=None, timeout=None):
        assert cancel_finished.wait(2)
        return "cancelled compiler output", ""

    process.communicate = communicate

    def run():
        try:
            tool.run_lean_code("launch race source", timeout=10)
        except BaseException as error:
            errors.append(error)

    def cancel():
        tool.cancel()
        cancel_finished.set()

    worker = threading.Thread(target=run)
    worker.start()
    assert spawning.wait(2)
    canceller = threading.Thread(target=cancel)
    canceller.start()
    try:
        # Cancel must synchronize with the in-progress launch/ownership handoff.
        assert not cancel_finished.wait(0.04)
    finally:
        release_spawn.set()
        canceller.join(2)
        worker.join(2)
    assert not worker.is_alive() and not canceller.is_alive()
    assert len(errors) == 1 and isinstance(errors[0], InterruptedError)
    assert process in cleaned and not tool.active_process_groups()


@pytest.mark.parametrize("returncode", [0, 1])
def test_admission_slot_is_held_until_owned_cleanup_finishes(tmp_path, monkeypatch, returncode):
    module, tool, process, _, _, root = tool_fixture(tmp_path, monkeypatch)
    process.returncode = returncode
    snapshots = []

    def cleanup(owned):
        assert owned is process
        snapshots.append(busy_slots(slot_directory(tool, root)))

    monkeypatch.setattr(module, "terminate_process_group", cleanup)
    assert tool.run_lean_code("exact cleanup source", timeout=10)[0] == returncode
    assert snapshots == [1]
    assert busy_slots(slot_directory(tool, root)) == 0


def test_spawned_timeout_retains_partial_output_and_ownership_until_cleanup(tmp_path, monkeypatch):
    module, tool, process, _, _, root = tool_fixture(tmp_path, monkeypatch)
    snapshots = []

    def communicate(source, timeout):
        if len(process.calls) == 1:
            raise subprocess.TimeoutExpired("mock Lean", timeout)
        return "retained stdout", "retained stderr"

    process.action = communicate
    monkeypatch.setattr(module, "terminate_process_group",
                        lambda owned: snapshots.append(busy_slots(slot_directory(tool, root))))
    ret, stdout, stderr = tool.run_lean_code("exact timed source", timeout=30)
    assert ret == 124 and stdout == "retained stdout" and "retained stderr" in stderr
    assert tool.last_run_metadata["compiler_launched"] is True
    assert tool.last_run_metadata["failure_kind"] == "compiler_timeout"
    assert snapshots == [1] and busy_slots(slot_directory(tool, root)) == 0
    assert process.calls[0][0] == "exact timed source" and process.calls[1] == (None, None)


def test_failed_owned_cleanup_does_not_release_capacity_for_a_live_process(tmp_path, monkeypatch):
    module, tool, process, _, cleaned, root = tool_fixture(tmp_path, monkeypatch)

    def cannot_reap(owned):
        assert owned is process
        raise PermissionError("live owned group cannot be reaped")

    monkeypatch.setattr(module, "terminate_process_group", cannot_reap)
    with pytest.raises(PermissionError, match="live owned group"):
        tool.run_lean_code("not accepted after failed cleanup", timeout=10)
    assert tool._active_process is process
    assert busy_slots(slot_directory(tool, root)) == 1
    # A later successful explicit cancellation resolves ownership and capacity.
    monkeypatch.setattr(module, "terminate_process_group", lambda owned: cleaned.append(owned))
    tool.cancel()
    assert process in cleaned and not tool.active_process_groups()
    assert busy_slots(slot_directory(tool, root)) == 0


@pytest.mark.parametrize("failure", [PermissionError("slot permissions"), OSError("slot filesystem")])
def test_lock_operational_errors_propagate_and_are_not_timeout_or_proof(tmp_path, monkeypatch, failure):
    module, tool, _, spawned, _, _ = tool_fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(module.fcntl, "flock", lambda *args: (_ for _ in ()).throw(failure))
    with pytest.raises(type(failure), match="slot"):
        tool.run_lean_code("not compiled", timeout=10)
    assert not spawned and tool.last_run_metadata["compiler_launched"] is False
    assert "failure_kind" not in tool.last_run_metadata


def test_spawn_error_releases_unused_slot_and_preserves_operational_failure(tmp_path, monkeypatch):
    module, tool, _, _, _, root = tool_fixture(tmp_path, monkeypatch)
    monkeypatch.setattr(module.subprocess, "Popen", lambda *a, **kw: (_ for _ in ()).throw(
        FileNotFoundError("mock compiler missing")))
    with pytest.raises(FileNotFoundError, match="compiler missing"):
        tool.run_lean_code("not compiled", timeout=10)
    assert not tool.active_process_groups() and busy_slots(slot_directory(tool, root)) == 0
    assert tool.last_run_metadata["compiler_launched"] is False


def test_admission_expiry_retries_same_bytes_and_counts_only_launched_compilers(tmp_path, monkeypatch):
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [124, 0])
    original = tool.run_lean_code

    def run(source, timeout):
        result = original(source, timeout)
        tool.last_run_metadata = {"compiler_launched": result[0] != 124,
                                 "compiler_slots": LeanToolchain.COMPILER_SLOTS,
                                 "admission_wait_sec": 10 if result[0] == 124 else 0,
                                 "compiler_execution_sec": 0 if result[0] == 124 else 1}
        if result[0] == 124:
            tool.last_run_metadata["failure_kind"] = "compiler_admission_timeout"
        return result

    monkeypatch.setattr(tool, "run_lean_code", run)
    result = prover.prove_challenge(target, tmp_path / "verified", save_verified_artifact=False)
    assert result.is_proven and len(synth.requests) == 1
    assert tool.calls[0][0] == tool.calls[1][0]
    assert [cap for _, cap in tool.calls] == [10, 30]
    assert result.attempts_count == 1
    assert result.diagnostics[0]["failure_kind"] == "compiler_admission_timeout"
    assert result.diagnostics[0]["compiler_launched"] is False
    assert result.diagnostics[0]["compiler_elapsed_sec"] == 0
    assert result.diagnostics[1]["phase"] == "codex_synthesis_timeout_retry"


def test_two_uncompiled_model_attempts_never_qualify_third_request_as_progress(tmp_path, monkeypatch):
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [124] * 4)
    original = tool.run_lean_code

    def run(source, timeout):
        result = original(source, timeout)
        tool.last_run_metadata = {"compiler_launched": False, "compiler_execution_sec": 0,
                                 "failure_kind": "compiler_admission_timeout"}
        return result

    monkeypatch.setattr(tool, "run_lean_code", run)
    result = prover.prove_challenge(target, tmp_path / "verified", save_verified_artifact=False)
    assert not result.is_proven and result.attempts_count == 0
    assert len(synth.requests) == 2 and len(tool.calls) == 4
    assert [cap for _, cap in tool.calls] == [10, 30, 10, 30]
    assert all(trace["status"] == "COMPILER_ADMISSION_TIMEOUT" for trace in result.synthesis_attempts)
    assert all(not trace["compiler_retry"] for trace in result.synthesis_attempts)
    assert not LeanProofSearch._repair_progress(result.diagnostics)


def test_retry_mapping_keeps_admission_distinct_and_terminal_rejection_fail_closed():
    import run_research as runner

    diagnostics = [{"exit_code": 124, "compiler_launched": False,
                    "failure_kind": "compiler_admission_timeout"}]
    for synthesis in ([], [{"status": "COMPILER_ADMISSION_TIMEOUT"}]):
        attempt = {"status": "UNRESOLVED", "diagnostics": diagnostics,
                   "synthesis_attempts": synthesis}
        assert runner._proof_retry_reason(attempt) == "compiler_admission_timeout"
        assert runner._retryable(attempt)
    for terminal in ("KERNEL_REJECTED", "PROOF_BODY_REJECTED", "COUNTEREXAMPLE_REJECTED"):
        assert not runner._retryable({"status": "UNRESOLVED", "diagnostics": diagnostics,
                                      "synthesis_attempts": [{"status": terminal}]})


def test_admission_retry_backoff_stays_finite_and_changed_context_resets_it(monkeypatch):
    import run_research as runner

    monkeypatch.setattr(runner.time, "time", lambda: 1000.0)
    record = {"proof_search_key": "same", "proof_attempt": {
        "status": "UNRESOLVED", "synthesis_attempts": [{"status": "COMPILER_ADMISSION_TIMEOUT"}]}}
    runner._schedule_proof_retry(record, "same", 50)
    assert record["proof_retry_reason"] == "compiler_admission_timeout"
    assert record["next_retry_at"] == 1300 and record["next_retry_iteration"] == 52
    for _ in range(100):
        runner._schedule_proof_retry(record, "same", 50)
    assert record["proof_retry_count"] == 5
    assert record["next_retry_at"] == 4600 and record["next_retry_iteration"] == 66
    record["proof_search_key"] = "fresh-current-receipt-bindings"
    runner._schedule_proof_retry(record, "same", 50)
    assert record["proof_retry_count"] == 1 and record["next_retry_at"] == 1300
