"""Real spawned worker lifecycle regressions, with no model or solver calls."""
import hashlib
import json
import multiprocessing
import multiprocessing.util
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

import pytest
import run_research as runner

ORIGINAL_WORKER = runner._job_worker


def event(directory, name, **fields):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / "events.jsonl").open("a") as stream:
        stream.write(json.dumps({"event": name, "pid": os.getpid(),
                                 "monotonic": time.monotonic(), **fields}) + "\n")


class OwnedChild:
    def __init__(self, directory, delay, fail=False):
        self.directory, self.delay, self.fail = Path(directory), delay, fail
        code = """import os, signal, sys, time
from pathlib import Path
delay = float(sys.argv[1])
def terminate(signum, frame):
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    time.sleep(delay)
    raise SystemExit(0)
signal.signal(signal.SIGTERM, terminate)
Path(sys.argv[2]).write_text(str(os.getpid()))
while True: time.sleep(.05)
"""
        self.process = subprocess.Popen([sys.executable, "-B", "-c", code,
                                         str(delay), str(self.directory / "child_ready")],
                                        start_new_session=True)
        until = time.monotonic() + 3
        while not (self.directory / "child_ready").exists():
            if time.monotonic() >= until:
                self.process.kill()
                self.process.wait(timeout=2)
                raise RuntimeError("Fixture child startup timed out")
            time.sleep(.01)
        event(self.directory, "child_started", child_pid=self.process.pid)

    def active_process_groups(self):
        return [self.process.pid] if self.process.poll() is None else []

    def cancel(self):
        event(self.directory, "cancel_started", child_pid=self.process.pid)
        if self.process.poll() is None:
            os.killpg(self.process.pid, signal.SIGTERM)
            try:
                self.process.wait(timeout=self.delay + 1)
            except subprocess.TimeoutExpired:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait(timeout=2)
        event(self.directory, "cancel_finished", child_pid=self.process.pid)
        if self.fail:
            raise RuntimeError("Fixture cleanup failed after child reaping")


def run_job(job, snapshot, options, deadline, active, check):
    directory = Path(job["directory"])
    event(directory, "worker_started", source_path=runner.__file__,
          source_sha256=hashlib.sha256(Path(runner.__file__).read_bytes()).hexdigest())
    item = OwnedChild(directory, job.get("cleanup_delay", .01),
                      job.get("cleanup_fail", False))
    active.append(item)
    time.sleep(.3)  # Allow the actual parent monitor to report established ownership.
    event(directory, "computation_finished")
    return {"job_id": job["job_id"], "kind": job["kind"],
            "records": [], "fixture_only": True}


def worker(connection, job, snapshot, options, budget):
    runner._run_job = run_job
    try:
        ORIGINAL_WORKER(connection, job, snapshot, options, budget)
    finally:
        event(job["directory"], "worker_function_finished")


def failing_after_delta_worker(connection, job, snapshot, options, budget):
    event(job["directory"], "worker_started")
    connection.send({"delta": {"job_id": job["job_id"], "kind": job["kind"],
                               "records": [], "fixture_only": True}})
    os._exit(7)


def plain_job(job, snapshot, options, deadline, active, check):
    event(job["directory"], "worker_started", source_path=runner.__file__,
          source_sha256=hashlib.sha256(Path(runner.__file__).read_bytes()).hexdigest())
    assert active == []
    return {"job_id": job["job_id"], "kind": job["kind"], "records": [],
            "fixture_only": True}


def delayed_exit_worker(connection, job, snapshot, options, budget):
    runner._run_job = plain_job
    ORIGINAL_WORKER(connection, job, snapshot, options, budget)
    event(job["directory"], "post_send_teardown_started")
    time.sleep(job.get("cleanup_delay", 3.2))
    event(job["directory"], "post_send_teardown_finished")


def finish_finalizer(directory, delay):
    event(directory, "finalizer_started")
    time.sleep(delay)
    event(directory, "finalizer_finished")


def delayed_finalizer_worker(connection, job, snapshot, options, budget):
    runner._run_job = plain_job
    multiprocessing.util.Finalize(None, finish_finalizer,
        args=(job["directory"], job.get("cleanup_delay", 3.2)), exitpriority=0)
    ORIGINAL_WORKER(connection, job, snapshot, options, budget)


_fixture_worker = worker

def job(directory, identifier="sieve-00", delay=.01, fail=False):
    return {"job_id": identifier, "kind": "sieve", "directory": str(directory),
            "candidates": [], "cleanup_delay": delay, "cleanup_fail": fail}


def dispatch(monkeypatch, jobs, stop=None, timeout=15, worker=None):
    monkeypatch.setattr(runner, "_job_worker", worker or _fixture_worker)
    return runner._dispatch_jobs(jobs, {}, runner._options(workers=2),
        stop or runner.GracefulDaemonInterrupt(), time.monotonic()+timeout, {})


def assert_reaped(directory, before):
    assert {p.pid for p in multiprocessing.active_children()} <= before
    for path in Path(directory).glob("**/child_ready"):
        pid = int(path.read_text())
        until = time.monotonic()+2
        while True:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            assert time.monotonic() < until, f"Owned child {pid} persisted after cleanup"
            time.sleep(.01)


def test_success_waits_for_owned_child_cleanup(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    result = dispatch(monkeypatch, [job(tmp_path / "slow", delay=3.2)])
    assert result == [{"job_id": "sieve-00", "kind": "sieve", "records": [],
                       "fixture_only": True}]
    assert_reaped(tmp_path, before)


def test_cleanup_failure_is_not_published_as_success(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    with pytest.raises(RuntimeError, match="Fixture cleanup failed"):
        dispatch(monkeypatch, [job(tmp_path / "failed", fail=True)])
    assert_reaped(tmp_path, before)


def test_actual_nonzero_exit_after_delta_remains_fatal(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    with pytest.raises(RuntimeError, match="failed after returning its delta.*exit=7"):
        dispatch(monkeypatch, [job(tmp_path)],
                 worker=failing_after_delta_worker)
    assert_reaped(tmp_path, before)


def test_cancellation_during_owned_cleanup_reaps_children(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    stop = runner.GracefulDaemonInterrupt()
    def request_stop():
        until = time.monotonic()+5
        path = tmp_path / "cancel" / "events.jsonl"
        while time.monotonic() < until:
            if path.exists() and "cancel_started" in path.read_text():
                stop.stop_requested = True
                return
            time.sleep(.01)
        stop.stop_requested = True
    thread = threading.Thread(target=request_stop)
    thread.start()
    started = time.monotonic()
    with pytest.raises(InterruptedError):
        dispatch(monkeypatch, [job(tmp_path / "cancel", delay=3.2)], stop)
    thread.join(timeout=5)
    assert time.monotonic()-started < 10
    assert_reaped(tmp_path, before)


def test_deadline_during_cleanup_never_returns_delta(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    with pytest.raises(InterruptedError):
        dispatch(monkeypatch, [job(tmp_path / "deadline", delay=3.2)], timeout=1)
    assert_reaped(tmp_path, before)


def test_healthy_companion_survives_slow_cleanup(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    result = dispatch(monkeypatch, [job(tmp_path / "slow", delay=3.2),
                                   job(tmp_path / "fast", "sieve-01")])
    assert [x["job_id"] for x in result] == ["sieve-00", "sieve-01"]
    assert_reaped(tmp_path, before)


def test_post_send_teardown_with_empty_active_list_exits_cleanly(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    result = dispatch(monkeypatch, [job(tmp_path, delay=3.2)],
                      worker=delayed_exit_worker)
    assert result[0]["fixture_only"]
    assert "post_send_teardown_finished" in (tmp_path / "events.jsonl").read_text()
    assert_reaped(tmp_path, before)


def test_real_python_finalizer_finishes_before_return(monkeypatch, tmp_path):
    before = {p.pid for p in multiprocessing.active_children()}
    dispatch(monkeypatch, [job(tmp_path, delay=3.2)],
             worker=delayed_finalizer_worker)
    assert "finalizer_finished" in (tmp_path / "events.jsonl").read_text()
    assert_reaped(tmp_path, before)


@pytest.mark.parametrize("cancel", [False, True])
def test_post_delta_exit_wait_respects_stop_and_deadline(monkeypatch, tmp_path, cancel):
    before = {p.pid for p in multiprocessing.active_children()}
    stop = runner.GracefulDaemonInterrupt()
    def request_stop():
        until = time.monotonic()+5
        while time.monotonic() < until:
            p = tmp_path / "events.jsonl"
            if p.exists() and "post_send_teardown_started" in p.read_text():
                stop.stop_requested = True
                return
            time.sleep(.01)
    thread = threading.Thread(target=request_stop) if cancel else None
    if thread:
        thread.start()
    started = time.monotonic()
    with pytest.raises(InterruptedError):
        dispatch(monkeypatch, [job(tmp_path, delay=8)], stop,
                 timeout=15 if cancel else 1,
                 worker=delayed_exit_worker)
    if thread:
        thread.join(timeout=5)
    assert time.monotonic()-started < 6
    assert_reaped(tmp_path, before)


