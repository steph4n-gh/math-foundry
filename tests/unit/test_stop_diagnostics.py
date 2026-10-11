"""Durable stop origins without model, Lean, or real process-control calls."""
import copy
import json
from pathlib import Path
import signal
import time
from types import SimpleNamespace

import pytest

import run_research as runner
import autonomous_math.novelty.review_worker as review
import autonomous_math.prover.replay_worker as replay

assert Path(runner.__file__).resolve() == Path(__file__).resolve().parents[2] / "run_research.py"


@pytest.fixture
def isolated_engine(monkeypatch, tmp_path):
    proof = {"id": "preserved", "status": "LEAN_CERTIFIED",
             "conjecture": {"exact": "unchanged AST"},
             "lean_proof": {"receipt_path": "preserved-exact-receipt"}}
    atlas = {"theorems": {"preserved": proof}, "total_iterations": 242,
             "total_lean_certified": 1, "total_refuted": 0}
    instances = []

    class Replay:
        def __init__(self, directory, **kwargs):
            self.state = {"state": "idle", "passed": 1, "failed": 0, "pending": 0}
            self.closed = False
            self.raise_pulse = None
            instances.append(self)
        def start(self):
            pass
        def pulse(self):
            if self.raise_pulse:
                raise self.raise_pulse
        def wake(self):
            pass
        def close(self):
            self.closed = True

    monkeypatch.setattr(replay, "ReplayWorker", Replay)
    monkeypatch.setattr(runner, "load_snapshot", lambda directory: copy.deepcopy(atlas))
    monkeypatch.setattr(runner.InstanceDatabase, "clear_cache", lambda: None)
    monkeypatch.setattr(runner.GracefulDaemonInterrupt, "install", lambda self: None)
    monkeypatch.setattr(runner.GracefulDaemonInterrupt, "uninstall", lambda self: None)
    monkeypatch.setattr(runner, "_refresh_novelty_reviews", lambda *args, **kwargs: None)
    monkeypatch.setattr(runner, "_commit_campaign_batch", lambda *args, **kwargs: None)

    def complete(preset, working, directory, pair_limit, triad_limit, lean_limit,
                 stop, deadline, status, **kwargs):
        return copy.deepcopy(working)
    monkeypatch.setattr(runner, "_bounded_batch", complete)

    def execute(**kwargs):
        options = dict(max_iterations=1, timeout_sec=None, pair_limit=0, triad_limit=0,
                       lean_limit=0, seed=7, workers=16, proof_backend="none",
                       model="gpt-6.1-sol", model_rounds=3,
                       model_request_timeout=1200, model_candidates=4,
                       reasoning_effort="xhigh")
        options.update(kwargs)
        return runner._execute(tmp_path, [{"campaign": "spectral"}], **options)
    return SimpleNamespace(execute=execute, instances=instances, proof=proof,
                           status=lambda: json.loads((tmp_path / "run_status.json").read_text()),
                           atlas=lambda: json.loads((tmp_path / "cumulative_discovery_atlas.json").read_text()))


@pytest.mark.parametrize("sig", [signal.SIGINT, signal.SIGTERM])
def test_signal_details_preserve_first_received_signal(monkeypatch, sig):
    monkeypatch.setattr(runner, "time", SimpleNamespace(time=lambda: 1234.5))
    stop = runner.GracefulDaemonInterrupt()
    stop._handler(sig, None)
    assert stop.stop_requested
    assert stop.stop_signal == {"number": int(sig), "name": signal.Signals(sig).name,
                                "received_at": 1234.5}
    stop._handler(signal.SIGTERM if sig == signal.SIGINT else signal.SIGINT, None)
    assert stop.stop_signal["number"] == int(sig)


@pytest.mark.parametrize("origin", ["requested_stop", "batch_deadline"])
def test_batch_check_still_interrupts_with_finite_deadline(origin):
    stop = runner.GracefulDaemonInterrupt()
    stop.stop_requested = origin == "requested_stop"
    deadline = time.monotonic() + (30 if stop.stop_requested else -1)
    with pytest.raises(InterruptedError, match="Research stopped before batch commit") as caught:
        runner._check_batch_stop(stop, deadline)
    assert caught.value.stop_origin == origin
    # A healthy batch remains admitted under the same finite deadline.
    runner._check_batch_stop(runner.GracefulDaemonInterrupt(), time.monotonic() + 30)


@pytest.mark.parametrize("sig", [signal.SIGINT, signal.SIGTERM])
def test_signal_interruption_survives_final_status_and_preserves_proof(isolated_engine, monkeypatch, sig):
    def interrupted(preset, atlas, directory, pair_limit, triad_limit, lean_limit,
                    stop, deadline, status, **kwargs):
        status["stage"] = "proof"
        status["active_batch"] = {"checkpoint": 243, "state": "running"}
        stop._handler(sig, None)
        runner._check_batch_stop(stop, deadline)
    monkeypatch.setattr(runner, "_bounded_batch", interrupted)
    isolated_engine.execute()
    status = isolated_engine.status()
    assert status["state"] == "stopped" and status["stage"] == "complete"
    assert status["stop_origin"] == "signal"
    assert status["stop_signal"]["number"] == int(sig)
    assert status["stop_signal"]["name"] == signal.Signals(sig).name
    assert isinstance(status["stop_signal"]["received_at"], (int, float))
    assert status["interruption_reason"] == "Research stopped before batch commit"
    assert status["interrupted_stage"] == "proof"
    assert status["active_batch"]["state"] == "interrupted"
    assert status["committed_iteration"] == 242
    assert isolated_engine.atlas()["theorems"]["preserved"] == isolated_engine.proof
    assert isolated_engine.instances[0].closed


def test_unexplained_interruption_keeps_exact_reason_and_remains_unattributed(isolated_engine, monkeypatch):
    def interrupted(*args, **kwargs):
        raise InterruptedError("Exact diagnostic from an otherwise unknown caller")
    monkeypatch.setattr(runner, "_bounded_batch", interrupted)
    isolated_engine.execute()
    status = isolated_engine.status()
    assert status["stop_origin"] == "batch_interruption"
    assert status["interruption_reason"] == "Exact diagnostic from an otherwise unknown caller"
    assert "stop_signal" not in status
    assert status["committed_iteration"] == 242


def test_untyped_interruption_with_recorded_signal_keeps_both_signal_and_exact_reason(isolated_engine, monkeypatch):
    def interrupted(preset, atlas, directory, pair_limit, triad_limit, lean_limit,
                    stop, deadline, status, **kwargs):
        stop._handler(signal.SIGTERM, None)
        raise InterruptedError("Exact cancellation from a different stop gate")
    monkeypatch.setattr(runner, "_bounded_batch", interrupted)
    isolated_engine.execute()
    status = isolated_engine.status()
    assert status["stop_origin"] == "signal"
    assert status["stop_signal"]["name"] == "SIGTERM"
    assert status["interruption_reason"] == "Exact cancellation from a different stop gate"


def test_late_signal_metadata_does_not_erase_preceding_heartbeat_failure():
    stop = runner.GracefulDaemonInterrupt()
    stop._handler(signal.SIGTERM, None)
    status = {"stop_origin": "heartbeat_error", "stop_reason": "Exact write failure"}
    runner._record_stop_diagnostics(status, stop)
    assert status["stop_signal"]["name"] == "SIGTERM"
    assert status["stop_origin"] == "heartbeat_error"
    assert status["stop_reason"] == "Exact write failure"


def test_batch_deadline_is_distinct_from_explicit_stop(isolated_engine, monkeypatch):
    def exhausted(preset, atlas, directory, pair_limit, triad_limit, lean_limit,
                  stop, deadline, status, **kwargs):
        runner._check_batch_stop(stop, time.monotonic() - 1)
    monkeypatch.setattr(runner, "_bounded_batch", exhausted)
    isolated_engine.execute()
    status = isolated_engine.status()
    assert status["stop_origin"] == "batch_deadline"
    assert status["state"] == "stopped" and status["committed_iteration"] == 242
    assert "stop_signal" not in status


def test_checkpoint_marker_stops_before_admitting_batch(isolated_engine, monkeypatch, tmp_path):
    (tmp_path / "stop_after_checkpoint.json").write_text("{}")
    def forbidden(*args, **kwargs):
        pytest.fail("Boundary marker must prevent admitting a new batch")
    monkeypatch.setattr(runner, "_bounded_batch", forbidden)
    isolated_engine.execute(max_iterations=None)
    status = isolated_engine.status()
    assert status["stop_origin"] == "checkpoint_boundary"
    assert status["stop_reason"] == "Requested stop at committed checkpoint boundary"
    assert status["committed_iteration"] == 242
    assert (tmp_path / "stop_after_checkpoint.json").exists()
    assert isolated_engine.atlas()["theorems"]["preserved"] == isolated_engine.proof


@pytest.mark.parametrize("limit,expected", [(0, 242), (1, 243)])
def test_iteration_limit_persisted_after_zero_or_one_completed_batches(isolated_engine, limit, expected):
    isolated_engine.execute(max_iterations=limit)
    status = isolated_engine.status()
    assert status["stop_origin"] == "iteration_limit"
    assert status["committed_iteration"] == expected
    assert isolated_engine.atlas()["theorems"]["preserved"] == isolated_engine.proof


def test_outer_deadline_still_stops_before_new_batch(isolated_engine, monkeypatch):
    clock = iter([100.0, 102.0])
    monkeypatch.setattr(runner, "time", SimpleNamespace(time=time.time, monotonic=lambda: next(clock)))
    def forbidden(*args, **kwargs):
        pytest.fail("Expired outer deadline must prevent admitting a batch")
    monkeypatch.setattr(runner, "_bounded_batch", forbidden)
    isolated_engine.execute(max_iterations=None, timeout_sec=1)
    status = isolated_engine.status()
    assert status["stop_origin"] == "outer_deadline"
    assert status["state"] == "stopped" and status["committed_iteration"] == 242


def test_heartbeat_failure_is_durable_failed_state_not_clean_interruption(isolated_engine, monkeypatch):
    def fail_start(self):
        self.raise_pulse = RuntimeError("Retained replay pulse failure")
    monkeypatch.setattr(replay.ReplayWorker, "start", fail_start)
    # Execute the failing heartbeat synchronously so failure order is deterministic.
    class Thread:
        def __init__(self, target, **kwargs):
            self.target = target
        def start(self):
            self.target()
        def join(self, **kwargs):
            pass
        def is_alive(self):
            return False
    monkeypatch.setattr(runner.threading, "Thread", Thread)
    with pytest.raises(RuntimeError, match="Retained replay pulse failure"):
        isolated_engine.execute(max_iterations=None)
    status = isolated_engine.status()
    assert status["state"] == "failed"
    assert status["stop_origin"] == "heartbeat_error"
    assert status["stop_reason"] == status["error"] == "Retained replay pulse failure"
    assert status["committed_iteration"] == 242
    assert isolated_engine.instances[0].closed


def test_malformed_batch_failure_is_not_relabelled_as_stop(isolated_engine, monkeypatch):
    def malformed(*args, **kwargs):
        raise ValueError("Invalid assigned evidence")
    monkeypatch.setattr(runner, "_bounded_batch", malformed)
    with pytest.raises(ValueError, match="Invalid assigned evidence"):
        isolated_engine.execute()
    status = isolated_engine.status()
    assert status["state"] == "failed" and status["stop_origin"] == "failure"
    assert status["error"] == "Invalid assigned evidence"
    assert "interruption_reason" not in status
    assert status["committed_iteration"] == 242


@pytest.fixture
def failing_reviewer(isolated_engine, monkeypatch):
    class Review:
        def __init__(self, directory, synthesizer, **kwargs):
            pass
        def start(self):
            pass
        def pulse(self):
            pass
        def wake(self):
            pass
        def close(self):
            raise RuntimeError("Originality reviewer still owns a live request")
    monkeypatch.setattr(review, "ReviewWorker", Review)
    monkeypatch.setattr(runner, "_synthesizer", lambda options: SimpleNamespace(configuration=lambda: {
        "model_override": "gpt-6.1-sol", "reasoning_effort": "xhigh"}))


def test_reviewer_close_failure_is_durable_failed_shutdown(isolated_engine, failing_reviewer):
    with pytest.raises(RuntimeError, match="Originality reviewer still owns a live request"):
        isolated_engine.execute(proof_backend="codex", max_iterations=0)
    status = isolated_engine.status()
    assert status["state"] == "failed" and status["stage"] == "shutdown"
    assert status["shutdown_errors"] == [{"worker": "originality_review",
        "error": "Originality reviewer still owns a live request"}]
    assert status["error"] == "Originality reviewer still owns a live request"
    assert isolated_engine.instances[0].closed
    assert status["committed_iteration"] == 242
    assert isolated_engine.atlas()["theorems"]["preserved"] == isolated_engine.proof


def test_reviewer_close_failure_preserves_original_body_failure(isolated_engine, failing_reviewer, monkeypatch):
    def malformed(*args, **kwargs):
        raise ValueError("Original invalid proof evidence")
    monkeypatch.setattr(runner, "_bounded_batch", malformed)
    with pytest.raises(ValueError, match="Original invalid proof evidence"):
        isolated_engine.execute(proof_backend="codex")
    status = isolated_engine.status()
    assert status["state"] == "failed" and status["stop_origin"] == "failure"
    assert status["error"] == "Original invalid proof evidence"
    assert status["shutdown_errors"][0]["error"] == "Originality reviewer still owns a live request"
    assert isolated_engine.instances[0].closed
    assert status["committed_iteration"] == 242


def test_both_close_failures_are_retained_with_first_error(isolated_engine, failing_reviewer, monkeypatch):
    def broken_close(self):
        raise RuntimeError("Independent replay still owns a compiler")
    monkeypatch.setattr(replay.ReplayWorker, "close", broken_close)
    with pytest.raises(RuntimeError, match="Independent replay still owns a compiler"):
        isolated_engine.execute(proof_backend="codex", max_iterations=0)
    status = isolated_engine.status()
    assert status["state"] == "failed" and status["stage"] == "shutdown"
    assert status["error"] == "Independent replay still owns a compiler"
    assert status["shutdown_errors"] == [
        {"worker": "independent_replay", "error": "Independent replay still owns a compiler"},
        {"worker": "originality_review", "error": "Originality reviewer still owns a live request"}]


def test_still_alive_heartbeat_cannot_report_clean_shutdown(isolated_engine, monkeypatch):
    joins = []
    class Thread:
        def __init__(self, target, **kwargs):
            pass
        def start(self):
            pass
        def join(self, *, timeout):
            joins.append(timeout)
        def is_alive(self):
            return True
    monkeypatch.setattr(runner.threading, "Thread", Thread)
    with pytest.raises(RuntimeError, match="Research heartbeat did not stop before shutdown deadline"):
        isolated_engine.execute(max_iterations=0)
    status = isolated_engine.status()
    assert joins == [5]
    assert status["state"] == "failed" and status["stage"] == "shutdown"
    assert status["shutdown_errors"] == [{"worker": "research_heartbeat",
        "error": "Research heartbeat did not stop before shutdown deadline"}]
    assert status["error"] == "Research heartbeat did not stop before shutdown deadline"
    assert status["committed_iteration"] == 242
    assert isolated_engine.atlas()["theorems"]["preserved"] == isolated_engine.proof
    assert isolated_engine.instances[0].closed
