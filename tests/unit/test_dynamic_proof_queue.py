"""Real spawned slots refill without changing admission or atomic knowledge state."""
import copy
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

import pytest

import run_research as runner
from autonomous_math.prover.lean_prover import LeanVerificationResult
from tests.unit.test_parallel_research import claim, empty_atlas, fake_engine, normalized


_original_worker = runner._job_worker


def _wait_until(predicate, seconds=20):
    until = time.monotonic()+seconds
    while time.monotonic() < until:
        if predicate():
            return
        time.sleep(0.02)
    raise AssertionError("Timed out waiting for controlled process state")


class _OwnedChild:
    def __init__(self, marker):
        self.process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"],
                                        start_new_session=True)
        marker.write_text(str(self.process.pid))

    def active_process_groups(self):
        return [self.process.pid] if self.process.poll() is None else []

    def cancel(self):
        from autonomous_math.prover.codex_synthesis import terminate_process_group
        terminate_process_group(self.process)


class _FailedCleanupChild(_OwnedChild):
    def cancel(self):
        raise RuntimeError("Controlled worker cleanup failure")


def _controlled_job(job, snapshot, options, deadline, active, check):
    """Controlled mathematics, real production worker lifecycle and process groups."""
    root = Path(options["fixture_root"])
    marker = root / job["job_id"]
    marker.with_suffix(".started").write_text(json.dumps({"pid": os.getpid(), "at": time.monotonic()}))
    if job["kind"] == "planning":
        from autonomous_math.sieve.adversarial_holdouts import HOLDOUT_REVISION
        runner.random.setstate(job["rng_state"])
        runner.random.random()  # The plan advances RNG; a cancelled batch must roll it back.
        result = {"job_id": job["job_id"], "kind": "planning", "records": [],
                  "candidates": options["fixture_candidates"], "holdout_revision": HOLDOUT_REVISION,
                  "catalog_graphs": 0, "catalog_graph_hashes": [], "invariants_tracked": 0,
                  "replayed_boundary_graphs": 0, "random_state": runner.random.getstate()}
    else:
        if job["kind"] == "proof":
            if job["job_id"] in options.get("fixture_failed_cleanup", []):
                active.append(_FailedCleanupChild(marker.with_suffix(".child")))
                time.sleep(0.4)  # Let the real worker report the owned process group.
            if job["job_id"] in options.get("fixture_hang", []):
                child = _OwnedChild(marker.with_suffix(".child"))
                active.append(child)
                child.process.wait()
            wait_for = options.get("fixture_wait_for", {}).get(job["job_id"])
            if wait_for:
                _wait_until(lambda: (root / wait_for).exists())
            time.sleep(options.get("fixture_delays", {}).get(job["job_id"], 0.02))
        records = []
        fingerprint = hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest()
        for candidate in job["candidates"]:
            check()
            if job["kind"] == "sieve":
                record = {"id": candidate["id"], "statement": candidate["statement"],
                          "conjecture": candidate, "status": "EMPIRICAL_SURVIVOR"}
            else:
                result = LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                    theorem_name=candidate["id"], conjecture_id=candidate["id"], attempts_count=1,
                    diagnostics=[{"exit_code": 1, "fixture_snapshot": fingerprint}])
                record = {"id": candidate["id"], "conjecture": candidate,
                          "proof_search_key": job["search_keys"][candidate["id"]],
                          "proof_attempt": result.to_dict()}
            records.append(record)
        result = {"job_id": job["job_id"], "kind": job["kind"], "records": records}
    marker.with_suffix(".finished").write_text(json.dumps({"at": time.monotonic()}))
    return result


def _fixture_worker(connection, job, snapshot, options, budget):
    # Spawn imports this module afresh. The lifecycle remains the actual worker,
    # including parent monitoring, SIGTERM handling and owned-child cleanup.
    root = Path(options["fixture_root"])
    (root / (job["job_id"]+".boot")).write_text(str(os.getpid()))
    time.sleep(options.get("fixture_boot_delay", 0))
    runner._run_job = _controlled_job
    _original_worker(connection, job, snapshot, options, budget)


def _jobs(directory, count=3):
    candidates = [claim(f"target_{index}", -index) for index in range(count)]
    return runner._jobs("proof", candidates, directory, 2,
                        {candidate.id: "frozen-context" for candidate in candidates})


def _running(pid):
    state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)],
                           capture_output=True, text=True).stdout.strip()
    return bool(state) and state[0] not in "ZE"


@pytest.mark.parametrize("workers,count", [(2, 3), (8, 16), (16, 17)])
def test_spawn_straggler_refills_idle_slot_with_frozen_snapshot(monkeypatch, tmp_path, workers, count):
    monkeypatch.setattr(runner, "_job_worker", _fixture_worker)
    jobs = _jobs(tmp_path / "jobs", count)
    assert len(jobs) == count and all(len(job["candidates"]) == 1 for job in jobs)
    snapshot = runner._snapshot(empty_atlas())
    before = copy.deepcopy(snapshot)
    queued_id = f"proof-{workers:02d}"
    options = dict(runner._options(workers=workers), fixture_root=str(tmp_path),
                   fixture_wait_for={"proof-00": queued_id+".started"})
    timing = {}
    results = runner._dispatch_jobs(jobs, snapshot, options, runner.GracefulDaemonInterrupt(),
                                    time.monotonic()+30, {}, timing=timing)
    assert [result["job_id"] for result in results] == [f"proof-{index:02d}" for index in range(count)]
    assert snapshot == before
    assert (tmp_path / (queued_id+".started")).exists()
    queued_start = json.loads((tmp_path / (queued_id+".started")).read_text())["at"]
    slow_end = json.loads((tmp_path / "proof-00.finished").read_text())["at"]
    assert queued_start < slow_end  # The straggler cannot finish until its queued sibling starts.
    spans = timing["job_timings"]
    first_free = min(spans[f"proof-{index:02d}"]["finished_sec"] for index in range(1, workers))
    assert spans[queued_id]["started_sec"] >= first_free
    # Spawn startup varies across hosts; refill must precede straggler completion.
    assert spans[queued_id]["started_sec"] < spans["proof-00"]["finished_sec"]
    assert timing["max_active_workers"] == timing["slots"] == workers
    assert timing["jobs_started"] == timing["jobs_completed"] == count
    assert timing["busy_sec"]+timing["idle_sec"] == pytest.approx(workers*timing["elapsed_sec"])
    fingerprints = {r["records"][0]["proof_attempt"]["diagnostics"][0]["fixture_snapshot"] for r in results}
    assert fingerprints == {hashlib.sha256(json.dumps(before, sort_keys=True).encode()).hexdigest()}


@pytest.mark.skipif(not hasattr(os, "killpg"), reason="Owned Unix process-group cleanup")
def test_failed_cleanup_rejects_delta_kills_reported_child_and_keeps_pending(monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "_job_worker", _fixture_worker)
    options = dict(runner._options(workers=1), fixture_root=str(tmp_path),
                   fixture_failed_cleanup=["proof-00"])
    with pytest.raises(RuntimeError, match="Controlled worker cleanup failure"):
        runner._dispatch_jobs(_jobs(tmp_path / "jobs", 2), runner._snapshot(empty_atlas()), options,
                              runner.GracefulDaemonInterrupt(), time.monotonic()+20, {})
    assert not (tmp_path / "proof-01.started").exists()
    child = int((tmp_path / "proof-00.child").read_text())
    _wait_until(lambda: not _running(child), seconds=5)


def test_spawn_queue_preserves_global_cap_results_and_rng(fake_engine, monkeypatch, tmp_path):
    monkeypatch.setattr(runner, "_job_worker", _fixture_worker)
    candidates = [claim(f"target_{index}", -index) for index in range(5)]
    results = []
    initial_rng = runner.random.getstate()
    dispatch, observed_deadlines = runner._dispatch_jobs, []
    def observe_deadline(*args, **kwargs):
        observed_deadlines.append(args[4])
        return dispatch(*args, **kwargs)
    monkeypatch.setattr(runner, "_dispatch_jobs", observe_deadline)
    for workers in (1, 2, 8):
        directory = tmp_path / str(workers)
        directory.mkdir()
        runner.random.setstate(initial_rng)
        observed_deadlines.clear()
        started = time.monotonic()
        options = dict(runner._options(workers=workers), fixture_root=str(directory),
                       fixture_candidates=[candidate.to_dict() for candidate in candidates])
        result = runner._bounded_batch({"pairs": [], "triads": []}, empty_atlas(), directory,
            0, 0, 3, runner.GracefulDaemonInterrupt(), time.monotonic()+300, {},
            options=options)
        results.append(result)
        assert result["batch_metrics"]["proof_targets"] == result["batch_metrics"]["proof_jobs"] == 3
        assert result["batch_metrics"]["proof_deferred"] == 2
        assert result["proof_schedule_sequence"] == 3
        assert sum("proof_attempt" in r for r in result["theorems"].values()) == 3
        assert result["batch_metrics"]["worker_timing"]["proof"]["max_active_workers"] <= workers
        # Waves depend on admitted targets and configured capacity, even when
        # the target cap leaves most of eight configured slots unused.
        waves = (3+workers-1)//workers
        expected_budget = 60+waves*runner._proof_budget(options)
        assert all(deadline-started == pytest.approx(expected_budget, abs=0.1) for deadline in observed_deadlines)
        assert not (directory / "proof-03.started").exists()
    assert all(normalized(result) == normalized(results[0]) for result in results[1:])
    assert results[0]["random_state"] != initial_rng
    runner.random.setstate(initial_rng)


def test_proposal_dispatch_keeps_committed_iteration_and_all_refutations(fake_engine, monkeypatch, tmp_path):
    captured = []
    def dispatch(jobs, snapshot, options, stop, deadline, status, synchronous=False, timing=None):
        if jobs and jobs[0]["kind"] == "proposal":
            captured.append(copy.deepcopy(jobs[0]["context"]))
            return [{"job_id": jobs[0]["job_id"], "kind": "proposal", "candidates": [],
                     "trace": {"status": "COMPLETED"}}]
        return [_controlled_job(job, snapshot, options, deadline, [], lambda: None) for job in jobs]
    monkeypatch.setattr(runner, "_dispatch_jobs", dispatch)
    atlas = empty_atlas()
    atlas["total_iterations"] = 19
    atlas["recent_refutations"] = [{"id": f"recorded_refutation_{index}"} for index in range(12)]
    before, initial_rng = copy.deepcopy(atlas), runner.random.getstate()
    try:
        runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, 0,
            runner.GracefulDaemonInterrupt(), time.monotonic()+30, {},
            options=dict(runner._options(workers=2, proof_backend="codex", model_candidates=2),
                         fixture_root=str(tmp_path), fixture_candidates=[]))
    finally:
        runner.random.setstate(initial_rng)
    assert len(captured) == 1
    assert captured[0]["total_iterations"] == 19
    assert captured[0]["recent_refutations"] == before["recent_refutations"]
    assert atlas == before


@pytest.mark.skipif(not hasattr(os, "killpg"), reason="Owned Unix process-group cancellation")
@pytest.mark.parametrize("workers", [2, 8])
def test_cancel_discards_completed_delta_and_pending_target_then_resumes(fake_engine, monkeypatch, tmp_path, workers):
    monkeypatch.setattr(runner, "_job_worker", _fixture_worker)
    count = workers+2
    candidates = [claim(f"target_{index}", -index) for index in range(count)]
    atlas = empty_atlas()
    checkpoint = tmp_path / "cumulative_discovery_atlas.json"
    runner.atomic_save_json(atlas, checkpoint)
    before = checkpoint.read_bytes()
    initial_rng = runner.random.getstate()
    stop, status, interrupted = runner.GracefulDaemonInterrupt(), {}, threading.Event()
    options = dict(runner._options(workers=workers), fixture_root=str(tmp_path),
                   fixture_candidates=[candidate.to_dict() for candidate in candidates],
                   fixture_hang=[f"proof-{index:02d}" for index in range(1, workers+1)])
    def interrupt_active_refill():
        _wait_until(lambda: (tmp_path / f"proof-{workers:02d}.child").exists())
        stop.stop_requested = True
        interrupted.set()
    thread = threading.Thread(target=interrupt_active_refill)
    thread.start()
    try:
        with pytest.raises(InterruptedError):
            runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, count,
                stop, time.monotonic()+60, status, options=options)
    finally:
        thread.join(timeout=25)
    assert (tmp_path / "proof-00.finished").exists()  # A delta arrived before cancellation.
    assert interrupted.is_set()
    assert not (tmp_path / f"proof-{workers+1:02d}.started").exists()
    assert atlas == empty_atlas() and checkpoint.read_bytes() == before
    assert runner.random.getstate() == initial_rng
    for marker in tmp_path.glob("proof-*.child"):
        assert not _running(int(marker.read_text()))
    resumed_root = tmp_path / "resume"
    resumed_root.mkdir()
    resumed = runner._bounded_batch({"pairs": [], "triads": []}, runner.load_snapshot(tmp_path),
        tmp_path, 0, 0, count, runner.GracefulDaemonInterrupt(), time.monotonic()+60, {},
        options=dict(options, fixture_hang=[], fixture_root=str(resumed_root)))
    assert resumed["proof_schedule_sequence"] == resumed["batch_metrics"]["proof_targets"] == count
    assert len(resumed["theorems"]) == count
    runner.random.setstate(initial_rng)


@pytest.mark.skipif(not hasattr(os, "killpg"), reason="Owned Unix parent-death cleanup")
@pytest.mark.parametrize("worker_count,boot_delay", [(2, 0), (2, 2), (8, 0), (8, 5)])
def test_parent_death_stops_active_workers_and_never_starts_pending(tmp_path, worker_count, boot_delay):
    script = """
import sys, time
from pathlib import Path
import run_research as runner
from tests.unit.test_dynamic_proof_queue import _fixture_worker, _jobs, empty_atlas
root=Path(sys.argv[1])
workers=int(sys.argv[3])
runner._job_worker=_fixture_worker
options=dict(runner._options(workers=workers), fixture_root=str(root),
             fixture_hang=[f'proof-{index:02d}' for index in range(workers)], fixture_boot_delay=float(sys.argv[2]))
runner._dispatch_jobs(_jobs(root/'jobs', workers+1), runner._snapshot(empty_atlas()), options,
                      runner.GracefulDaemonInterrupt(), time.monotonic()+40, {})
"""
    parent = subprocess.Popen([sys.executable, "-c", script, str(tmp_path), str(boot_delay), str(worker_count)],
                              cwd=runner.REPO_ROOT, start_new_session=True)
    suffix = ".boot" if boot_delay else ".child"
    try:
        _wait_until(lambda: all((tmp_path / (f"proof-{index:02d}"+suffix)).exists() for index in range(worker_count)))
        parent.kill()
        parent.wait(timeout=5)
        worker_pids = [int(marker.read_text()) for marker in tmp_path.glob("proof-*.boot")]
        children = [int(marker.read_text()) for marker in tmp_path.glob("proof-*.child")]
        _wait_until(lambda: all(not _running(pid) for pid in worker_pids+children), seconds=10)
        assert not (tmp_path / f"proof-{worker_count:02d}.boot").exists()
        if boot_delay:
            assert not list(tmp_path.glob("proof-*.started"))
    finally:
        if parent.poll() is None:
            parent.kill()
            parent.wait(timeout=5)
        for marker in list(tmp_path.glob("proof-*.boot"))+list(tmp_path.glob("proof-*.child")):
            pid = int(marker.read_text())
            if _running(pid):
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
