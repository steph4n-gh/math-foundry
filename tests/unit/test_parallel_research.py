"""Parallel rounds preserve one committed knowledge state and bounded proof work."""
import copy
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import subprocess
import sys
import time
from types import SimpleNamespace

import networkx as nx
import pytest

import run_research as runner
from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.prover.lean_prover import LeanVerificationResult
from autonomous_math.sieve.certificates import CounterexampleCertificate, SieveResult


def claim(identifier, value=0, invariant="order", guard=None):
    return Conjecture.create(id=identifier, lhs=InvariantNode(invariant), rel=">=",
                             rhs=ConstantNode(value), guard=guard)


def empty_atlas():
    return {"theorems": {}, "total_iterations": 0, "total_conjectures_generated": 0,
            "total_refuted": 0, "recent_refutations": []}


@pytest.fixture
def fake_engine(monkeypatch):
    class Database:
        _cached_gi, _cached_matrix = [], {}
        calls = 0
        @classmethod
        def clear_cache(cls):
            pass
        def sieve_conjecture(self, candidate):
            type(self).calls += 1
            return SieveResult(status="SURVIVED", conjecture=candidate,
                               tested_instances_count=1, checked_instances_count=1)
    class Search:
        calls, context = [], "first"
        def __init__(self, **kwargs):
            self.toolchain = SimpleNamespace(ensure_workspace_built=lambda: True)
        def is_available(self):
            return True
        def search_key(self, candidate):
            return type(self).context + runner._candidate_key(candidate)
        def prove_conjecture(self, candidate, **kwargs):
            type(self).calls.append(candidate.id)
            return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
                theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=1,
                diagnostics=[{"exit_code": 1}])
    monkeypatch.setattr(runner, "InstanceDatabase", Database)
    monkeypatch.setattr(runner, "LeanProofSearch", Search)
    monkeypatch.setattr(runner, "independent_holdout", lambda c, check: SieveResult(
        status="SURVIVED", conjecture=c, tested_instances_count=1, checked_instances_count=1))
    return Database, Search


def synchronous(candidates, atlas, directory, lean_limit=0, screening_key="unchanged"):
    database = runner.InstanceDatabase()
    if screening_key != "unchanged":
        # A requested fake catalog revision must also reach the worker. The
        # coordinator binds caching to membership reported by that worker.
        type(database)._cached_gi = [SimpleNamespace(canonical_hash=hashlib.sha256(
            screening_key.encode()).hexdigest())]
    key = runner._screening_key([graph.canonical_hash for graph in database._cached_gi])
    return runner._coordinate_candidates(candidates, atlas, directory, lean_limit,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {},
        dict(runner._options(workers=2), replay_boundary=False),
        synchronous=True, screen_key=key)


def test_global_dedup_ignores_id_and_metadata_across_rounds(fake_engine, tmp_path):
    database, _ = fake_engine
    first = claim("first")
    alias = first.model_copy(update={"id": "another_label", "metadata": {"explanation": "same mathematics"}})
    atlas = empty_atlas()
    synchronous([first, alias], atlas, tmp_path)
    assert atlas["total_conjectures_generated"] == 1
    assert set(atlas["theorems"]) == {"first"}
    atlas["total_iterations"] = 1
    synchronous([alias], atlas, tmp_path)
    assert database.calls == 1
    assert atlas["total_conjectures_generated"] == 1
    synchronous([], atlas, tmp_path, screening_key="new-catalog")
    assert database.calls == 2  # A survivor is challenged even if not regenerated.
    assert atlas["theorems"]["first"]["discovered_iteration"] == 1


def test_worker_catalog_membership_overrides_stale_planner_cache_key(fake_engine, tmp_path):
    database, _ = fake_engine
    candidate, atlas = claim("probe"), empty_atlas()
    options = dict(runner._options(workers=2), replay_boundary=False)
    runner._coordinate_candidates([candidate], atlas, tmp_path, 0,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options,
        synchronous=True, screen_key="planner-catalog-that-was-not-admitted")
    admitted_key = runner._screening_key([])
    assert atlas["theorems"][candidate.id]["screening_key"] == admitted_key
    assert atlas["theorems"][candidate.id]["screening_key"] != "planner-catalog-that-was-not-admitted"
    synchronous([candidate], atlas, tmp_path)
    assert database.calls == 1
    synchronous([candidate], atlas, tmp_path, screening_key="new-worker-catalog")
    changed_key = runner._screening_key([graph.canonical_hash for graph in database._cached_gi])
    assert changed_key != admitted_key
    assert atlas["theorems"][candidate.id]["screening_key"] == changed_key
    assert database.calls == 2


def test_global_proof_budget_and_context_retry(fake_engine, tmp_path):
    _, search = fake_engine
    candidates = [claim("supported_a"), claim("supported_b", -1), claim("supported_c", -2),
                  claim("unsupported", invariant="diameter")]
    atlas = empty_atlas()
    synchronous(candidates, atlas, tmp_path, lean_limit=2)
    assert search.calls == ["supported_a", "supported_b"]
    assert atlas["batch_metrics"]["proof_targets"] == 2
    assert atlas["theorems"]["unsupported"]["proof_attempt"]["attempts_count"] == 0
    synchronous(candidates, atlas, tmp_path, lean_limit=2)
    assert search.calls == ["supported_a", "supported_b", "supported_c"]
    assert atlas["theorems"]["unsupported"]["proof_search_skipped"]
    search.context = "new-reuse-or-model-context"
    synchronous(candidates, atlas, tmp_path, lean_limit=2)
    assert search.calls[-2:] == ["supported_a", "supported_b"]


@pytest.mark.parametrize("failure", ["lean_timeout", "model_timeout", "transient_service"])
def test_retry_schedule_gives_waiting_targets_a_turn_after_resume(fake_engine, monkeypatch, tmp_path, failure):
    _, search = fake_engine
    def unresolved(self, candidate, **kwargs):
        search.calls.append(candidate.id)
        diagnostics = [{"exit_code": 124}] if failure == "lean_timeout" else []
        synthesis = [] if failure == "lean_timeout" else [{
            "status": "TIMEOUT" if failure == "model_timeout" else "FAILED"}]
        return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
            theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=1,
            diagnostics=diagnostics, synthesis_attempts=synthesis)
    monkeypatch.setattr(search, "prove_conjecture", unresolved)
    clock = [time.time()]
    monkeypatch.setattr(runner.time, "time", lambda: clock[0])
    candidates, atlas = [claim("A"), claim("B", -1), claim("C", -2)], empty_atlas()
    synchronous(candidates, atlas, tmp_path, lean_limit=2)
    assert search.calls == ["A", "B"]
    # Reload the exact checkpoint, including retry delays and persistent ordering.
    clock[0] += 301
    atlas["total_iterations"] = 2
    runner.atomic_save_json(atlas, tmp_path / "cumulative_discovery_atlas.json")
    atlas = runner.load_snapshot(tmp_path)
    synchronous(candidates, atlas, tmp_path, lean_limit=2, screening_key="new-catalog")
    assert search.calls[2:] == ["C", "A"]
    clock[0] += 601
    atlas["total_iterations"] = 6
    synchronous(candidates, atlas, tmp_path, lean_limit=2)
    assert search.calls[4:] == ["B", "C"]
    assert atlas["proof_schedule_sequence"] == 6
    assert {key: value["last_proof_attempt_sequence"] for key, value in atlas["theorems"].items()} == {
        "A": 4, "B": 5, "C": 6}


def test_lossless_constants_keep_distinct_verdicts_and_identities_after_resume(tmp_path):
    order = InvariantNode("order")
    loose, tight = [Conjecture.create(id=name, lhs=order, rel="<=",
        rhs=BinaryOpNode("*", ConstantNode(value), order))
        for name, value in (("loose", 1.0000001), ("tight", 0.9999999))]
    assert runner._candidate_key(loose) != runner._candidate_key(tight)
    assert loose.evaluate(nx.empty_graph(32), invariants={"order": 32})[0]
    assert not tight.evaluate(nx.empty_graph(32), invariants={"order": 32})[0]
    atlas = empty_atlas()
    options = dict(runner._options(), replay_boundary=False)
    runner._coordinate_candidates([loose, tight], atlas, tmp_path, 0,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options, synchronous=True)
    assert atlas["theorems"]["loose"]["status"] == "EMPIRICAL_SURVIVOR"
    assert atlas["theorems"]["tight"]["status"] == "REFUTED"
    assert atlas["total_conjectures_generated"] == 2
    runner.atomic_save_json(atlas, tmp_path / "cumulative_discovery_atlas.json")
    resumed = runner.load_snapshot(tmp_path)
    runner._coordinate_candidates([loose, tight], resumed, tmp_path, 0,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options, synchronous=True)
    assert resumed["total_conjectures_generated"] == 2
    assert resumed["theorems"]["loose"]["conjecture"] == loose.to_dict()
    assert resumed["theorems"]["tight"]["conjecture"] == tight.to_dict()


def test_identity_migration_invalidates_only_uncertified_caches():
    atlas = empty_atlas()
    cache = {"proof_search_key": "legacy-lossy-key", "screening_key": "legacy-screen",
             "proof_search_skipped": True, "next_retry_at": time.time()+60}
    for identifier, status in (("unresolved", "EMPIRICAL_SURVIVOR"),
                               ("certified", "LEAN_CERTIFIED"), ("refuted", "REFUTED")):
        atlas["theorems"][identifier] = {"id": identifier, "status": status,
            "conjecture": claim(identifier).to_dict(), **cache,
            "proof_attempt": {"status": "UNRESOLVED", "diagnostics": [{"exit_code": 124}]},
            "last_proof_attempt_sequence": 42,
            "lean_proof": {"receipt_path": "retained-receipt"} if status == "LEAN_CERTIFIED" else None,
            "counterexample": {"retained": "certificate"} if status == "REFUTED" else None}
    before = copy.deepcopy(atlas)
    runner._migrate_candidate_identity(atlas)
    unresolved = atlas["theorems"]["unresolved"]
    assert not set(cache) & set(unresolved)
    for field in ("conjecture", "proof_attempt", "last_proof_attempt_sequence"):
        assert unresolved[field] == before["theorems"]["unresolved"][field]
    assert atlas["theorems"]["certified"] == before["theorems"]["certified"]
    assert atlas["theorems"]["refuted"] == before["theorems"]["refuted"]
    assert atlas["candidate_identity_migration"]["invalidated_record_ids"] == ["unresolved"]
    migrated = copy.deepcopy(atlas)
    runner._migrate_candidate_identity(atlas)
    assert atlas == migrated


def test_guard_failure_retries_after_translation_becomes_available(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    from autonomous_math.prover import trusted_lean
    for relative in ("core/invariants.py", "core/expander_codes.py", "core/ast.py",
                     "sieve/instance_db.py", "sieve/adversarial_holdouts.py"):
        source = runner.REPO_ROOT / "autonomous_math" / relative
        fixture = tmp_path / "autonomous_math" / relative
        fixture.parent.mkdir(parents=True, exist_ok=True)
        fixture.write_bytes(source.read_bytes())
    translator = tmp_path / "autonomous_math/prover/trusted_lean.py"
    translator.parent.mkdir(parents=True)
    translator.write_text("first translator revision")
    monkeypatch.setattr(runner, "REPO_ROOT", tmp_path)
    available = [False]
    def translate(candidate):
        if not available[0]:
            raise ValueError("Guard has no trusted formalization yet")
        return "challenge", candidate.id
    monkeypatch.setattr(trusted_lean, "render_challenge", translate)
    candidate = claim("guarded", guard=GuardPredicate(property_name_or_type="is_connected"))
    atlas = empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert not search.calls
    assert atlas["theorems"]["guarded"]["proof_search_skipped"]
    available[0] = True
    translator.write_text("second translator revision")
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == ["guarded"]


def test_transient_model_failure_recovers_after_cooldown(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    def failed_request(self, candidate, **kwargs):
        search.calls.append(candidate.id)
        return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
            theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=0,
            synthesis_attempts=[{"status": "FAILED", "error": "temporary transport failure"}])
    monkeypatch.setattr(search, "prove_conjecture", failed_request)
    candidate, atlas = claim("retry_transport"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id]
    synchronous([candidate], atlas, tmp_path, lean_limit=1, screening_key="changed-catalog")
    assert search.calls == [candidate.id]
    atlas["theorems"][candidate.id]["next_retry_at"] = time.time()-1
    atlas["total_iterations"] = 2
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id, candidate.id]
    assert runner._retryable({"status": "UNRESOLVED", "error_message": "Shared proof-search budget exhausted"})


def test_sampling_history_updated_between_pair_draws(monkeypatch):
    from autonomous_math.prover.flywheel import FlywheelFeedback
    seen = []
    def sample(self, invariants, history):
        seen.append(set(history))
        return ("order", "size") if not history else ("order", "max_degree")
    monkeypatch.setattr(FlywheelFeedback, "sample_pair", sample)
    monkeypatch.setattr(FlywheelFeedback, "sample_triad", lambda *args: ("order", ["size", "max_degree"], None))
    monkeypatch.setattr(runner, "InstanceDatabase", lambda: SimpleNamespace(
        _cached_matrix={"order": [], "size": [], "max_degree": []}))
    atlas = empty_atlas()
    preset = runner._sample_preset({}, atlas)
    assert seen == [set(), {("order", "size")}]
    assert len(set(preset["pairs"])) == 2


def normalized(atlas):
    def remove_times(value):
        if isinstance(value, dict):
            return {key: remove_times(item) for key, item in value.items() if key not in {"timestamp", "created_at"}}
        if isinstance(value, list):
            return [remove_times(item) for item in value]
        return value
    clean = remove_times(atlas)
    clean.pop("batch_metrics", None)
    return clean


def test_spawn_one_and_two_workers_have_same_results(monkeypatch, tmp_path):
    candidates = [claim("nonnegative_order"), claim("nonnegative_size", invariant="size"),
                  claim("false", 10)]
    results = []
    for workers in (1, 2):
        runner.InstanceDatabase.clear_cache()
        result = runner._coordinate_candidates(candidates, empty_atlas(), tmp_path / str(workers), 0,
            runner.GracefulDaemonInterrupt(), time.monotonic()+60, {}, runner._options(workers=workers))
        results.append(result)
    assert normalized(results[0]) == normalized(results[1])
    assert results[0]["total_conjectures_generated"] == 3
    results[0]["total_iterations"] = 1
    again = runner._coordinate_candidates(candidates, results[0], tmp_path / "resume", 0,
        runner.GracefulDaemonInterrupt(), time.monotonic()+60, {}, runner._options(workers=2))
    assert again["total_conjectures_generated"] == 3
    assert again["batch_metrics"]["screened"] == 0


def test_bad_delta_is_rejected_before_merge(tmp_path):
    candidate = claim("true")
    jobs = runner._jobs("sieve", [candidate], tmp_path, 1)
    cert = CounterexampleCertificate.from_counterexample_graph(nx.path_graph(2), candidate)
    delta = {"job_id": jobs[0]["job_id"], "kind": "sieve", "records": [{
        "id": candidate.id, "conjecture": candidate.to_dict(), "status": "REFUTED", "counterexample": cert.to_dict()}]}
    with pytest.raises(ValueError, match="Unverified worker counterexample"):
        runner._validated_delta_records([delta], jobs)
    delta["records"][0]["conjecture"] = claim("true", 3).to_dict()
    with pytest.raises(ValueError, match="changed the assigned"):
        runner._validated_delta_records([delta], jobs)
    proof_jobs = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "context"})
    packet = {"job_id": proof_jobs[0]["job_id"], "kind": "proof", "records": [{
        "id": candidate.id, "conjecture": candidate.to_dict(), "proof_search_key": "context", "status": "LEAN_CERTIFIED"}]}
    with pytest.raises(ValueError, match="unassigned state"):
        runner._validated_delta_records([packet], proof_jobs)


def test_cancellation_terminates_spawn_workers_and_can_resume(monkeypatch, tmp_path):
    candidate = claim("retry")
    jobs = runner._jobs("sieve", [candidate], tmp_path, 1)
    before = {child.pid for child in multiprocessing.active_children()}
    with pytest.raises(InterruptedError):
        runner._dispatch_jobs(jobs, runner._snapshot(empty_atlas()), runner._options(),
            runner.GracefulDaemonInterrupt(), time.monotonic()+0.01, {})
    assert {child.pid for child in multiprocessing.active_children()} <= before
    result = runner._dispatch_jobs(jobs, runner._snapshot(empty_atlas()), runner._options(),
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {})
    assert result[0]["records"][0]["status"] == "EMPIRICAL_SURVIVOR"


def test_cancellation_kills_active_child_process_group(monkeypatch, tmp_path):
    if not hasattr(os, "fork"):
        pytest.skip("Unix process-group cancellation")
    original_context = multiprocessing.get_context
    monkeypatch.setattr(multiprocessing, "get_context", lambda mode: original_context("fork"))
    class SlowSearch:
        process = None
        def __init__(self, **kwargs):
            pass
        def prove_conjecture(self, candidate, **kwargs):
            self.process = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], start_new_session=True)
            (tmp_path / "child_pid").write_text(str(self.process.pid))
            self.process.wait()
        def active_process_groups(self):
            return [self.process.pid] if self.process and self.process.poll() is None else []
        def cancel(self):
            if self.process and self.process.poll() is None:
                os.killpg(self.process.pid, 9)
                self.process.wait(timeout=2)
    monkeypatch.setattr(runner, "LeanProofSearch", SlowSearch)
    candidate = claim("slow")
    jobs = runner._jobs("proof", [candidate], tmp_path, 1, {candidate.id: "context"})
    # The worker reserves 15 seconds itself, so stop explicitly while a real child is active.
    stop = runner.GracefulDaemonInterrupt()
    import threading
    def cancel_after_start():
        until = time.monotonic()+5
        while not (tmp_path / "child_pid").exists() and time.monotonic() < until:
            time.sleep(0.01)
        stop.stop_requested = True
    thread = threading.Thread(target=cancel_after_start)
    thread.start()
    with pytest.raises(InterruptedError):
        runner._dispatch_jobs(jobs, runner._snapshot(empty_atlas()), runner._options(), stop, time.monotonic()+30, {})
    thread.join(timeout=5)
    pid = int((tmp_path / "child_pid").read_text())
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


def test_hanging_planner_is_killed_without_checkpoint_or_rng_loss(monkeypatch, tmp_path):
    if not hasattr(os, "fork"):
        pytest.skip("Controlled hanging-process test uses Unix fork")
    # Warm catalog setup before the timer, so this test demonstrably reaches the hang.
    runner.InstanceDatabase()
    original_context = multiprocessing.get_context
    monkeypatch.setattr(multiprocessing, "get_context", lambda mode: original_context("fork"))
    original_generate = runner._generate
    def hanging_generate(*args):
        (tmp_path / "planner_started").write_text("entered deliberately hanging generator")
        time.sleep(30)
        return []
    monkeypatch.setattr(runner, "_generate", hanging_generate)
    atlas = empty_atlas()
    before_rng = runner.random.getstate()
    started = time.monotonic()
    with pytest.raises(InterruptedError):
        runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, 0,
            runner.GracefulDaemonInterrupt(), time.monotonic()+1, {}, options=runner._options())
    assert (tmp_path / "planner_started").exists()
    assert time.monotonic()-started < 6
    assert atlas == empty_atlas()
    assert runner.random.getstate() == before_rng
    assert not (tmp_path / "cumulative_discovery_atlas.json").exists()
    monkeypatch.setattr(runner, "_generate", original_generate)
    resumed = runner._bounded_batch({"pairs": [], "triads": []}, atlas, tmp_path, 0, 0, 0,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options=runner._options())
    assert resumed["total_conjectures_generated"] > 0
    assert resumed["batch_metrics"]["screened"] > 0


@pytest.mark.parametrize("workers", [-1, 0, 17, True, False, 1.0, 16.0, "16", None])
def test_worker_bounds(workers):
    with pytest.raises(ValueError):
        runner._options(workers=workers)


@pytest.mark.parametrize("workers", range(1, 17))
def test_worker_integer_range_is_supported(workers):
    assert runner._options(workers=workers)["workers"] == workers


def test_cli_worker_limit_matches_options(monkeypatch, tmp_path):
    called = []
    monkeypatch.setattr(runner, "run_continuous_daemon", lambda *args, **kwargs: called.append(kwargs))
    monkeypatch.setattr(sys, "argv", ["run_research.py", "--continuous", "--workers", "16",
                                    "--model-request-timeout", "1200",
                                    "--output-dir", str(tmp_path)])
    runner.main()
    assert called[0]["workers"] == 16
    assert called[0]["model_request_timeout"] == 1200
    monkeypatch.setattr(sys, "argv", ["run_research.py", "--workers", "17"])
    with pytest.raises(SystemExit) as failure:
        runner.main()
    assert failure.value.code == 2


@pytest.mark.parametrize("timeout", [300, 600, 1200])
def test_long_model_request_budget_scales_enclosing_deadline(timeout):
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    options = runner._options(workers=16, proof_backend="codex", model_rounds=2,
                              model_request_timeout=timeout)
    assert CodexProofSynthesizer(timeout_per_request=timeout).timeout_per_request == timeout
    assert runner._proof_budget(options) == 50 + 2 * (timeout + 10 + 30)


@pytest.mark.parametrize("timeout", [0, -1, 1201, float("inf"), float("nan")])
def test_runner_and_synthesizer_reject_unbounded_request_time(timeout):
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    with pytest.raises(ValueError):
        runner._options(model_request_timeout=timeout)
    with pytest.raises(ValueError):
        CodexProofSynthesizer(timeout_per_request=timeout)
