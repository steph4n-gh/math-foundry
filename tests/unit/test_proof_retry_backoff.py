"""Unchanged expensive failures wait; a changed checked context can retry immediately."""
import copy

import pytest

import run_research as runner
from autonomous_math.prover.lean_prover import LeanVerificationResult
from tests.unit.test_parallel_research import claim, empty_atlas, fake_engine, synchronous


def install_failure(monkeypatch, search, terminal, preliminary_timeout=True):
    def fail(self, candidate, **kwargs):
        search.calls.append(candidate.id)
        return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
            theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=4,
            diagnostics=[{"exit_code": 124 if preliminary_timeout else 1}, {"exit_code": 1}],
            synthesis_attempts=[{"status": terminal}])
    monkeypatch.setattr(search, "prove_conjecture", fail)


@pytest.mark.parametrize("terminal,expected", [
    ("MODEL_UNKNOWN", "model_unknown"), ("TIMEOUT", "model_timeout"),
    ("COMPILER_TIMEOUT", "compiler_timeout"), ("FAILED", "model_error")])
def test_unchanged_failures_require_elapsed_time_and_checkpoint_gap(
        fake_engine, monkeypatch, tmp_path, terminal, expected):
    _, search = fake_engine
    clock = [1000.0]
    monkeypatch.setattr(runner.time, "time", lambda: clock[0])
    install_failure(monkeypatch, search, terminal)
    candidate, atlas = claim("bounded_retry"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    record = atlas["theorems"][candidate.id]
    original_attempt = copy.deepcopy(record["proof_attempt"])
    assert record["proof_retry_reason"] == expected
    assert record["proof_retry_count"] == 1
    assert record["next_retry_at"] == 1300.0
    assert record["next_retry_iteration"] == 3
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id]
    # A new graph catalog does not erase the proof-context cooldown.
    atlas["total_iterations"] = 2
    synchronous([candidate], atlas, tmp_path, lean_limit=1, screening_key="new-catalog")
    assert search.calls == [candidate.id]
    clock[0] = 1400.0
    atlas["total_iterations"] = 1
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id]
    assert record["proof_attempt"] == original_attempt
    atlas["total_iterations"] = 2
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    record = atlas["theorems"][candidate.id]
    assert search.calls == [candidate.id, candidate.id]
    assert record["proof_retry_count"] == 2
    assert record["next_retry_at"] == 2000.0
    assert record["next_retry_iteration"] == 7


def test_changed_checked_context_unlocks_and_resets_backoff(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    monkeypatch.setattr(runner.time, "time", lambda: 1000.0)
    install_failure(monkeypatch, search, "MODEL_UNKNOWN")
    candidate, atlas = claim("changed_dependencies"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    old_key = atlas["theorems"][candidate.id]["proof_search_key"]
    search.context = "new-validated-proof-receipt"
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    record = atlas["theorems"][candidate.id]
    assert search.calls == [candidate.id, candidate.id]
    assert record["proof_search_key"] != old_key
    assert record["proof_retry_count"] == 1
    assert record["next_retry_iteration"] == 3


def test_model_unknown_is_not_reported_as_preliminary_compiler_timeout():
    for diagnostics in ([], [{"exit_code": 124}]):
        attempt = {"status": "UNRESOLVED", "diagnostics": diagnostics,
                   "synthesis_attempts": [{"status": "MODEL_UNKNOWN"}]}
        assert runner._proof_retry_reason(attempt) == "model_unknown"
        assert runner._retryable(attempt)


@pytest.mark.parametrize("terminal", ["KERNEL_REJECTED", "PROOF_BODY_REJECTED", "COUNTEREXAMPLE_REJECTED"])
def test_terminal_rejection_is_not_overridden_by_preliminary_timeout(
        fake_engine, monkeypatch, tmp_path, terminal):
    _, search = fake_engine
    install_failure(monkeypatch, search, terminal)
    candidate, atlas = claim("terminal_rejection"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    attempt = atlas["theorems"][candidate.id]["proof_attempt"]
    assert not runner._retryable(attempt)
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id]
    assert not set(runner.PROOF_RETRY_FIELDS) & set(atlas["theorems"][candidate.id])


def test_backoff_is_bounded_and_context_change_resets_count(monkeypatch):
    monkeypatch.setattr(runner.time, "time", lambda: 1000.0)
    record = {"proof_search_key": "same", "proof_attempt": {
        "status": "UNRESOLVED", "synthesis_attempts": [{"status": "TIMEOUT"}]}}
    for _ in range(100):
        runner._schedule_proof_retry(record, "same", 50)
    assert record["proof_retry_count"] == 5
    assert record["next_retry_at"] == 4600.0
    assert record["next_retry_iteration"] == 66
    record["proof_search_key"] = "changed"
    runner._schedule_proof_retry(record, "same", 50)
    assert record["proof_retry_count"] == 1
    assert record["next_retry_at"] == 1300.0
    assert record["next_retry_iteration"] == 52


@pytest.mark.parametrize("status", ["MACHINE_CHECKED_PROVEN", "REFUTED"])
def test_success_or_refutation_clears_retry_metadata(status):
    record = {field: 123 for field in runner.PROOF_RETRY_FIELDS}
    record.update(proof_search_key="same", proof_attempt={"status": status,
        "diagnostics": [{"exit_code": 124}], "synthesis_attempts": [{"status": "TIMEOUT"}]})
    runner._schedule_proof_retry(record, "same", 50)
    assert not set(runner.PROOF_RETRY_FIELDS) & set(record)


def test_existing_unknown_attempt_remains_retryable_without_new_metadata(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    install_failure(monkeypatch, search, "MODEL_UNKNOWN", preliminary_timeout=False)
    candidate, atlas = claim("legacy_unknown"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    record = atlas["theorems"][candidate.id]
    for field in runner.PROOF_RETRY_FIELDS:
        record.pop(field, None)
    runner.atomic_save_json(atlas, tmp_path / "cumulative_discovery_atlas.json")
    resumed = runner.load_snapshot(tmp_path)
    synchronous([candidate], resumed, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id, candidate.id]
    assert resumed["theorems"][candidate.id]["proof_retry_count"] == 1


def test_uncompiled_model_body_at_shared_deadline_gets_bounded_retry(fake_engine, monkeypatch, tmp_path):
    _, search = fake_engine
    clock = [1000.0]
    monkeypatch.setattr(runner.time, "time", lambda: clock[0])

    def uncompiled(self, candidate, **kwargs):
        search.calls.append(candidate.id)
        return LeanVerificationResult(status="UNRESOLVED", is_machine_checked=False,
            theorem_name=candidate.id, conjecture_id=candidate.id, attempts_count=1,
            diagnostics=[{"exit_code": 1, "compiler_launched": True},
                {"phase": "shared_budget", "exit_code": 124, "compiler_launched": False}],
            synthesis_attempts=[{"status": "KERNEL_REJECTED"}])

    monkeypatch.setattr(search, "prove_conjecture", uncompiled)
    candidate, atlas = claim("uncompiled_body"), empty_atlas()
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert atlas["theorems"][candidate.id]["proof_retry_reason"] == "shared_budget_exhausted"
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id]
    clock[0] += 301
    atlas["total_iterations"] = 2
    synchronous([candidate], atlas, tmp_path, lean_limit=1)
    assert search.calls == [candidate.id, candidate.id]


def test_earlier_shared_budget_marker_cannot_override_actual_terminal_kernel_error():
    attempt = {"status": "UNRESOLVED", "diagnostics": [
        {"phase": "shared_budget", "exit_code": 124, "compiler_launched": False},
        {"phase": "generated", "exit_code": 1, "compiler_launched": True}],
        "synthesis_attempts": [{"status": "KERNEL_REJECTED"}]}
    assert runner._proof_retry_reason(attempt) is None
