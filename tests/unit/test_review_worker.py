import copy
import json
import threading
import time
from types import SimpleNamespace

import pytest

from autonomous_math.novelty import review_worker as worker


def test_queue_allows_fresh_work_before_due_retry_and_skips_completed():
    records = [{"id": name, "status": "awaiting_review"} for name in ("fresh", "failed", "done", "named")]
    records[1]["ai_review"] = {"status": "error", "attempts": 1, "retry_at": 40}
    records[2]["ai_review"] = {"status": "complete", "attempts": 1}
    records[3]["assessment"] = {"reviewer": "Expert"}
    atlas = {"theorems": {item["id"]: {"discovered_iteration": 1} for item in records}}
    assert worker.next_review(records, atlas, 50)["id"] == "fresh"
    assert worker.next_review(records[1:], atlas, 30) is None
    assert worker.next_review(records[1:], atlas, 50)["id"] == "failed"


@pytest.fixture
def queue(monkeypatch, tmp_path):
    records = [{"id": "target", "status": "awaiting_review", "fingerprint": "same-proof"}]
    atlas = {"theorems": {"target": {"discovered_iteration": 1}}}
    writes = []
    monkeypatch.setattr(worker, "load_snapshot", lambda _: atlas)
    monkeypatch.setattr(worker, "get_reviews", lambda *_: {"records": copy.deepcopy(records)})

    def save(atlas, directory, identifier, fingerprint, result):
        assert identifier == "target" and fingerprint == "same-proof"
        writes.append(copy.deepcopy(result))
        records[0]["ai_review"] = copy.deepcopy(result)

    monkeypatch.setattr(worker, "record_ai_review", save)
    return SimpleNamespace(records=records, atlas=atlas, writes=writes)


class Synthesizer:
    timeout_per_request = 300

    def __init__(self):
        self.cancelled = threading.Event()

    def configuration(self):
        return {"configured_model": "configured-model", "reasoning_effort": "high"}

    def cancel(self):
        self.cancelled.set()


def await_condition(predicate):
    limit = time.monotonic() + 3
    while not predicate() and time.monotonic() < limit:
        time.sleep(0.01)
    assert predicate()


def test_worker_does_not_block_proofs_and_completed_review_is_not_repeated(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review
    started, release = threading.Event(), threading.Event()
    calls = []

    def assess(*args):
        calls.append(args)
        started.set()
        assert release.wait(3)
        return {"status": "complete", "outcome": "unresolved", "summary": "Evidence missing"}

    monkeypatch.setattr(model_review, "assess_review", assess)
    current = worker.ReviewWorker(tmp_path, Synthesizer())
    current.start()
    try:
        assert started.wait(3)
        assert current._thread.is_alive()
        current.pulse()
        assert json.loads((tmp_path / "novelty_review_worker.json").read_text())["current_id"] == "target"
        release.set()
        await_condition(lambda: queue.records[0].get("ai_review", {}).get("status") == "complete")
        current.wake()
    finally:
        release.set()
        current.close()
    resumed = worker.ReviewWorker(tmp_path, Synthesizer())
    resumed.start()
    resumed.close()
    assert len(calls) == 1
    assert queue.records[0]["status"] == "awaiting_review"


def test_stop_cancels_inflight_review_and_leaves_resumable_error(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review
    synthesizer = Synthesizer()
    entered = threading.Event()

    def assess(*args):
        entered.set()
        assert synthesizer.cancelled.wait(3)
        raise InterruptedError("Cancelled model request")

    monkeypatch.setattr(model_review, "assess_review", assess)
    current = worker.ReviewWorker(tmp_path, synthesizer)
    current.start()
    assert entered.wait(3)
    with pytest.raises(RuntimeError, match="already owns"):
        worker.ReviewWorker(tmp_path, Synthesizer()).start()
    current.close()
    assert not current._thread.is_alive()
    saved = queue.records[0]["ai_review"]
    assert saved["status"] == "error"
    assert saved["retry_at"] <= time.time()
    assert worker.next_review(queue.records, queue.atlas, time.time())


def test_error_preserves_failure_and_backs_off(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review

    def assess(*args):
        raise ValueError("Invented source citation")

    monkeypatch.setattr(model_review, "assess_review", assess)
    current = worker.ReviewWorker(tmp_path, Synthesizer())
    current._review_one(queue.atlas, queue.records[0])
    saved = queue.records[0]["ai_review"]
    assert saved["status"] == "error"
    assert "Invented source" in saved["error"]
    assert saved["retry_at"] > time.time()
    assert worker.next_review(queue.records, queue.atlas, time.time()) is None


def test_due_source_refresh_does_not_repeat_model_without_new_evidence(queue,monkeypatch,tmp_path):
    from autonomous_math.novelty import model_review,primary_sources
    ai={"status":"complete","outcome":"unresolved","sources_revision":primary_sources.SOURCE_REVISION,
        "revision":model_review.REVIEW_REVISION,"evidence_key":"same","trace_path":"preserved/trace.json"}
    queue.records[0].update(ai_review=ai,source_refresh_due=True)
    current=worker.ReviewWorker(tmp_path,Synthesizer())
    monkeypatch.setattr(model_review,"build_review_source_pack",lambda *a,**kw:{"evidence_key":"same","source_coverage":{"unavailable":[{"reason":"still inaccessible"}]}})
    monkeypatch.setattr(model_review,"assess_review",lambda *_:pytest.fail("unchanged acquisition must not charge a model"))
    assert worker.next_review(queue.records,queue.atlas,time.time())
    current._review_one(queue.atlas,queue.records[0])
    assert queue.records[0]["ai_review"]["trace_path"]=="preserved/trace.json"
    assert queue.records[0]["ai_review"]["source_refresh"]["status"]=="unchanged"
    # New primary text causes exactly one comparison, followed by completion.
    monkeypatch.setattr(model_review,"build_review_source_pack",lambda *a,**kw:{"evidence_key":"new","source_coverage":{}})
    calls=[]
    def assess(*_):
        calls.append(1);return {"status":"complete","outcome":"unresolved","sources_revision":primary_sources.SOURCE_REVISION,"evidence_key":"new"}
    monkeypatch.setattr(model_review,"assess_review",assess)
    current._review_one(queue.atlas,queue.records[0])
    queue.records[0].update(source_refresh_due=False)
    assert len(calls)==1 and worker.next_review(queue.records,queue.atlas,time.time()) is None


def test_invalid_bound_review_is_reassessed_even_when_paper_key_is_unchanged(queue,monkeypatch,tmp_path):
    from autonomous_math.novelty import model_review,primary_sources
    queue.records[0]["ai_review"]={"status":"complete","outcome":"unresolved","sources_revision":primary_sources.SOURCE_REVISION,
        "evidence_key":"same","refresh_pending":True,"trace_path":"retained/bad/trace.json"}
    monkeypatch.setattr(model_review,"build_review_source_pack",lambda *a,**kw:pytest.fail("invalid review must not use no-model shortcut"))
    calls=[]
    def assess(*_):
        calls.append(1);return {"status":"complete","outcome":"unresolved","sources_revision":primary_sources.SOURCE_REVISION,"evidence_key":"same"}
    monkeypatch.setattr(model_review,"assess_review",assess)
    assert worker.next_review(queue.records,queue.atlas,time.time())
    worker.ReviewWorker(tmp_path,Synthesizer())._review_one(queue.atlas,queue.records[0])
    assert len(calls)==1
    assert queue.records[0]["ai_review"]["prior_review"]["trace_path"]=="retained/bad/trace.json"


def test_start_failure_releases_worker_ownership(monkeypatch, tmp_path):
    first = worker.ReviewWorker(tmp_path, Synthesizer())
    monkeypatch.setattr(first, "pulse", lambda: (_ for _ in ()).throw(OSError("storage failed")))
    with pytest.raises(OSError, match="storage failed"):
        first.start()
    assert first._owner is None
    second = worker.ReviewWorker(tmp_path, Synthesizer())
    monkeypatch.setattr(second, "_run", lambda: None)
    second.start()
    second.close()


def test_completed_review_survives_normal_metadata_lock_contention(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review
    calls, waits = [], []
    save = worker.record_ai_review
    blocked = [70]  # Two bounded Crossref calls and pacing can hold the lock for seven seconds.

    def assess(*args):
        calls.append(args)
        return {"status": "complete", "outcome": "unresolved", "summary": "Comparison finished"}

    def contend(atlas, directory, identifier, fingerprint, result):
        if result["status"] == "complete" and blocked[0]:
            blocked[0] -= 1
            raise RuntimeError("Another novelty review writer owns this directory")
        return save(atlas, directory, identifier, fingerprint, result)

    monkeypatch.setattr(model_review, "assess_review", assess)
    monkeypatch.setattr(worker, "record_ai_review", contend)
    monkeypatch.setattr(worker.time, "sleep", waits.append)
    current = worker.ReviewWorker(tmp_path, Synthesizer())
    current._review_one(queue.atlas, queue.records[0])
    assert len(calls) == 1
    assert len(waits) == 70 and sum(waits) == pytest.approx(7)
    assert [result["status"] for result in queue.writes] == ["running", "complete"]
    assert worker.next_review(queue.records, queue.atlas, time.time()) is None


def test_close_publication_failure_still_releases_ownership(monkeypatch, tmp_path):
    first = worker.ReviewWorker(tmp_path, Synthesizer())
    monkeypatch.setattr(first, "_run", lambda: None)
    first.start()
    monkeypatch.setattr(first, "pulse", lambda: (_ for _ in ()).throw(OSError("storage failed")))
    with pytest.raises(OSError, match="storage failed"):
        first.close()
    assert first._owner is None and not first._thread.is_alive()
    second = worker.ReviewWorker(tmp_path, Synthesizer())
    monkeypatch.setattr(second, "_run", lambda: None)
    second.start()
    second.close()


def backlog():
    records = [{"id": f"fresh-{index:02d}", "status": "awaiting_review"} for index in range(35)]
    records.extend([
        {"id": "old-retry", "status": "awaiting_review", "ai_review": {
            "status": "error", "attempts": 4, "retry_at": 100, "started_at": 50}},
        {"id": "new-retry", "status": "awaiting_review", "ai_review": {
            "status": "error", "attempts": 1, "retry_at": 200, "started_at": 150}}])
    atlas = {"theorems": {item["id"]: {"discovered_iteration": 1} for item in records}}
    return records, atlas


def test_due_retry_gets_opportunity_after_two_fresh_requests(monkeypatch, tmp_path):
    records, atlas = backlog()
    monkeypatch.setattr(worker, "load_snapshot", lambda _: atlas)
    monkeypatch.setattr(worker, "get_reviews", lambda *_: {"records": copy.deepcopy(records)})
    selected = []
    current = worker.ReviewWorker(tmp_path, Synthesizer())

    def review_one(_, item):
        selected.append(item["id"])
        record = next(record for record in records if record["id"] == item["id"])
        record["ai_review"] = {"status": "complete", "attempts": 1}
        if len(selected) == 6:
            current._stop.set()

    monkeypatch.setattr(current, "_review_one", review_one)
    current._run()
    assert selected == ["fresh-00", "fresh-01", "old-retry", "fresh-02", "fresh-03", "new-retry"]


def test_resumed_worker_gives_due_retry_a_turn_within_two_fresh_requests(monkeypatch, tmp_path):
    records, atlas = backlog()
    # Prior completion is retained and is never offered again after restart.
    records[0]["ai_review"] = {"status": "complete", "attempts": 1}
    monkeypatch.setattr(worker, "load_snapshot", lambda _: atlas)
    monkeypatch.setattr(worker, "get_reviews", lambda *_: {"records": copy.deepcopy(records)})
    selected = []
    resumed = worker.ReviewWorker(tmp_path, Synthesizer())

    def review_one(_, item):
        selected.append(item["id"])
        record = next(record for record in records if record["id"] == item["id"])
        record["ai_review"] = {"status": "complete", "attempts": 1}
        if len(selected) == 3:
            resumed._stop.set()

    monkeypatch.setattr(resumed, "_review_one", review_one)
    resumed._run()
    assert selected == ["fresh-01", "fresh-02", "old-retry"]


def test_future_retry_cooldown_cannot_be_bypassed_by_fairness_counter():
    records, atlas = backlog()
    for record in records[-2:]:
        record["ai_review"]["retry_at"] = 2000
    assert worker.next_review(records, atlas, 1000, fresh_since_retry=2)["id"] == "fresh-00"
    assert worker.next_review(records[-2:], atlas, 1000, fresh_since_retry=2) is None


def test_oldest_due_retry_precedes_recent_failure_with_lower_attempt_count():
    records, atlas = backlog()
    assert worker.next_review(records, atlas, 1000, fresh_since_retry=2)["id"] == "old-retry"


@pytest.mark.parametrize("mechanical_status", ["known_result", "routine_consequence"])
def test_mechanically_closed_error_leaves_queue_without_losing_failure(mechanical_status):
    records, atlas = backlog()
    record = records[-2]
    record["automatic_status"] = mechanical_status
    before = copy.deepcopy(record)
    assert worker.next_review([record], atlas, 1000, fresh_since_retry=2) is None
    assert record == before


def test_superseded_error_is_inactive_even_when_display_status_is_awaiting():
    records, atlas = backlog()
    record = records[-2]
    record["ai_review"].update(superseded=True, superseded_reason="Named assessment resolved the queue")
    before = copy.deepcopy(record)
    assert worker.next_review([record], atlas, 1000, fresh_since_retry=2) is None
    assert record == before


def test_fresh_save_failure_cannot_starve_due_retry(monkeypatch, tmp_path):
    records, atlas = backlog()
    monkeypatch.setattr(worker, "load_snapshot", lambda _: atlas)
    monkeypatch.setattr(worker, "get_reviews", lambda *_: {"records": copy.deepcopy(records)})
    selected = []
    current = worker.ReviewWorker(tmp_path, Synthesizer())
    current._wake = SimpleNamespace(wait=lambda _: None, clear=lambda: None)

    def review_one(_, item):
        selected.append(item["id"])
        if len(selected) == 3:
            current._stop.set()
            return
        raise RuntimeError("The progress save was blocked before model launch")

    monkeypatch.setattr(current, "_review_one", review_one)
    current._run()
    assert selected == ["fresh-00", "fresh-00", "old-retry"]


def test_target_becoming_known_during_request_retains_only_ai_result(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review

    def assess(*args):
        queue.records[0].update(status="known_result", automatic_status="known_result")
        return {"status": "complete", "outcome": "unresolved", "summary": "Independent AI result"}

    monkeypatch.setattr(model_review, "assess_review", assess)
    current = worker.ReviewWorker(tmp_path, Synthesizer())
    current._review_one(queue.atlas, copy.deepcopy(queue.records[0]))
    assert queue.records[0]["status"] == "known_result"
    assert queue.records[0]["ai_review"]["status"] == "complete"
    assert worker.next_review(queue.records, queue.atlas, time.time(), fresh_since_retry=2) is None


def test_stale_classification_does_not_reopen_historical_error_before_refresh():
    records, atlas = backlog()
    record = records[-2]
    record.update(automatic_status="awaiting_review", classification_revision=None)
    record["ai_review"].update(error="Earlier model deadline", trace_path="preserved/trace.json")
    before = copy.deepcopy(record)
    assert worker.next_review([record], atlas, 1000, fresh_since_retry=2) is None
    assert record == before
    # A current deterministic comparison may legitimately leave the result open.
    record["classification_revision"] = "current-reviewed-policy-and-parent-context"
    assert worker.next_review([record], atlas, 1000, fresh_since_retry=2) is record
    assert record["ai_review"] == before["ai_review"]


def test_fresh_review_waits_for_deterministic_classification_refresh():
    record = {"id": "fresh", "status": "awaiting_review", "classification_revision": None}
    atlas = {"theorems": {"fresh": {"discovered_iteration": 1}}}
    assert worker.next_review([record], atlas, 1000) is None
    record["classification_revision"] = "current-reviewed-policy-and-parent-context"
    assert worker.next_review([record], atlas, 1000) is record


def test_old_review_policy_requires_new_assessment_even_when_paper_cache_is_unchanged(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review, primary_sources
    queue.records[0]["ai_review"] = {"status": "complete", "outcome": "unresolved", "sources_revision": primary_sources.SOURCE_REVISION,
        "revision": "prior-policy", "evidence_key": "same", "trace_path": "retained/prior/trace.json"}
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *a, **kw: pytest.fail("obsolete policy must not use unchanged-source shortcut"))
    calls = []
    def assess(*args):
        calls.append(args)
        return {"status": "complete", "outcome": "unresolved", "revision": model_review.REVIEW_REVISION, "evidence_key": "same"}
    monkeypatch.setattr(model_review, "assess_review", assess)
    current = worker.ReviewWorker(tmp_path, Synthesizer()); start = time.monotonic()
    current._review_one(queue.atlas, queue.records[0])
    assert len(calls) == 1 and calls[0][-1] - start == pytest.approx(2 * current.synthesizer.timeout_per_request + 20, abs=0.1)
    assert queue.records[0]["ai_review"]["prior_review"]["trace_path"] == "retained/prior/trace.json"


def test_worker_retains_both_request_measurements_on_skeptical_challenge_error(queue, monkeypatch, tmp_path):
    from autonomous_math.novelty import model_review
    from autonomous_math.prover.codex_synthesis import SynthesisError
    measurements = [{"stage": "assessment", "status": "complete", "usage": {"input_tokens": 100, "output_tokens": 20}, "duration_ms": 1000},
                    {"stage": "challenge", "status": "error", "usage": {}, "duration_ms": 1200000}]
    accounting = model_review._request_totals(measurements)
    monkeypatch.setattr(model_review, "assess_review", lambda *a: (_ for _ in ()).throw(SynthesisError("Challenge timeout", accounting)))
    worker.ReviewWorker(tmp_path, Synthesizer())._review_one(queue.atlas, queue.records[0])
    result = queue.records[0]["ai_review"]
    assert result["status"] == "error" and result["requests"] == measurements
    assert result["usage_accounting"]["missing_usage_count"] == 1 and result["usage"] == {}
    assert result["retry_at"] > time.time()
