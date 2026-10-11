"""One resumable AI review queue alongside the research runner.

Only receipt-bound sidecar records are written. Model calls never hold the
sidecar lock or block proof scheduling, and completed triage is not originality.
"""
from __future__ import annotations

import fcntl
import logging
from pathlib import Path
import threading
import time
import uuid

from autonomous_math.research_state import atomic_save_json, load_snapshot
from autonomous_math.novelty.review import get_reviews, record_ai_review

logger = logging.getLogger(__name__)


def next_review(records, atlas, now, fresh_since_retry=0):
    """Give a due retry a turn after at most two fresh selections."""
    fresh, retries = [], []
    for record in records:
        ai = record.get("ai_review", {})
        if "classification_revision" in record and record["classification_revision"] is None:
            continue  # Wait for the deterministic refresh before reopening model work.
        if (record["status"] != "awaiting_review" or record.get("assessment")
                or record.get("automatic_status") in {"known_result", "routine_consequence"}
                or ai.get("superseded")):
            continue
        if (ai.get("status") == "complete" and not ai.get("refresh_pending") and not record.get("source_refresh_due")
                or ai.get("retry_at", 0) > now):
            continue
        (retries if ai else fresh).append(record)
    if retries and (fresh_since_retry >= 2 or not fresh):
        return min(retries, key=lambda item: (item["ai_review"].get("retry_at", 0),
            item["ai_review"].get("started_at", 0), item["id"]))
    return min(fresh, key=lambda item: (
        -atlas["theorems"][item["id"]].get("discovered_iteration", 0), item["id"]), default=None)


class ReviewWorker:
    def __init__(self, directory, synthesizer, stop_requested=lambda: False, deadline=float("inf")):
        self.directory = Path(directory)
        self.synthesizer = synthesizer
        self.stop_requested = stop_requested
        self.deadline = deadline
        self._stop = threading.Event()
        self._wake = threading.Event()
        self._owner = None
        self._thread = None
        self._fresh_since_retry = 0
        config = synthesizer.configuration()
        self.state = {"state": "idle", "current_id": None,
            "model": config.get("model_override") or config.get("configured_model"),
            "reasoning_effort": config.get("reasoning_effort"), "error": None}

    def stopped(self):
        return self._stop.is_set() or self.stop_requested() or time.monotonic() >= self.deadline

    def start(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        owner = (self.directory / ".novelty_model_worker.lock").open("a+")
        try:
            fcntl.flock(owner, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            owner.close()
            raise RuntimeError("An automated originality reviewer already owns this output directory")
        self._owner = owner
        self._thread = threading.Thread(target=self._run, name="originality-review", daemon=True)
        try:
            self.pulse()
            self._thread.start()
        except BaseException:
            owner.close()
            self._owner = None
            raise

    def wake(self):
        self._wake.set()

    def pulse(self):
        """Called by the runner heartbeat, including while a model call is blocked."""
        if self.stopped():
            self.synthesizer.cancel()
        atomic_save_json(dict(self.state, heartbeat=time.time()), self.directory / "novelty_review_worker.json")

    def close(self):
        self._stop.set()
        self._wake.set()
        # Repeat cancellation to cover a child starting between a stop check and
        # Popen. Keep the ownership lock until the worker has actually exited.
        if self._thread:
            until = time.monotonic() + 20
            while self._thread.is_alive() and time.monotonic() < until:
                self.synthesizer.cancel()
                self._thread.join(timeout=0.1)
            if self._thread.is_alive():
                raise RuntimeError("Originality reviewer did not stop within its cancellation budget")
        self.state = dict(self.state, state="stopped", current_id=None)
        try:
            self.pulse()
        finally:
            if self._owner:
                self._owner.close()
                self._owner = None

    def _save(self, record, result):
        # Reload at commit: a result for an obsolete proof can never attach to
        # a replacement. Brief contention with the metadata stage is retryable.
        for attempt in range(150):
            try:
                return record_ai_review(load_snapshot(self.directory), self.directory,
                    record["id"], record["fingerprint"], result)
            except RuntimeError:
                if attempt == 149:
                    raise
                time.sleep(0.1)

    def _review_one(self, atlas, record):
        from autonomous_math.novelty.model_review import assess_review, build_review_source_pack, REVIEW_REVISION
        from autonomous_math.novelty.primary_sources import SOURCE_REVISION
        previous = record.get("ai_review",{})
        if (previous.get("status") == "complete" and previous.get("sources_revision") == SOURCE_REVISION
                and previous.get("revision") == REVIEW_REVISION
                and not previous.get("refresh_pending")):
            # Retry a missing source automatically; unchanged evidence never
            # spends a second model request merely because the cooldown expired.
            prepared = build_review_source_pack(record,atlas["theorems"][record["id"]],atlas,
                directory=self.directory,deadline=min(self.deadline,time.monotonic()+20),online=True)
            if self.stopped():return
            if prepared["evidence_key"] == previous.get("evidence_key"):
                retained = dict(previous,source_refresh={"checked_at":time.time(),"status":"unchanged",
                                                        "coverage":prepared["source_coverage"]})
                self._save(record,retained)
                return
        attempt = record.get("ai_review", {}).get("attempts", 0) + 1
        attempt_dir = self.directory / "novelty_attempts" / (uuid.uuid4().hex)
        started = time.time()
        progress = {"status": "running", "attempts": attempt, "started_at": started,
            "model": self.state["model"], "reasoning_effort": self.state["reasoning_effort"],
            "trace_path": str(attempt_dir / "trace.json")}
        if record.get("ai_review",{}).get("status") == "complete":
            progress["prior_review"] = {key:record["ai_review"].get(key) for key in
                ("outcome","summary","trace_path","assessed_at","source_pack_sha256","evidence_digest")}
        self._save(record, progress)
        self.state = dict(self.state, state="running", current_id=record["id"], error=None)
        try:
            if self.stopped():
                raise InterruptedError("Research runner stopped")
            result = assess_review(record, atlas["theorems"][record["id"]], atlas,
                self.synthesizer, attempt_dir,
                # Each CLI request retains its finite cap; a possible extension
                # additionally requires a second skeptical request on the same
                # source pack. Include bounded source preparation overhead.
                min(self.deadline, time.monotonic() + 2 * self.synthesizer.timeout_per_request + 20))
            if self.stopped():
                raise InterruptedError("Research runner stopped before review commit")
            result = dict(progress, **result)
        except Exception as exc:
            trace = getattr(exc, "trace", {})
            result = dict(progress, status="error", error=str(exc)[:1500],
                finished_at=time.time(), retry_at=time.time() + (0 if self.stopped() else min(3600, 60 * 2**min(attempt, 6))),
                usage=trace.get("usage", {}), duration_ms=trace.get("duration_ms"))
            if trace.get("requests"):
                result.update(requests=trace["requests"], usage_accounting=trace.get("usage_accounting", {}))
            logger.warning("AI originality review for %s: %s", record["id"], exc)
        self._save(record, result)
        self.state = dict(self.state, state="idle", current_id=None, error=None)

    def _run(self):
        try:
            while not self.stopped():
                try:
                    atlas = load_snapshot(self.directory)
                    review = next_review(get_reviews(atlas, self.directory)["records"], atlas, time.time(),
                                         self._fresh_since_retry)
                    if review:
                        # Charge selection before launch/save so a persistence
                        # failure cannot keep resetting fresh-request priority.
                        self._fresh_since_retry = (0 if review.get("ai_review") else
                                                   min(2, self._fresh_since_retry + 1))
                        self._review_one(atlas, review)
                        continue
                    self.state = dict(self.state, state="idle", current_id=None, error=None)
                except Exception as exc:
                    self.state = dict(self.state, state="error", current_id=None, error=str(exc)[:1500])
                    logger.exception("Automated originality review unavailable")
                self._wake.wait(5)
                self._wake.clear()
        finally:
            self.state = dict(self.state, state="stopped", current_id=None)
