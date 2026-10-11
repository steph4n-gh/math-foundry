import copy
import fcntl
import json
import threading

import pytest

import review_novelty as cli
from autonomous_math.novelty import model_review, review_worker
from autonomous_math.prover import codex_synthesis


@pytest.fixture
def batch(monkeypatch, tmp_path):
    records = [{"id": x, "fingerprint": x, "ai_review": {"status": "complete", "outcome": "unresolved"}}
               for x in ("a", "b")]
    atlas = {"theorems": {x["id"]: {"id": x["id"]} for x in records}}
    calls, cancelled, lock = [], [], threading.Lock()
    monkeypatch.setattr(cli, "get_reviews", lambda a, d: {"records": copy.deepcopy(records)})
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *a, **k:
                        {"source_coverage": {"primary_literature": 1}, "evidence_key": "bound"})
    monkeypatch.setattr(model_review, "validate_completed_review", lambda *a: {})

    class Synth:
        def __init__(self, **kwargs): self.configuration = kwargs
        def cancel(self): cancelled.append(self.configuration)

    class Worker:
        def __init__(self, directory, synthesizer, **kwargs): self.config = kwargs
        def stopped(self): return False
        def _review_one(self, frozen, record):
            with lock:
                calls.append((record["id"], frozen))
                item = next(r for r in records if r["id"] == record["id"])
                item["ai_review"] = {"status": "complete", "outcome": "routine_consequence",
                                     "assessment_sha256": "bound", "usage": None}

    monkeypatch.setattr(codex_synthesis, "CodexProofSynthesizer", Synth)
    monkeypatch.setattr(review_worker, "ReviewWorker", Worker)
    return atlas, records, calls, cancelled, tmp_path


def test_fixed_batch_uses_frozen_context_without_changing_atlas(batch):
    atlas, records, calls, cancelled, directory = batch
    before = copy.deepcopy(atlas)
    report = cli.review_unresolved(atlas, directory, directory / "report.json", identifiers=["a"], workers=2)
    assert report["state"] == "completed" and report["target_ids"] == ["a"]
    assert [c[0] for c in calls] == ["a"] and calls[0][1] is atlas
    assert atlas == before and len(cancelled) == 1
    assert report["results"][0]["attempts"][0]["usage"] is None
    assert records[1]["ai_review"]["outcome"] == "unresolved"


def test_model_validation_error_retries_once_and_retains_failure(batch, monkeypatch):
    atlas, records, calls, cancelled, directory = batch
    Worker = review_worker.ReviewWorker
    original = Worker._review_one

    def fail_then_complete(self, frozen, record):
        if not calls:
            calls.append((record["id"], frozen))
            records[0]["ai_review"] = {"status": "error", "error": "Exact quote does not bind"}
        else:
            original(self, frozen, record)

    monkeypatch.setattr(Worker, "_review_one", fail_then_complete)
    report = cli.review_unresolved(atlas, directory, directory / "report.json", identifiers=["a"])
    attempts = report["results"][0]["attempts"]
    assert [a["status"] for a in attempts] == ["error", "complete"]
    assert attempts[0]["error"] == "Exact quote does not bind"


def test_interrupt_cancels_queued_target_and_request_starting_after_first_cancel(batch, monkeypatch):
    atlas, records, calls, _, directory = batch
    launch_checkpoint, first_cancel, child_stopped = (threading.Event() for _ in range(3))
    active = threading.Event()
    real_wait = cli.wait
    interrupted = False

    class Synth:
        def __init__(self, **kwargs): pass
        def cancel(self):
            first_cancel.set()
            if active.is_set():
                child_stopped.set()

    class Worker:
        def __init__(self, *args, **kwargs): self.stop_requested = kwargs["stop_requested"]
        def stopped(self): return self.stop_requested()
        def _review_one(self, frozen, record):
            calls.append((record["id"], frozen))
            launch_checkpoint.set()
            assert first_cancel.wait(3), "Batch failed to signal interruption"
            # Simulate Popen occurring after the first cancel found no child.
            active.set()
            assert child_stopped.wait(3), "Cancellation was not repeated after request startup"
            records[0]["ai_review"] = {"status": "error", "error": "Interrupted request"}

    def interrupt_at_launch(*args, **kwargs):
        nonlocal interrupted
        if not interrupted:
            assert launch_checkpoint.wait(3)
            interrupted = True
            raise KeyboardInterrupt("stop batch")
        return real_wait(*args, **kwargs)

    monkeypatch.setattr(codex_synthesis, "CodexProofSynthesizer", Synth)
    monkeypatch.setattr(review_worker, "ReviewWorker", Worker)
    monkeypatch.setattr(cli, "wait", interrupt_at_launch)
    with pytest.raises(KeyboardInterrupt, match="stop batch"):
        cli.review_unresolved(atlas, directory, directory / "interrupted.json", identifiers=["a", "b"], workers=1)
    assert [call[0] for call in calls] == ["a"]  # Queued target never launches.
    assert child_stopped.is_set()
    assert records[0]["ai_review"]["status"] == "error"
    assert json.loads((directory / "interrupted.json").read_text())["state"] == "interrupted"


def test_batch_refuses_active_review_owner(batch):
    atlas, records, calls, cancelled, directory = batch
    with (directory / ".novelty_model_worker.lock").open("a+") as owner:
        fcntl.flock(owner, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(BlockingIOError):
            cli.review_unresolved(atlas, directory, directory / "report.json")
    assert not calls and json.loads((directory / "report.json").read_text())["state"] == "failed"


def test_batch_rejects_missing_target_and_report_overwrite(batch):
    atlas, records, calls, cancelled, directory = batch
    with pytest.raises(ValueError, match="current certified"):
        cli.review_unresolved(atlas, directory, directory / "missing.json", identifiers=["absent"])
    existing = directory / "existing.json"
    existing.write_text("existing evidence")
    with pytest.raises(ValueError, match="overwrite"):
        cli.review_unresolved(atlas, directory, existing)
    assert existing.read_text() == "existing evidence" and not calls


@pytest.mark.parametrize("workers,timeout", [(0, 1200), (5, 1200), (1, 0), (1, 1201)])
def test_review_batch_requires_finite_budgets(batch, workers, timeout):
    atlas, records, calls, cancelled, directory = batch
    with pytest.raises(ValueError, match="finite"):
        cli.review_unresolved(atlas, directory, directory / "report.json", workers=workers, timeout=timeout)
    assert not calls


def test_scholarly_query_follows_distance_ast_and_guard():
    from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, InvariantNode, UnaryOpNode
    from autonomous_math.novelty.review import _query
    distance = InvariantNode("parity_code_distance")
    target = Conjecture.create(id="query", lhs=UnaryOpNode("ceil", BinaryOpNode("/", distance, ConstantNode(8))),
                              rel="<=", rhs=InvariantNode("order"))
    assert "Griesmer" in _query(target)
    nullity = Conjecture.create(id="nullity", lhs=InvariantNode("parity_code_dimension"),
                               rel="<=", rhs=InvariantNode("max_degree"))
    assert "zero forcing" in _query(nullity) and "arbitrary field" in _query(nullity)
    assert len(_query(nullity)) <= 400
