"""Originality review is bounded, read-only for proofs, and failure-isolated."""
import copy
import json
import random
import time
from urllib.request import urlopen

import pytest

import run_research as runner
from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.dashboard.server import run_dashboard
from autonomous_math.research_state import atomic_save_json


@pytest.mark.parametrize("search_fails", [False, True])
def test_reviews_follow_durable_checkpoints_and_failure_does_not_stop_research(tmp_path, monkeypatch, search_fails):
    from autonomous_math.novelty import review
    initial = {"theorems": {}, "total_iterations": 0, "total_refuted": 0,
               "total_lean_certified": 0, "random_state": random.getstate()}
    monkeypatch.setattr(runner, "load_snapshot", lambda directory: copy.deepcopy(initial))
    monkeypatch.setattr(runner, "_bounded_batch", lambda preset, atlas, *args, **kwargs: copy.deepcopy(atlas))
    committed = []

    def update(atlas, directory, **kwargs):
        on_disk = json.loads((directory / "cumulative_discovery_atlas.json").read_text())
        assert on_disk["total_iterations"] == atlas["total_iterations"]
        assert kwargs["max_searches"] == 2
        assert kwargs["online"] is False  # deterministic offline runner stays offline
        assert kwargs["timeout_sec"] <= 3
        committed.append(on_disk["total_iterations"])
        if search_fails:
            raise OSError("Literature storage unavailable")
        return {"updated_at": time.time(), "counts": {"awaiting_review": 0}}

    monkeypatch.setattr(review, "update_reviews", update)
    result = runner._execute(tmp_path, [{}], 2, 10, 0, 0, 0, 7, proof_backend="none", model_candidates=0)
    assert committed == [1, 2]
    assert result["total_iterations"] == 2
    assert result["theorems"] == initial["theorems"]
    status = json.loads((tmp_path / "run_status.json").read_text())
    assert status["state"] == "stopped"
    assert status["novelty_review"]["status"] == ("error" if search_fails else "complete")


@pytest.mark.parametrize("stopped,deadline", [(True, float("inf")), (False, 0)])
def test_stopped_or_expired_run_does_not_start_literature_request(tmp_path, monkeypatch, stopped, deadline):
    from autonomous_math.novelty import review
    def unexpected(*args, **kwargs):
        pytest.fail("Review should not begin after stop/deadline")
    monkeypatch.setattr(review, "update_reviews", unexpected)
    stop = runner.GracefulDaemonInterrupt()
    stop.stop_requested = stopped
    runner._refresh_novelty_reviews({}, tmp_path, {}, stop, deadline)


def test_corrupt_review_is_visible_without_breaking_proof_dashboard(tmp_path):
    (tmp_path / "novelty_reviews.json").write_text("{broken")
    result = DashboardDataService(data_dir=tmp_path).get_novelty_reviews({"theorems": {}})
    assert result["status"] == "unavailable"
    assert result["error"]
    assert result["records"] == []


def test_review_endpoint_is_read_only_and_separate_from_proof_status(tmp_path):
    atlas_path = tmp_path / "cumulative_discovery_atlas.json"
    atomic_save_json({"theorems": {}}, atlas_path)
    before = atlas_path.read_bytes()
    server = run_dashboard(port=0, block=False, data_dir=tmp_path)
    try:
        with urlopen(f"http://127.0.0.1:{server.server_port}/api/novelty_reviews", timeout=10) as response:
            result = json.loads(response.read())
        assert result["records"] == []
        assert result["counts"]["potential_contribution"] == 0
        assert atlas_path.read_bytes() == before
        assert not (tmp_path / "novelty_reviews.json").exists()
    finally:
        server.shutdown()
        server.server_close()


def test_cli_rejects_missing_atlas_without_creating_research_state(tmp_path):
    import review_novelty
    with pytest.raises(SystemExit) as error:
        review_novelty.main(["--output-dir", str(tmp_path), "--offline"])
    assert error.value.code == 2
    assert list(tmp_path.iterdir()) == []
