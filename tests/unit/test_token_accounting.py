"""Request-level accounting must retain failures and avoid duplicate/subset sums."""
import json
import os

import pytest

from autonomous_math.dashboard.data_service import DashboardDataService


def save_trace(root, name, usage, *, status="KERNEL_ACCEPTED", modified=9900, artifact=None):
    directory = root / name
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "trace.json"
    path.write_text(json.dumps({"artifact_path": str(artifact or directory), "status": status, "usage": usage}))
    os.utime(path, (modified, modified))
    return path


def test_counts_failed_and_uncommitted_requests_once_without_subset_double_count(tmp_path):
    usage = {"input_tokens": 100, "cached_input_tokens": 80, "output_tokens": 20,
             "reasoning_output_tokens": 15, "cache_write_input_tokens": 5}
    saved = save_trace(tmp_path, "jobs/proof/round_1", usage)
    save_trace(tmp_path, "copy", {}, status="RUNNING", modified=9999, artifact=saved.parent)
    save_trace(tmp_path, "jobs/rejected/round_1", {"input_tokens": 10, "output_tokens": 3}, status="PROOF_BODY_REJECTED")
    save_trace(tmp_path, "jobs/timeout", {}, status="TIMEOUT")
    # The checkpoint omits older attempts and duplicates an accepted one.
    (tmp_path / "cumulative_discovery_atlas.json").write_text(json.dumps({"model_proposals": [
        {"artifact_path": str(saved.parent), "usage": usage}]}))
    result = DashboardDataService(data_dir=tmp_path).get_token_usage(now=10000)
    assert result["requests"] == 3
    assert result["reported_requests"] == 2
    assert result["unreported_requests"] == 1
    assert result["pending_request_traces"] == 0
    assert result["input_tokens"] == 110
    assert result["cached_input_tokens"] == 80
    assert result["output_tokens"] == 23
    assert result["total_tokens"] == 133
    assert result["last_hour"]["total_tokens"] == 133


def test_recent_window_uses_saved_time_and_missing_usage_is_not_zero_report(tmp_path):
    save_trace(tmp_path, "old", {"input_tokens": 200, "output_tokens": 50}, modified=6000)
    save_trace(tmp_path, "new", {}, status="RUNNING")
    service = DashboardDataService(data_dir=tmp_path)
    result = service.get_token_usage(now=10000)
    assert result["total_tokens"] == 250
    assert result["last_hour"] == {"reported_requests": 0, "unreported_requests": 1, "total_tokens": 0}
    assert result["pending_request_traces"] == 1
    save_trace(tmp_path, "new", {"input_tokens": 30, "output_tokens": 2}, status="MODEL_UNKNOWN")
    result = service.get_token_usage(now=10000)
    assert result["requests"] == result["reported_requests"] == 2
    assert result["pending_request_traces"] == result["unreported_requests"] == 0
    assert result["total_tokens"] == 282
    assert result["last_hour"]["total_tokens"] == 32


@pytest.mark.parametrize("usage", [None, {}, {"input_tokens": -1, "output_tokens": 2},
    {"input_tokens": True, "output_tokens": 2}, {"input_tokens": 1, "output_tokens": 2.5},
    {"input_tokens": 10, "output_tokens": 2, "cached_input_tokens": 11}])
def test_invalid_usage_is_explicitly_unreported(tmp_path, usage):
    save_trace(tmp_path, "bad", usage)
    result = DashboardDataService(data_dir=tmp_path).get_token_usage(now=10000)
    assert result["unreported_requests"] == 1
    assert result["reported_requests"] == result["total_tokens"] == 0


def test_missing_directory_corrupt_trace_and_actual_zero_report(tmp_path):
    service = DashboardDataService(data_dir=tmp_path / "missing")
    assert service.get_token_usage(now=10000)["requests"] == 0
    save_trace(tmp_path, "zero", {"input_tokens": 0, "output_tokens": 0})
    bad = tmp_path / "bad"
    bad.mkdir()
    (bad / "trace.json").write_text("{incomplete")
    result = DashboardDataService(data_dir=tmp_path).get_token_usage(now=10000)
    assert result["requests"] == result["reported_requests"] == result["unreadable_traces"] == 1
    assert result["unreported_requests"] == result["total_tokens"] == 0


def test_token_totals_are_exposed_in_telemetry(tmp_path, monkeypatch):
    from autonomous_math.sieve import instance_db
    class Catalog:
        _cached_gi = []
        _cached_matrix = {}
    monkeypatch.setattr(instance_db, "InstanceDatabase", Catalog)
    save_trace(tmp_path, "request", {"input_tokens": 12, "output_tokens": 3})
    telemetry = DashboardDataService(data_dir=tmp_path).get_telemetry({"theorems": {}})
    assert telemetry["pipeline"]["token_usage"]["total_tokens"] == 15
