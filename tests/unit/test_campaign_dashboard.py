"""Campaign views use saved ownership, never inferred historical attribution."""
import json
import os
from pathlib import Path
import shutil
import subprocess

import pytest

from autonomous_math.dashboard.data_service import CAMPAIGN_LABELS, DashboardDataService


def trace(root, relative, usage, status="MODEL_UNKNOWN", artifact=None):
    directory = root / relative
    directory.mkdir(parents=True, exist_ok=True)
    p = directory / "trace.json"
    p.write_text(json.dumps({"artifact_path": str(artifact or directory), "usage": usage, "status": status}))
    return p


def job(root, relative, campaign):
    directory = root / relative
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "job.json").write_text(json.dumps({"campaign": campaign, "kind": "proof"}))
    return directory


def test_per_campaign_costs_share_global_deduplication_and_include_failures(tmp_path):
    owner = job(tmp_path, "jobs/batch/proof-00", "spectral")
    saved = trace(tmp_path, "jobs/batch/proof-00/verified/synthesis/round_1",
                  {"input_tokens": 100, "cached_input_tokens": 75, "output_tokens": 20}, "KERNEL_ACCEPTED")
    trace(tmp_path, "copy", {}, "RUNNING", artifact=saved.parent)
    trace(tmp_path, "copy-final", {"input_tokens": 100, "cached_input_tokens": 75, "output_tokens": 20}, artifact=saved.parent)
    job(tmp_path, "jobs/batch/proof-01", "expander_codes")
    trace(tmp_path, "jobs/batch/proof-01/verified/synthesis/round_1", {}, "TIMEOUT")
    trace(tmp_path, "historical", {"input_tokens": 5, "output_tokens": 2})
    result = DashboardDataService(data_dir=tmp_path).get_token_usage()
    assert result["requests"] == 3
    assert result["total_tokens"] == 127
    assert result["cached_input_tokens"] == 75
    assert result["by_campaign"]["spectral"] == {"requests": 1, "reported_requests": 1,
        "unreported_requests": 0, "pending_request_traces": 0, "total_tokens": 120}
    assert result["by_campaign"]["expander_codes"]["unreported_requests"] == 1
    assert result["by_campaign"]["expander_codes"]["reported_requests"] == 0
    assert result["unattributed"]["requests"] == 1
    assert result["unattributed"]["total_tokens"] == 7
    assert sum(b["requests"] for b in result["by_campaign"].values()) + result["unattributed"]["requests"] == result["requests"]


def test_current_configuration_does_not_attribute_old_request(tmp_path):
    trace(tmp_path, "old", {"input_tokens": 8, "output_tokens": 2})
    service = DashboardDataService(data_dir=tmp_path)
    usage = service.get_token_usage()
    result = service.get_campaigns({"configuration": {"campaign": "expander_codes"}, "theorems": {}},
                                  {"state": "running"}, usage)
    assert usage["by_campaign"] == {}
    assert usage["unattributed"]["total_tokens"] == 10
    assert all(row["completed_batches"] is None and row["unique_proofs_added"] is None for row in result["rows"])
    assert result["current"] is None
    assert len(result["rows"]) == 7


@pytest.mark.parametrize("metadata", [{"campaign": "guessed-name"}, {"campaign": ["spectral"]}, {"research_family": "adjacency_spectrum"}])
def test_bad_or_family_only_job_metadata_is_unattributed(tmp_path, metadata):
    directory = tmp_path / "job"
    directory.mkdir()
    (directory / "job.json").write_text(json.dumps(metadata))
    trace(tmp_path, "job/round_1", {})
    usage = DashboardDataService(data_dir=tmp_path).get_token_usage()
    assert usage["unattributed"]["requests"] == 1
    assert usage["by_campaign"] == {}


def test_campaign_progress_preserves_unique_ids_and_partial_batch_boundary(tmp_path):
    atlas = {"campaign_rotation": {"revision": "campaign-focus-v1", "schedule": list(CAMPAIGN_LABELS),
             "current": None, "next": "spectral", "next_index": 0, "started_checkpoint": 149},
             "campaign_progress": {"expander_codes": {"completed_batches": 2, "last_checkpoint": 151,
               "last_completed_at": 100, "certified_ids": ["proof-a", "proof-a", "proof-b"],
               "unsupported_lean_candidates": 3}},
             "theorems": {"old": {"status": "LEAN_CERTIFIED"},
                 "new": {"status": "LEAN_CERTIFIED", "certified_campaign": "expander_codes"}}}
    status = {"state": "running", "campaign_rotation": dict(atlas["campaign_rotation"], current="spectral", next="advanced_spectral"),
              "batch_progress": {"stage": "proof", "pending": 2}}
    result = DashboardDataService(data_dir=tmp_path).get_campaigns(atlas, status, {"by_campaign": {}, "unattributed": {}})
    by_name = {r["name"]: r for r in result["rows"]}
    assert result["current"] == "spectral" and result["next"] == "advanced_spectral"
    assert by_name["spectral"]["state"] == "running"
    assert by_name["advanced_spectral"]["state"] == "next"
    assert by_name["expander_codes"]["unique_proofs_added"] == 2
    assert by_name["expander_codes"]["completed_batches"] == 2
    assert by_name["metric_topological"]["completed_batches"] is None
    assert "Diameter, radius, and girth" in by_name["metric_topological"]["limitations"]
    assert "order 16" in by_name["expander_codes"]["limitations"]
    assert result["historical_unattributed_proofs"] == 1
    assert result["batch_progress"] == status["batch_progress"]
    status["state"] = "stale"
    assert DashboardDataService(data_dir=tmp_path).get_campaigns(atlas, status, {})["current"] is None


def test_campaign_ui_labels_partial_usage_and_untracked_history():
    node = shutil.which("node")
    if not node:
        pytest.skip("Node exercises the existing dashboard JavaScript")
    html = (Path(__file__).parents[2] / "autonomous_math/dashboard/static/index.html").read_text()
    helpers = html[html.index("      const esc ="):html.index("      const fmt =")]
    function = html[html.index("      function renderCampaigns("):html.index("      function renderRunner(")]
    harness = r'''
    const assert = require("node:assert/strict"), elements = new Map();
    const $ = (id) => {if (!elements.has(id)) elements.set(id, {}); return elements.get(id);};
    const fmt = (n) => n == null ? "—" : String(n), date = String;
    '''
    assertions = r'''
    renderCampaigns({current:"spectral",next:"expander_codes",schedule:["spectral","expander_codes"],
      historical_unattributed_proofs:52,unattributed_usage:{requests:3,total_tokens:200,unreported_requests:1},
      batch_progress:{stage:"proof"},rows:[
      {name:"spectral",label:"Spectral bounds",state:"running",completed_batches:2,unique_proofs_added:1,
       token_usage:{requests:2,reported_requests:1,unreported_requests:1,pending_request_traces:1,total_tokens:100}},
      {name:"expander_codes",label:"Binary adjacency codes",state:"next",limitations:"Order 16 limit"}]});
    assert.match($("campaign-current").textContent,/Active: Spectral bounds/);
    assert.match($("campaign-current").textContent,/Next: Binary adjacency codes/);
    assert.match($("campaign-rows").innerHTML,/100 known/);
    assert.match($("campaign-rows").innerHTML,/1 reported · 1 missing · 1 pending/);
    assert.match($("campaign-rows").innerHTML,/No attributed requests/);
    assert.match($("campaign-rows").innerHTML,/—/);
    assert.match($("campaign-attribution").textContent,/untracked history/);
    assert.match($("campaign-attribution").textContent,/52 retained proofs have no campaign attribution/);
    assert.match($("campaign-batch-progress").textContent,/uncommitted work is excluded/);
    assert.doesNotMatch($("campaign-rows").innerHTML,/novel|discovery/i);
    '''
    subprocess.run([node, "-e", helpers + harness + function + assertions], check=True, capture_output=True, text=True)


def test_originality_usage_remains_unattributed_even_below_campaign_job(tmp_path):
    job(tmp_path, "campaign", "spectral")
    trace(tmp_path, "campaign/novelty_attempts/review-1", {"input_tokens": 50, "output_tokens": 5})
    trace(tmp_path, "campaign/novelty_attempts/review-2", {}, "TIMEOUT")
    usage = DashboardDataService(data_dir=tmp_path).get_token_usage()
    assert usage["by_campaign"] == {}
    assert usage["review"] == {"requests": 2, "reported_requests": 1, "unreported_requests": 1, "total_tokens": 55}
    assert usage["unattributed"]["requests"] == 2 and usage["unattributed"]["total_tokens"] == 55
    assert usage["requests"] == 2 and usage["total_tokens"] == 55


def test_uncommitted_visit_does_not_increment_committed_campaign_counters(tmp_path):
    atlas = {"campaign_progress": {"spectral": {"completed_batches": 1, "last_checkpoint": 151,
                                             "last_completed_at": 10, "certified_ids": []}}, "theorems": {}}
    status = {"state": "running", "campaign_rotation": {"schedule": list(CAMPAIGN_LABELS),
        "current": "spectral", "next": "extremal_coloring"},
        "campaign_visits": {"spectral": {"checkpoint": 152, "started_at": 20, "run_id": "run-1"}},
        "active_batch": {"campaign": "spectral", "checkpoint": 152, "started_at": 20, "state": "running"},
        "batch_progress": {"campaign": "spectral", "kind": "proof", "jobs_total": 3,
                           "jobs_started": 3, "jobs_completed": 1, "active_workers": 2}}
    result = DashboardDataService(data_dir=tmp_path).get_campaigns(atlas, status, {})
    row = next(row for row in result["rows"] if row["name"] == "spectral")
    assert row["last_visited_checkpoint"] == 152 and row["last_checkpoint"] == 151
    assert row["completed_batches"] == 1 and row["unique_proofs_added"] == 0
    assert result["active_batch"] == status["active_batch"]
    assert result["batch_progress"]["jobs_completed"] == 1
