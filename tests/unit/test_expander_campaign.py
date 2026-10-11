"""Focused code campaigns keep exact domains, the retained atlas, and bounded admission."""
import copy
import json
import random
import sys
import time
from types import SimpleNamespace

import networkx as nx
import numpy as np
import pytest

import run_research as runner
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.prover.trusted_lean import expander_code_candidates, render_challenge
from autonomous_math.sieve.instance_db import CODE_COLUMNS, InstanceDatabase
from tests.unit.test_parallel_research import empty_atlas, fake_engine


@pytest.fixture
def catalog(monkeypatch):
    graphs = [nx.cycle_graph(4), nx.complete_graph(2), nx.empty_graph(17)]
    instances = [GraphInstance.from_networkx(g) for g in graphs]
    for key, value in {"_cached_nx": graphs, "_cached_gi": instances,
                       "_cached_invariants": [InstanceDatabase._compute_instance_invariants(g, n)
                                              for g, n in zip(instances, graphs)],
                       "_cached_matrix": None, "_code_columns_enabled": False}.items():
        monkeypatch.setattr(InstanceDatabase, key, value)
    InstanceDatabase._rebuild_cached_matrix()
    return InstanceDatabase()


def test_optional_columns_are_explicit_and_retained_graphs_are_nonvacuous(catalog):
    assert not set(CODE_COLUMNS) & set(catalog._cached_matrix)
    assert all(not set(CODE_COLUMNS) & set(row) for row in catalog._cached_invariants)
    coverage = catalog.ensure_code_columns()
    assert coverage == {"construction": "kernel_of_adjacency_over_GF2", "max_exact_order": 16,
                        "graphs": 3, "defined_graphs": 2, "unsupported_graphs": 1,
                        "nonzero_code_graphs": 1, "zero_code_graphs": 1}
    assert catalog._cached_matrix["parity_code_dimension"].tolist()[:2] == [2, 0]
    assert catalog._cached_matrix["parity_code_distance"].tolist()[:2] == [2, 3]
    assert catalog._cached_matrix["unique_neighbor_radius"].tolist()[:2] == [1, 2]
    assert np.isnan(catalog._cached_matrix["parity_code_distance"][2])
    catalog.add_instance(nx.cycle_graph(6))
    assert catalog.ensure_code_columns()["nonzero_code_graphs"] == 2
    assert all(len(catalog._cached_matrix[name]) == 4 for name in CODE_COLUMNS)
    InstanceDatabase._cached_matrix = None
    assert catalog.ensure_code_columns()["defined_graphs"] == 3
    assert all(len(catalog._cached_matrix[name]) == 4 for name in CODE_COLUMNS)


def test_guarded_code_sieve_counts_undefined_not_guard_false(catalog):
    target = expander_code_candidates()[2]
    result = catalog.sieve_conjecture(target)
    assert result.status == "SURVIVED"
    assert result.checked_instances_count == 1  # C4; K2's zero code fails the guard.
    assert result.undefined_instances_count == 1  # Order17 cannot evaluate the guard.
    source, _ = render_challenge(target)
    assert "h_guard" in source
    assert "≤ 16" not in source and "<= 16" not in source


@pytest.mark.parametrize("target", [
    Conjecture.create(id="false_zero_code_distance", lhs=InvariantNode("parity_code_distance"), rel="<=", rhs=InvariantNode("order")),
    Conjecture.create(id="false_unique_neighbor_radius", lhs=InvariantNode("unique_neighbor_radius"), rel=">=", rhs=ConstantNode(3)),
])
def test_false_code_controls_get_real_counterexample(catalog, target):
    result = catalog.sieve_conjecture(target)
    assert result.status == "REFUTED"
    assert result.counterexample_certificate is not None


@pytest.mark.parametrize("mixed", [True, False])
def test_guard_domain_failure_on_large_holdouts_is_explicit(monkeypatch, mixed):
    graphs = ([nx.cycle_graph(4)] if mixed else []) + [nx.empty_graph(17)]
    monkeypatch.setattr(runner, "_holdouts", lambda: tuple(GraphInstance.from_networkx(g) for g in graphs))
    result = runner.independent_holdout(expander_code_candidates()[2])
    assert result.status == ("SURVIVED" if mixed else "INCONCLUSIVE")
    assert result.checked_instances_count == int(mixed)
    assert result.undefined_instances_count == 1


def test_initial_code_seeds_and_adaptive_pairs_stay_in_focus(catalog):
    preset = runner.CAMPAIGN_PRESETS["expander_codes"]
    seeds = runner._generate(preset, 0, 0)
    assert len(seeds) == 4
    assert all(c.metadata["writeup"] for c in seeds)
    assert all(catalog.sieve_conjecture(c).status == "SURVIVED" for c in seeds)
    focus = set(CODE_COLUMNS)
    pool = focus | set(preset["bridge_invariants"])
    saved = random.getstate()
    try:
        random.seed(19)
        atlas = empty_atlas()
        for _ in range(12):
            selected = runner._sample_preset(preset, atlas, ["chromatic_number", "order", "max_degree"])
            for pair in selected["pairs"]:
                assert set(pair) <= pool and set(pair) & focus
            for target, inputs, guard in selected["triads"]:
                assert ({target} | set(inputs)) <= pool
                assert ({target} | set(inputs)) & focus
    finally:
        random.setstate(saved)


def test_only_exact_code_foundations_receive_known_classification(catalog, monkeypatch):
    monkeypatch.setattr(runner, "_holdouts", lambda: (GraphInstance.from_networkx(nx.cycle_graph(4)),))
    targets = expander_code_candidates()
    records = runner._sieve_delta(targets, lambda: None)
    assert all(r["novelty_status"] == "TEXTBOOK_FOLKLORE" for r in records)
    assert all(r["novelty_score"] == 0 for r in records)
    # A model cannot gain known status by borrowing an ID or trusted-looking metadata.
    changed = targets[3].model_copy(update={"rhs_expr": InvariantNode("parity_code_dimension")})
    assert runner._sieve_delta([changed], lambda: None)[0]["novelty_status"] == "UNKNOWN_IN_LITERATURE"


def test_code_evaluator_changes_invalidate_empirical_screen_cache(monkeypatch):
    from pathlib import Path
    original = Path.read_bytes
    old = runner._screening_key([])
    def changed(path):
        contents = original(path)
        return contents + b"\n# changed exact code evaluator\n" if path.name == "expander_codes.py" else contents
    monkeypatch.setattr(Path, "read_bytes", changed)
    assert runner._screening_key([]) != old


def test_focused_admission_retains_unrelated_records_and_global_cap(fake_engine, monkeypatch, tmp_path):
    database, search = fake_engine
    monkeypatch.setattr(database, "ensure_code_columns", lambda self: {}, raising=False)
    old = Conjecture.create(id="retained_old", lhs=InvariantNode("order"), rel=">=", rhs=ConstantNode(0))
    record = {"id": old.id, "conjecture": old.to_dict(), "statement": old.to_latex(),
              "status": "EMPIRICAL_SURVIVOR", "novelty_status": "UNKNOWN_IN_LITERATURE"}
    atlas = empty_atlas()
    atlas["candidate_identity_revision"] = runner.CANDIDATE_IDENTITY_REVISION
    atlas["theorems"][old.id] = copy.deepcopy(record)
    options = dict(runner._options(workers=2), replay_boundary=False, research_family="expander_codes",
                   focus_invariants=list(CODE_COLUMNS))
    runner._coordinate_candidates([old, *expander_code_candidates()], atlas, tmp_path, 1,
        runner.GracefulDaemonInterrupt(), time.monotonic()+30, {}, options, synchronous=True, screen_key="focus")
    assert len(search.calls) == 1 and search.calls[0] != old.id
    assert atlas["batch_metrics"]["proof_targets"] == 1
    assert atlas["batch_metrics"]["research_family"] == "expander_codes"
    assert atlas["theorems"][old.id] == record


def test_continuous_campaign_selection_and_default_rotation(monkeypatch, tmp_path):
    calls = []
    monkeypatch.setattr(runner, "_execute", lambda *args, **kwargs: calls.append((args, kwargs)))
    runner.run_continuous_daemon(tmp_path, campaign="expander_codes", model="chosen-model", reasoning_effort="xhigh")
    args, kwargs = calls.pop()
    assert args[1] == [runner.CAMPAIGN_PRESETS["expander_codes"]]
    assert args[10] == "chosen-model" and kwargs["reasoning_effort"] == "xhigh"
    assert kwargs["campaign"] == "expander_codes"
    runner.run_continuous_daemon(tmp_path)
    assert calls[-1][0][1] == list(runner.CAMPAIGN_PRESETS.values())
    assert calls[-1][1]["campaign"] is None


def test_cli_campaign_model_and_effort_are_forwarded(monkeypatch, tmp_path):
    captured = {}
    monkeypatch.setattr(runner, "run_continuous_daemon", lambda *args, **kwargs: captured.update(kwargs))
    monkeypatch.setattr(sys, "argv", ["run_research.py", "--continuous", "--campaign", "expander_codes",
        "--model", "gpt-6-astra", "--reasoning-effort", "xhigh", "--output-dir", str(tmp_path)])
    runner.main()
    assert captured["campaign"] == "expander_codes"
    assert captured["model"] == "gpt-6-astra" and captured["reasoning_effort"] == "xhigh"


def test_reasoning_effort_plumbs_to_bounded_synthesizer(monkeypatch):
    captured = {}
    monkeypatch.setattr("autonomous_math.prover.codex_synthesis.CodexProofSynthesizer",
                        lambda **kwargs: captured.update(kwargs))
    runner._synthesizer(runner._options(proof_backend="codex", reasoning_effort="high"))
    assert captured["reasoning_effort"] == "high"
    assert runner._options()["reasoning_effort"] is None
    with pytest.raises(ValueError, match="bounded model"):
        runner._options(reasoning_effort="invented")


def test_explicit_model_agenda_and_off_focus_proposal_rejection(monkeypatch, tmp_path):
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"declarations": []})
    atlas = dict(empty_atlas(), total_iterations=19, research_family="expander_codes",
                 code_catalog={"nonzero_code_graphs": 7})
    context = proposals.build_proposal_context(atlas)
    assert context["agenda"]["family"] == "expander_codes"
    assert context["agenda"]["selection"] == "explicit_campaign"
    assert context["agenda"]["catalog_coverage"]["nonzero_code_graphs"] == 7
    assert set(context["agenda"]["focus_invariants"]) == set(CODE_COLUMNS)
    assert "zero" in context["agenda"]["code_semantics"]["distance"]
    def proposal(name):
        return {"lhs_json": json.dumps({"node_type": "invariant", "name": name}),
                "rhs_json": json.dumps({"node_type": "constant", "value": 0}),
                "rel": ">=", "guard_json": None, "explanation": "A nonnegative foundational quantity; sharpness unknown."}
    synth = SimpleNamespace(request_json=lambda *args: ({"proposals": [proposal("parity_code_dimension"), proposal("order")]}, {}))
    candidates, trace = proposals.propose_candidates(synth, atlas, tmp_path, deadline=0, limit=2)
    assert len(candidates) == 1 and candidates[0].lhs_expr.variables == {"parity_code_dimension"}
    assert len(trace["rejected"]) == 1
    assert "selected mathematical family" in trace["rejected"][0]["reason"]


def test_dashboard_code_axes_and_active_model_selection(catalog, tmp_path):
    service = DashboardDataService(data_dir=tmp_path)
    pointcloud = service.get_pointcloud("parity_code_dimension", "parity_code_distance")
    assert pointcloud["excluded_undefined_points"] == 1
    assert {p["id"] for p in pointcloud["points"]} == {0, 1}
    assert set(CODE_COLUMNS) <= set(pointcloud["available_invariants"])
    (tmp_path / "run_status.json").write_text(json.dumps({"state": "stopped", "model_selection":
        {"model": "actual-selected", "reasoning_effort": "xhigh"}}))
    telemetry = service.get_telemetry(dict(empty_atlas(), configuration={"campaign": "expander_codes"}))
    assert telemetry["pipeline"]["code_catalog"]["nonzero_code_graphs"] == 1
    assert telemetry["pipeline"]["model_selection"] == {"model": "actual-selected", "reasoning_effort": "xhigh", "source": "runner", "enabled": True}
    json.dumps(telemetry, allow_nan=False)


def test_dashboard_preserves_committed_coverage_including_learned_graphs(catalog, tmp_path):
    committed = {"construction": "kernel_of_adjacency_over_GF2", "max_exact_order": 16,
                 "graphs": 5, "defined_graphs": 3, "unsupported_graphs": 2,
                 "nonzero_code_graphs": 2, "zero_code_graphs": 1}
    telemetry = DashboardDataService(data_dir=tmp_path).get_telemetry(
        dict(empty_atlas(), configuration={"campaign": "expander_codes"}, code_catalog=committed))
    assert telemetry["pipeline"]["code_catalog"] == committed
    assert telemetry["base_catalog_graphs"] == 3
    assert not catalog._code_columns_enabled


def test_current_offline_runner_disables_model_despite_old_model_receipts(catalog, tmp_path):
    old_attempt = {"configuration": {"configured_model": "old-model", "reasoning_effort": "xhigh"}}
    atlas = dict(empty_atlas(), configuration={"proof_backend": "codex"})
    atlas["theorems"] = {"old": {"proof_attempt": {"synthesis_attempts": [old_attempt]}}}
    (tmp_path / "run_status.json").write_text(json.dumps({"state": "running", "pid": 123,
        "heartbeat": time.time(), "model_selection": {"enabled": False, "model": None, "reasoning_effort": None}}))
    selection = DashboardDataService(data_dir=tmp_path).get_telemetry(atlas)["pipeline"]["model_selection"]
    assert selection == {"enabled": False, "model": None, "reasoning_effort": None, "source": "runner"}


def test_legacy_model_fallback_is_explicitly_historical(catalog, tmp_path):
    atlas = dict(empty_atlas(), configuration={"proof_backend": "codex"})
    atlas["theorems"] = {"old": {"proof_attempt": {"synthesis_attempts": [{"configuration": {
        "model_override": "actual-old-override", "configured_model": "different-default",
        "configured_reasoning_effort": "high"}}]}}}
    selection = DashboardDataService(data_dir=tmp_path).get_telemetry(atlas)["pipeline"]["model_selection"]
    assert selection["source"] == "historical"
    assert selection["model"] == "actual-old-override"
    assert selection["reasoning_effort"] == "high"


def test_offline_runner_status_explicitly_records_disabled_model(monkeypatch, tmp_path):
    monkeypatch.setattr(runner.InstanceDatabase, "clear_cache", lambda: None)
    runner._execute(tmp_path, [runner.CAMPAIGN_PRESETS["expander_codes"]], 0, None, 0, 0, 0, 7,
                    proof_backend="none")
    status = json.loads((tmp_path / "run_status.json").read_text())
    assert status["model_selection"] == {"enabled": False, "model": None, "reasoning_effort": None}
