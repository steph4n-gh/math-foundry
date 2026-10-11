"""Campaign ownership survives resumes without widening proof admission."""
import copy
import json
import time
from types import SimpleNamespace

import pytest

import run_research as runner
from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, GuardPredicate, InvariantNode


def candidate(identifier, variable, rhs="order", guard=None, helpers=()):
    return Conjecture.create(id=identifier, lhs=InvariantNode(variable), rel="<=",
        rhs=InvariantNode(rhs), guard=guard, metadata={"helper_for": list(helpers)} if helpers else {})


def atlas(iteration=209):
    return {"total_iterations": iteration, "theorems": {}}


def test_rotation_starts_at_spectral_then_resumes_exact_next_campaign():
    state = atlas()
    presets = list(runner.CAMPAIGN_PRESETS.values())
    runner._prepare_campaign_rotation(state, presets)
    assert runner._campaign_view(state)["next"] == "spectral"
    visited = []
    for index in range(9):
        # JSON serialization models the durable checkpoint between invocations.
        state = json.loads(json.dumps(state))
        runner._prepare_campaign_rotation(state, presets)
        name = presets[state["campaign_rotation"]["next_index"]]["campaign"]
        visited.append(name)
        working = copy.deepcopy(state)
        working["total_iterations"] += 1
        working["batch_metrics"] = {"screened": 1, "proof_targets": 0}
        runner._commit_campaign_batch(working, state, name, time.time())
        state = working
    assert visited == list(runner.CAMPAIGN_PRESETS) + ["spectral", "advanced_spectral"]
    assert sum(p["completed_batches"] for p in state["campaign_progress"].values()) == 9
    assert [b["checkpoint"] for b in state["campaign_history"]] == list(range(210, 219))


def test_failed_work_does_not_advance_committed_cursor_and_scope_change_archives_period():
    state = atlas()
    runner._prepare_campaign_rotation(state, [runner.CAMPAIGN_PRESETS["expander_codes"]])
    original = copy.deepcopy(state)
    abandoned = copy.deepcopy(state)
    abandoned["campaign_rotation"]["next_index"] = 0
    assert state == original
    runner._prepare_campaign_rotation(state, list(runner.CAMPAIGN_PRESETS.values()))
    assert runner._campaign_view(state)["next"] == "spectral"
    assert state["campaign_period_history"][0]["rotation"]["schedule"] == ["expander_codes"]
    runner._prepare_campaign_rotation(state, [runner.CAMPAIGN_PRESETS["chemical_energy"]])
    assert runner._campaign_view(state)["next"] == "chemical_energy"
    assert len(state["campaign_period_history"]) == 2


def test_certificate_attribution_counts_only_exact_new_ids_once():
    state = atlas()
    runner._prepare_campaign_rotation(state, list(runner.CAMPAIGN_PRESETS.values()))
    state["theorems"] = {"old": {"status": "LEAN_CERTIFIED"}}
    working = copy.deepcopy(state)
    working["total_iterations"] += 1
    working["theorems"]["new"] = {"status": "LEAN_CERTIFIED"}
    working["theorems"]["empirical"] = {"status": "EMPIRICAL_SURVIVOR"}
    runner._commit_campaign_batch(working, state, "spectral", time.time())
    assert working["campaign_progress"]["spectral"]["certified_ids"] == ["new"]
    assert "certified_campaign" not in working["theorems"]["old"]
    next_state = copy.deepcopy(working)
    next_state["total_iterations"] += 1
    runner._commit_campaign_batch(next_state, working, "advanced_spectral", time.time())
    assert next_state["campaign_progress"]["advanced_spectral"]["certified_added"] == 0
    assert next_state["theorems"]["new"]["certified_campaign"] == "spectral"


@pytest.mark.parametrize("name", list(runner.CAMPAIGN_PRESETS))
def test_selected_campaign_pins_agenda_and_supported_grammar(name, monkeypatch):
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda agenda, workspace: {
        "status": "UNAVAILABLE", "declarations": [], "sources": []})
    context = proposals.build_proposal_context({"research_family": name, "total_iterations": 999})
    agenda = context["agenda"]
    assert agenda["campaign"] == agenda["family"] == name
    family = proposals.campaign_family(name)
    assert runner.CAMPAIGN_PRESETS[name]["focus_invariants"] == family["focus"]
    assert set(agenda["focus_invariants"]) <= set(proposals.capability_report()["invariants"])
    if name == "metric_topological":
        assert {"diameter", "radius", "girth"} <= set(agenda["unsupported_lean_invariants"])
        assert {"triangle_count", "density"} <= set(agenda["focus_invariants"])
    if name == "expander_codes":
        assert "GF(2)" in agenda["code_semantics"]["construction"]


def test_generic_callers_keep_original_six_family_rotation(monkeypatch):
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"declarations": [], "sources": []})
    assert [proposals.build_proposal_context({"total_iterations": i})["agenda"]["family"]
            for i in range(7)] == [f["name"] for f in proposals._FAMILIES] + [proposals._FAMILIES[0]["name"]]


def test_campaign_scope_checks_numeric_premises_and_actual_helper_parent():
    spectral = runner.CAMPAIGN_PRESETS["spectral"]
    assert runner._campaign_eligible(candidate("s", "spectral_radius"), spectral)
    assert not runner._campaign_eligible(candidate("c", "parity_code_distance"), spectral)
    assert not runner._campaign_eligible(candidate("mixed", "spectral_radius", "parity_code_distance"), spectral)
    guard = GuardPredicate(invariant="parity_code_dimension", op=">=", threshold=1)
    assert not runner._campaign_eligible(candidate("premise_escape", "spectral_radius", guard=guard), spectral)
    state = {"theorems": {"s": {"conjecture": candidate("s", "spectral_radius").to_dict()},
                          "c": {"conjecture": candidate("c", "parity_code_distance").to_dict()}}}
    assert runner._campaign_eligible(candidate("helper", "size", helpers=["s"]), spectral, state)
    assert not runner._campaign_eligible(candidate("other_helper", "size", helpers=["c"]), spectral, state)
    assert not runner._campaign_eligible(candidate("invented_helper", "size", helpers=["missing"]), spectral, state)


def test_model_independent_exploration_cannot_smuggle_code_bridge_into_spectral(tmp_path, monkeypatch):
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"declarations": [], "sources": []})
    good = candidate("good", "spectral_radius")
    escaped = candidate("escaped", "spectral_radius", "parity_code_distance")
    def encode(c):
        return {"lhs_json": json.dumps(c.lhs_expr.to_dict()), "rhs_json": json.dumps(c.rhs_expr.to_dict()),
                "rel": "<=", "guard_json": None, "explanation": "Independent exploration of this proposed bound."}
    class Synthesizer:
        def request_json(self, *args):
            return {"proposals": [encode(escaped), encode(good)]}, {"status": "RESPONSE_VALIDATED"}
    selected, trace = proposals.propose_candidates(Synthesizer(), {"research_family": "spectral"}, tmp_path,
                                                   deadline=time.monotonic() + 5, limit=2)
    assert len(selected) == 1 and selected[0].metadata["campaign"] == "spectral"
    assert "leave the active campaign" in trace["rejected"][0]["reason"]


@pytest.mark.parametrize("name", list(runner.CAMPAIGN_PRESETS))
def test_adaptive_sampling_cannot_leave_campaign(name):
    preset = runner.CAMPAIGN_PRESETS[name]
    state = {"invariant_fertility": {"parity_code_distance": 100000, "graph_energy": 100000}}
    for _ in range(6):
        sampled = runner._sample_preset(preset, state, ["order", "size", "parity_code_distance", "graph_energy"])
        allowed = set(preset["focus_invariants"] + preset["bridge_invariants"])
        focus = set(preset["focus_invariants"])
        for pair in sampled["pairs"]:
            assert set(pair) <= allowed and set(pair) & focus
        for y, xs, *_ in sampled["triads"]:
            assert {y, *xs} <= allowed and {y, *xs} & focus
    assert name in state["campaign_sampling_history"]


def test_campaign_job_metadata_exists_before_request_launch(tmp_path, monkeypatch):
    options = dict(runner._options(proof_backend="none"), campaign="spectral", research_family="spectral",
                   focus_invariants=["spectral_radius"], bridge_invariants=["order"])
    job = {"job_id": "proposal-00", "kind": "proposal", "directory": str(tmp_path)}
    def run(job, snapshot, options, *args):
        saved = json.loads((tmp_path / "job.json").read_text())
        assert saved["campaign"] == saved["research_family"] == "spectral"
        return {"job_id": job["job_id"], "kind": job["kind"]}
    monkeypatch.setattr(runner, "_run_job", run)
    status = {}
    runner._dispatch_jobs([job], {"certified": []}, options, SimpleNamespace(stop_requested=False),
        time.monotonic() + 10, status, synchronous=True)
    assert status["batch_progress"]["jobs_completed"] == 1


def test_noncode_focus_does_not_generate_expander_seeds(monkeypatch):
    from autonomous_math.prover import trusted_lean
    monkeypatch.setattr(trusted_lean, "expander_code_candidates", lambda: pytest.fail("non-code campaign requested code seeds"))
    for method in ("generate_archetypal", "generate_advanced_spectral_candidates", "generate_metric_candidates", "generate_chemical_candidates"):
        monkeypatch.setattr(runner.ConjectureGenerator, method, lambda self: [])
    monkeypatch.setattr(trusted_lean, "bootstrap_candidates", lambda: [])
    assert runner._generate(runner.CAMPAIGN_PRESETS["spectral"], 0, 0) == []


def test_resume_and_campaign_change_reset_frontier_baseline(tmp_path, monkeypatch):
    visited = []
    def bounded(preset, state, *args, **kwargs):
        visited.append(preset["campaign"])
        working = copy.deepcopy(state)
        working["batch_metrics"] = {"screened": 1}
        return runner.reconcile(working)
    monkeypatch.setattr(runner, "_bounded_batch", bounded)
    monkeypatch.setattr(runner, "_refresh_novelty_reviews", lambda *args, **kwargs: None)
    first = runner.run_continuous_daemon(tmp_path, max_iterations=2, proof_backend="none", max_lean_targets=0)
    second = runner.run_continuous_daemon(tmp_path, max_iterations=1, proof_backend="none", max_lean_targets=0)
    assert visited == ["spectral", "advanced_spectral", "extremal_coloring"]
    assert second["frontier_period"]["starting_checkpoint"] == first["frontier_period"]["starting_checkpoint"] == 0
    third = runner.run_continuous_daemon(tmp_path, max_iterations=1, proof_backend="none", max_lean_targets=0,
                                        campaign="expander_codes")
    assert visited[-1] == "expander_codes"
    assert third["frontier_period"]["starting_checkpoint"] == 3
    assert len(third["frontier_period_history"]) == 1
