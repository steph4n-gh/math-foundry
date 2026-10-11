"""Checked composition, bounded proof contexts, and exact-byte timeout recovery."""
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.trusted_lean import render_challenge


def bound(identifier, left, right, reverse=False, guard=None, metadata=None):
    return Conjecture.create(id=identifier, lhs=right if reverse else left,
        rel=">=" if reverse else "<=", rhs=left if reverse else right, guard=guard, metadata=metadata)


def receipt(candidate, source=None):
    return {"theorem_name": candidate.id, "conjecture_id": candidate.id,
            "conjecture": candidate.to_dict(), "source_path": str(source) if source else "unused"}


def chain(reverse=(False, False, False), guards=(None, None, None)):
    n, m, delta = map(InvariantNode, ("order", "size", "max_degree"))
    p = bound("parent_a", n, m, reverse[0], guards[0])
    q = bound("parent_b", m, delta, reverse[1], guards[1])
    goal = bound("composed", n, delta, reverse[2], guards[2],
                 {"origin": "checked_transitivity", "parents": [p.id, q.id]})
    return goal, [receipt(p), receipt(q)]


@pytest.mark.parametrize("reverse", [(a, b, c) for a in (False, True)
                                    for b in (False, True) for c in (False, True)])
def test_composition_checks_all_inequality_orientations(reverse):
    goal, parents = chain(reverse)
    assert LeanProofSearch(max_attempts=1).candidate_tactics(goal, parents) == [
        "exact le_trans (parent_a G) (parent_b G)"]


@pytest.mark.parametrize("metadata", [
    {}, {"origin": "other", "parents": ["parent_a", "parent_b"]},
    {"origin": "checked_transitivity", "parents": "parent_a"},
    {"origin": "checked_transitivity", "parents": ["parent_a"]},
    {"origin": "checked_transitivity", "parents": ["parent_a", "parent_a"]},
    {"origin": "checked_transitivity", "parents": ["parent_a", 1]},
    {"origin": "checked_transitivity", "parents": ["parent_b", "parent_a"]},
    {"origin": "checked_transitivity", "parents": ["parent_a", "missing"]},
])
def test_malformed_parent_metadata_never_selects_transitivity(metadata):
    goal, parents = chain()
    goal = goal.model_copy(update={"metadata": metadata})
    assert not any(t.startswith("exact le_trans") for t in LeanProofSearch().candidate_tactics(goal, parents))


@pytest.mark.parametrize("mutation", ["middle", "endpoint", "strict"])
def test_parent_ast_not_metadata_must_establish_the_chain(mutation):
    goal, parents = chain()
    previous = Conjecture.from_dict(parents[1]["conjecture"])
    changes = {"middle": {"lhs_expr": ConstantNode(8)}, "endpoint": {"rhs_expr": ConstantNode(9)},
               "strict": {"rel": "<"}}[mutation]
    parents[1] = receipt(previous.model_copy(update=changes))
    assert not LeanProofSearch._composition_parents(goal, parents)


def test_composition_requires_compatible_guards_without_adding_premises():
    tree, connected = GuardPredicate("is_tree"), GuardPredicate("is_connected")
    goal, parents = chain(guards=(tree, None, tree))
    assert LeanProofSearch(max_attempts=1).candidate_tactics(goal, parents) == [
        "exact le_trans (parent_a G h_guard) (parent_b G)"]
    for guards in ((tree, None, None), (tree, connected, tree)):
        goal, parents = chain(guards=guards)
        assert not LeanProofSearch._composition_parents(goal, parents)


def test_supported_string_and_structured_guards_share_exact_formal_premise():
    structured = GuardPredicate(predicate_type="property", property_name="is_bipartite")
    goal, parents = chain(guards=("is_bipartite", structured, structured))
    assert LeanProofSearch(max_attempts=1).candidate_tactics(goal, parents) == [
        "exact le_trans (parent_a G h_guard) (parent_b G h_guard)"]
    assert all("h_guard" in tactic for tactic in LeanProofSearch._reuse_tactics(parents, goal))
    assert len(LeanProofSearch()._select_reuse(goal, parents)) == 2


def test_invalid_receipts_cannot_supply_metadata_parents(monkeypatch):
    import autonomous_math.research_state as state
    goal, parents = chain()
    wheel = SimpleNamespace(lemmas={r["conjecture_id"]: SimpleNamespace(
        lemma_id=r["conjecture_id"], receipt_path="invalid") for r in parents})
    monkeypatch.setattr(state, "validate_receipt", lambda *args: (None, "Changed source artifact"))
    prover = LeanProofSearch(flywheel=wheel)
    assert not prover._validated_reuse(goal)
    assert not any(t.startswith("exact le_trans") for t in prover.candidate_tactics(goal, prover._validated_reuse(goal)))


@pytest.mark.parametrize("root_qualified", [False, True])
def test_small_context_keeps_dependency_closure_and_tracks_observed_references(tmp_path, root_qualified):
    n = InvariantNode("order")
    prefix = "_root_." if root_qualified else ""
    declarations = []
    library = []
    for name, body in (("ancestor", "exact Nat.cast_nonneg _"),
                       ("bridge", f"exact {prefix}ancestor G"),
                       ("selected", "exact bridge G"),
                       ("unrelated", "exact Nat.cast_nonneg _")):
        c = bound(name, ConstantNode(0), n)
        source = render_challenge(c)[0].replace("sorry", body)
        declarations.append(source[source.index("theorem "):])
        library.append(receipt(c))
    path = tmp_path / "checked_source.lean"
    path.write_text("import Mathlib.Tactic\n" + "\n".join(declarations))
    library[1]["source_path"] = str(path)
    library[2]["source_path"] = str(path)
    target = bound("new_target", ConstantNode(0), n)
    challenge, context = LeanProofSearch._reuse_context(render_challenge(target)[0], [library[1], library[2]], library)
    assert "theorem unrelated " not in challenge
    assert challenge.index("theorem ancestor ") < challenge.index("theorem bridge ") < challenge.index("theorem selected ")
    assert challenge.count("theorem ancestor ") == 1 and challenge.count("theorem bridge ") == 1
    assert len(context["names"]) == 3 and context["selected_count"] == 2
    tracking = LeanProofSearch._reference_tracking(challenge.replace("sorry", f"exact {prefix}selected G"), target.id, context)
    assert tracking == {"used_lemma_ids": ["selected"], "transitive_used_lemma_ids": ["ancestor", "bridge"],
                        "context_lemma_ids": ["ancestor", "bridge", "selected"],
                        "reference_tracking": "source_identifier_references"}


def test_reuse_is_bounded_and_validated_explicit_parents_take_priority():
    goal, parents = chain()
    n = InvariantNode("order")
    unrelated = [receipt(bound(f"prior_{i}", n, ConstantNode(i))) for i in range(20)]
    selected = LeanProofSearch()._select_reuse(goal, unrelated + parents)
    assert len(selected) == 2
    assert {"parent_a", "parent_b"} <= {r["conjecture_id"] for r in selected}


def test_variable_overlap_fallback_is_bounded():
    goal = bound("fallback", ConstantNode(0), InvariantNode("order"))
    previous = [receipt(bound(f"prior_{i}", InvariantNode("order"), ConstantNode(i + 1))) for i in range(20)]
    assert len(LeanProofSearch()._select_reuse(goal, previous)) == LeanProofSearch.REUSE_LIMIT


def test_reference_tracking_ignores_comments_and_escaped_string_literals():
    body = 'have h := real G -- comment_only G\n/- outer nested_only /- nested -/ -/\ntrace "string_only \\"escaped\\""\nexact h'
    assert LeanProofSearch._identifier_references(body, ["real", "comment_only", "nested_only", "string_only", "escaped"]) == {"real"}


class RecordedToolchain:
    is_available = False
    workspace_dir = Path("/unused")

    def __init__(self, results, clock=None):
        self.results = iter(results)
        self.calls = []
        self.clock = clock

    def ensure_workspace_built(self):
        return True

    def get_version(self):
        return "test-double"

    def run_lean_code(self, code, timeout):
        self.calls.append((code, timeout))
        result = next(self.results)
        if result == "cancel":
            raise InterruptedError("cancelled")
        if self.clock is not None:
            self.clock[0] += timeout if result == 124 else 1
        if result == 0:
            return 0, "'retry_target' depends on axioms: [propext, Classical.choice, Quot.sound]\n", ""
        return result, "error: genuine fixture error" if result != 124 else "", "Lean verification timed out" if result == 124 else ""


class RecordedSynthesizer:
    max_rounds, timeout_per_request, allowed_imports = 2, 10, ()

    def __init__(self):
        self.requests = []

    def generate_candidate(self, challenge, feedback, attempt_dir, deadline):
        attempt_dir.mkdir(parents=True)
        self.requests.append((challenge, list(feedback)))
        return {"outcome": "proof", "proof_body": "exact Nat.cast_nonneg _", "imports": [],
                "explanation": "Known nonnegative order.", "counterexample": None}, {"artifact_path": str(attempt_dir)}


def retry_prover(monkeypatch, results, budget=60, clock=None):
    tool, synth = RecordedToolchain(results, clock), RecordedSynthesizer()
    prover = LeanProofSearch(toolchain=tool, synthesizer=synth, max_attempts=0,
                            timeout_per_attempt=10, total_timeout_sec=budget)
    monkeypatch.setattr(prover, "search_key", lambda _: "fixture")
    target = Conjecture.create(id="retry_target", lhs=InvariantNode("order"), rel=">=", rhs=ConstantNode(0))
    return prover, target, tool, synth


def test_generated_timeout_retries_identical_bytes_before_model_repair(tmp_path, monkeypatch):
    prover, target, tool, synth = retry_prover(monkeypatch, [124, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and result.attempts_count == 2 and len(synth.requests) == 1
    assert tool.calls[0][0] == tool.calls[1][0]
    assert [call[1] for call in tool.calls] == [10, 30]
    trace = result.synthesis_attempts[0]
    assert trace["status"] == "KERNEL_ACCEPTED" and trace["compiler_retry"]
    directory = Path(trace["artifact_path"])
    assert json.loads((directory / "compiler.json").read_text())["failure_kind"] == "compiler_timeout"
    assert json.loads((directory / "compiler_retry.json").read_text())["success"]


def test_timeout_retry_is_clipped_to_shared_deadline(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, tool, synth = retry_prover(monkeypatch, [124, 0], budget=25, clock=clock)
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and [call[1] for call in tool.calls] == [10, 15]
    assert len(synth.requests) == 1


def test_exhausted_budget_never_launches_retry_or_repair(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, tool, synth = retry_prover(monkeypatch, [124], budget=8, clock=clock)
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert not result.is_proven and len(tool.calls) == len(synth.requests) == 1
    assert result.synthesis_attempts[0]["status"] == "COMPILER_TIMEOUT"
    assert not result.synthesis_attempts[0]["compiler_retry"]


def test_real_errors_repair_normally_without_timeout_retry(tmp_path, monkeypatch):
    prover, target, tool, synth = retry_prover(monkeypatch, [1, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and len(synth.requests) == 2
    assert [call[1] for call in tool.calls] == [10, 10]
    assert not any(trace["compiler_retry"] for trace in result.synthesis_attempts)


def test_retry_preserves_cancellation_boundary(tmp_path, monkeypatch):
    prover, target, tool, synth = retry_prover(monkeypatch, [124, "cancel"])
    with pytest.raises(InterruptedError):
        prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert len(synth.requests) == 1 and len(tool.calls) == 2


def first_fixed_prover(monkeypatch, results, budget=60, clock=None):
    prover, target, tool, synth = retry_prover(monkeypatch, results, budget, clock)
    prover.max_attempts = 2
    monkeypatch.setattr(prover, "candidate_tactics", lambda *args: ["exact Nat.cast_nonneg _", "simp"])
    return prover, target, tool, synth


def test_first_fixed_timeout_retries_identical_bytes_without_requesting_model(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and result.attempts_count == 2 and not synth.requests
    assert tool.calls[0][0] == tool.calls[1][0]
    assert [call[1] for call in tool.calls] == [10, 30]
    assert [d["phase"] for d in result.diagnostics] == ["fixed_tactic", "fixed_tactic_timeout_retry"]
    assert result.diagnostics[0]["failure_kind"] == "compiler_timeout"
    assert result.diagnostics[1]["success"] and result.proof_origin == "fixed_tactic"


def test_first_fixed_candidate_is_retried_only_once(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124, 124, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and result.attempts_count == 3 and not synth.requests
    assert [call[1] for call in tool.calls] == [10, 30, 10]
    assert tool.calls[0][0] == tool.calls[1][0] != tool.calls[2][0]
    assert [d["phase"] for d in result.diagnostics] == [
        "fixed_tactic", "fixed_tactic_timeout_retry", "fixed_tactic"]


def test_later_fixed_candidate_timeout_does_not_delay_model_with_retry(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [1, 124, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and len(synth.requests) == 1
    assert [call[1] for call in tool.calls] == [10, 10, 10]
    assert [d["phase"] for d in result.diagnostics] == ["fixed_tactic", "fixed_tactic", "codex_synthesis"]


def test_first_fixed_compiler_error_is_not_retried(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [1, 0])
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and not synth.requests
    assert [call[1] for call in tool.calls] == [10, 10]
    assert all(d["phase"] == "fixed_tactic" for d in result.diagnostics)


def test_first_fixed_retry_never_shortens_an_already_long_attempt(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124, 0])
    prover.timeout_per_attempt = 30
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and not synth.requests
    assert [call[1] for call in tool.calls] == [30, 30]
    assert tool.calls[0][0] != tool.calls[1][0]
    assert all(d["phase"] == "fixed_tactic" for d in result.diagnostics)


def test_first_fixed_retry_is_clipped_to_shared_deadline(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124, 0], budget=25, clock=clock)
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert result.is_proven and [call[1] for call in tool.calls] == [10, 15]
    assert not synth.requests


def test_exhausted_first_fixed_budget_launches_neither_retry_nor_model(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124], budget=8, clock=clock)
    result = prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert not result.is_proven and len(tool.calls) == 1 and not synth.requests
    assert tool.calls[0][1] == 8 and result.attempts_count == 1
    assert result.diagnostics[-1]["phase"] == "shared_budget"
    assert not result.diagnostics[-1]["compiler_launched"]


def test_first_fixed_retry_preserves_cancellation_boundary(tmp_path, monkeypatch):
    prover, target, tool, synth = first_fixed_prover(monkeypatch, [124, "cancel"])
    with pytest.raises(InterruptedError):
        prover.prove_challenge(target, tmp_path, save_verified_artifact=False)
    assert len(tool.calls) == 2 and not synth.requests


def test_negative_cache_fingerprint_includes_selection_and_retry_policy():
    target = bound("fingerprint", ConstantNode(0), InvariantNode("order"))
    prover = LeanProofSearch(max_attempts=0)
    initial = prover.search_key(target)
    prover.REUSE_LIMIT += 1
    assert prover.search_key(target) != initial
    prover.REUSE_LIMIT -= 1
    prover.GENERATED_RETRY_TIMEOUT_SEC += 1
    assert prover.search_key(target) != initial
    prover.GENERATED_RETRY_TIMEOUT_SEC -= 1
    prover.SEARCH_POLICY = "checked-transitivity-small-context-v1"
    assert prover.search_key(target) != initial
