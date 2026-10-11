"""Compiler context reductions preserve proof trust and finite retry gates.

All compiler and synthesizer calls in this module are deterministic local test
doubles. Actual host compilation is exercised separately by the recovery audit.
"""
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.trusted_lean import render_challenge


def nonnegative(identifier, guard=None):
    return Conjecture.create(id=identifier, lhs=ConstantNode(0), rel="<=",
                             rhs=InvariantNode("order"), guard=guard)


def expanded_context(tmp_path, guard=None):
    library = []
    for name, body in (("ancestor", "exact Nat.cast_nonneg _"),
                       ("bridge", "exact ancestor G"),
                       ("selected", "exact bridge G"),
                       ("unrelated", "exact Nat.cast_nonneg _")):
        target = nonnegative(name, guard)
        if guard is not None and name in {"bridge", "selected"}:
            body += " h_guard"
        source = tmp_path / f"{name}.lean"
        source.write_text(render_challenge(target)[0].replace("sorry", body))
        library.append({"theorem_name": name, "conjecture_id": name,
                        "conjecture": target.to_dict(), "source_path": str(source)})
    # A selected source is itself a complete independently checked declaration
    # closure; that mirrors the durable sources produced by real proof reuse.
    closure_source = tmp_path / "closure.lean"
    bodies = [Path(receipt["source_path"]).read_text() for receipt in library]
    imports = sorted({line for body in bodies for line in body.splitlines()
                      if line.startswith("import ")})
    closure_source.write_text("\n".join(imports) + "\nopen scoped BigOperators\n" +
                              "\n".join(body[body.index("theorem "):] for body in bodies))
    for receipt in library:
        receipt["source_path"] = str(closure_source)
    target = nonnegative("prune_target", guard)
    base = render_challenge(target)[0]
    challenge, context = LeanProofSearch._reuse_context(base, [library[2], library[3]], library)
    return target, base, challenge, context, library


def theorem_block(code, name):
    start = code.index(f"theorem {name} ")
    next_decl = code.find("\ntheorem ", start + 1)
    return code[start:next_decl if next_decl >= 0 else None]


def target_statement(code):
    return theorem_block(code, "prune_target").split(":= by", 1)[0]


def test_direct_parent_retains_transitive_checked_closure_and_exact_target(tmp_path):
    _, base, challenge, context, _ = expanded_context(tmp_path)
    pruned, actual = LeanProofSearch._prune_context(challenge, "prune_target", "exact selected G", context)
    assert actual["names"] == {"ancestor", "bridge", "selected"}
    assert "theorem unrelated " not in pruned
    assert pruned.index("theorem ancestor ") < pruned.index("theorem bridge ") < pruned.index("theorem selected ")
    assert target_statement(pruned) == target_statement(base)
    assert {line for line in challenge.splitlines() if line.startswith("import ")} == {
        line for line in pruned.splitlines() if line.startswith("import ")}
    assert "open scoped BigOperators" in pruned
    assert actual["selected_names"] == {"selected"}
    compiled = pruned.replace("sorry", "exact selected G")
    tracking = LeanProofSearch._reference_tracking(compiled, "prune_target", actual)
    assert tracking["used_lemma_ids"] == ["selected"]
    assert tracking["transitive_used_lemma_ids"] == ["ancestor", "bridge"]
    assert tracking["context_lemma_ids"] == ["ancestor", "bridge", "selected"]


def test_no_named_parent_omits_proof_bodies_but_keeps_imports_scopes_and_guard(tmp_path):
    _, base, challenge, context, _ = expanded_context(tmp_path, GuardPredicate("is_connected"))
    pruned, actual = LeanProofSearch._prune_context(challenge, "prune_target", "exact Nat.cast_nonneg _", context)
    assert not actual["names"] and actual["selected_count"] == 0
    assert not any(f"theorem {name} " in pruned for name in context["names"])
    assert target_statement(pruned) == target_statement(base)
    assert "h_guard" in target_statement(pruned)
    assert "open scoped BigOperators" in pruned


@pytest.mark.parametrize("body", ["exact _root_.selected G", "nlinarith [selected G, bridge G]"])
def test_root_qualified_and_shared_dependency_references_keep_single_ancestor(tmp_path, body):
    _, _, challenge, context, _ = expanded_context(tmp_path)
    pruned, actual = LeanProofSearch._prune_context(challenge, "prune_target", body, context)
    assert actual["names"] == {"ancestor", "bridge", "selected"}
    assert pruned.count("theorem ancestor ") == 1
    assert pruned.count("theorem bridge ") == 1


def test_comment_and_string_mentions_are_not_parent_dependencies(tmp_path):
    _, _, challenge, context, _ = expanded_context(tmp_path)
    body = 'trace "selected G"\n/- bridge G /- ancestor G -/ -/\n-- unrelated G\nexact Nat.cast_nonneg _'
    pruned, actual = LeanProofSearch._prune_context(challenge, "prune_target", body, context)
    assert not actual["names"]
    assert "theorem selected " not in pruned


def test_pruning_one_candidate_does_not_remove_context_from_later_candidates(tmp_path):
    _, _, challenge, context, _ = expanded_context(tmp_path)
    original_names = set(context["names"])
    first, _ = LeanProofSearch._prune_context(challenge, "prune_target", "exact selected G", context)
    second, actual = LeanProofSearch._prune_context(challenge, "prune_target", "exact unrelated G", context)
    assert "theorem unrelated " not in first
    assert "theorem unrelated " in second
    assert actual["names"] == {"unrelated"}
    assert context["names"] == original_names


@pytest.mark.parametrize("body", ["exact?", "apply?", "library_search", "aesop", "simp_all",
                                 "solve_by_elim", "apply_rules [selected]", "run_tac pure ()"])
def test_implicit_global_search_and_meta_operations_keep_full_context(tmp_path, body):
    _, _, challenge, context, _ = expanded_context(tmp_path)
    pruned, actual = LeanProofSearch._prune_context(challenge, "prune_target", body, context)
    assert pruned == challenge
    assert actual["names"] == context["names"]


@pytest.mark.parametrize("mutation", ["unknown_dependency", "cycle", "missing_declaration", "wrong_target"])
def test_bad_context_or_declaration_bindings_fail_closed(tmp_path, mutation):
    _, _, challenge, context, _ = expanded_context(tmp_path)
    context = {**context, "dependencies": {name: set(dependencies)
                                           for name, dependencies in context["dependencies"].items()}}
    name = "prune_target"
    if mutation == "unknown_dependency":
        context["dependencies"]["selected"].add("not_checked")
    elif mutation == "cycle":
        context["dependencies"]["ancestor"].add("selected")
    elif mutation == "missing_declaration":
        challenge = challenge.replace(theorem_block(challenge, "ancestor"), "")
    else:
        name = "missing_target"
    with pytest.raises(ValueError):
        LeanProofSearch._prune_context(challenge, name, "exact selected G", context)


class CompilerDouble:
    is_available = False

    def __init__(self, workspace, outcomes, clock=None):
        self.workspace_dir = workspace
        self.outcomes = iter(outcomes)
        self.calls = []
        self.clock = clock

    def ensure_workspace_built(self):
        return True

    def get_version(self):
        return "fixed compiler double"

    def run_lean_code(self, code, timeout):
        self.calls.append((code, timeout))
        result = next(self.outcomes)
        if result == "cancel":
            raise InterruptedError("cancellation during bounded verification")
        if self.clock is not None:
            self.clock[0] += timeout if result == 124 else 1
        if result == 0:
            return 0, "'prune_target' depends on axioms: [propext, Classical.choice, Quot.sound]\n", ""
        return result, "", "Lean verification timed out" if result == 124 else "error: bounded fixture rejection"


class SynthesizerDouble:
    max_rounds, timeout_per_request, allowed_imports = 3, 1200, ()

    def __init__(self, body):
        self.body, self.requests = body, []

    def generate_candidate(self, challenge, feedback, directory, deadline):
        directory.mkdir(parents=True)
        self.requests.append((challenge, list(feedback), deadline))
        return {"outcome": "proof", "proof_body": self.body, "imports": [],
                "explanation": "Fixture uses an already checked parent.", "counterexample": None}, {
                    "artifact_path": str(directory)}


def fixture_prover(tmp_path, monkeypatch, outcomes, body="exact selected G", budget=3770, clock=None):
    target, _, expanded, _, library = expanded_context(tmp_path)
    tool = CompilerDouble(tmp_path, outcomes, clock)
    synth = SynthesizerDouble(body)
    prover = LeanProofSearch(toolchain=tool, synthesizer=synth, max_attempts=0,
                            timeout_per_attempt=10, total_timeout_sec=budget)
    monkeypatch.setattr(prover, "search_key", lambda _: "fixture key")
    monkeypatch.setattr(prover, "_checked_library", lambda: library)
    monkeypatch.setattr(prover, "_select_reuse", lambda *args: [library[2], library[3]])
    return prover, target, expanded, tool, synth


def test_full_model_context_actual_compiler_source_and_saved_receipt_match(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module
    import autonomous_math.research_state as state

    prover, target, expanded, tool, synth = fixture_prover(tmp_path, monkeypatch, [0])
    binary = tmp_path / "compiler-double"
    binary.write_text("not executed")
    monkeypatch.setattr(module.subprocess, "run", lambda *args, **kwargs: SimpleNamespace(stdout=str(binary)))
    monkeypatch.setattr(state, "workspace_fingerprint", lambda _: "fixture workspace")
    result = prover.prove_challenge(target, tmp_path / "verified")
    assert result.is_proven and len(synth.requests) == 1
    assert synth.requests[0][0] == expanded
    source = result.verified_file_path.read_text()
    receipt = json.loads(result.receipt_path.read_text())
    challenge = Path(receipt["challenge_path"]).read_text()
    assert source + "\n#print axioms prune_target\n" == tool.calls[0][0]
    assert "theorem unrelated " not in source and "theorem unrelated " not in challenge
    assert source.split("theorem prune_target ", 1)[0] == challenge.split("theorem prune_target ", 1)[0]
    assert target_statement(source) == target_statement(challenge)
    assert receipt["source_sha256"] == hashlib.sha256(source.encode()).hexdigest()
    assert receipt["challenge_sha256"] == hashlib.sha256(challenge.encode()).hexdigest()
    assert receipt["conjecture"] == target.to_dict()
    assert result.context_lemma_ids == ["ancestor", "bridge", "selected"]
    assert result.diagnostics[-1]["context_declaration_count"] == 3
    assert result.diagnostics[-1]["selected_lemma_count"] == 1


def test_pre_existing_proof_keeps_checked_parent_context_without_model_request(tmp_path, monkeypatch):
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [0])
    existing = render_challenge(target)[0].replace("sorry", "exact selected G")
    result = prover.prove_challenge(existing, tmp_path / "verified", save_verified_artifact=False)
    assert result.is_proven and result.proof_origin == "pre_existing"
    assert not synth.requests and len(tool.calls) == 1
    # The existing proof's dependency cannot be inferred from the absent tactic.
    # Preserve this path conservatively, including its complete checked context.
    compiled = tool.calls[0][0]
    assert "theorem selected " in compiled and "theorem ancestor " in compiled
    assert "theorem unrelated " in compiled
    assert result.used_lemma_ids == ["selected"]
    assert result.transitive_used_lemma_ids == ["ancestor", "bridge"]


def test_pruned_exact_byte_retry_keeps_model_count_and_shared_deadline(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module

    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [124, 0], budget=25, clock=clock)
    result = prover.prove_challenge(target, tmp_path / "verified", save_verified_artifact=False)
    assert result.is_proven and len(synth.requests) == 1
    assert tool.calls[0][0] == tool.calls[1][0]
    assert [timeout for _, timeout in tool.calls] == [10, 15]
    assert result.diagnostics[0]["failure_kind"] == "compiler_timeout"
    assert result.diagnostics[1]["phase"] == "codex_synthesis_timeout_retry"


def test_pruned_retry_preserves_cancellation_and_never_spends_another_model_request(tmp_path, monkeypatch):
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [124, "cancel"])
    with pytest.raises(InterruptedError):
        prover.prove_challenge(target, tmp_path / "verified", save_verified_artifact=False)
    assert len(synth.requests) == 1 and len(tool.calls) == 2


def test_fully_consumed_target_budget_does_not_launch_retry_or_repair(tmp_path, monkeypatch):
    import autonomous_math.prover.lean_prover as module

    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    prover, target, _, tool, synth = fixture_prover(tmp_path, monkeypatch, [124], budget=8, clock=clock)
    result = prover.prove_challenge(target, tmp_path / "verified", save_verified_artifact=False)
    assert not result.is_proven and len(tool.calls) == len(synth.requests) == 1
    assert tool.calls[0][1] == 8
    assert not result.synthesis_attempts[0]["compiler_retry"]


def diagnostic(raw_line, target_line, error_count=2, phase="codex_synthesis", kind="compiler_rejection"):
    return {"phase": phase, "failure_kind": kind, "error_count": error_count,
            "first_error_line": raw_line, "first_target_error_line": target_line}


def test_context_growth_alone_cannot_admit_third_model_request():
    assert not LeanProofSearch._repair_progress([diagnostic(40, 10), diagnostic(500, 10)])


def test_real_target_progress_survives_pruning_that_reduces_raw_line_numbers():
    assert LeanProofSearch._repair_progress([diagnostic(500, 10), diagnostic(40, 20)])


def test_error_outside_target_and_compiler_timeout_do_not_count_as_progress():
    assert not LeanProofSearch._repair_progress([diagnostic(500, 10), diagnostic(700, None)])
    assert not LeanProofSearch._repair_progress([diagnostic(500, 10), diagnostic(550, 20, kind="compiler_timeout")])


def test_legacy_progress_diagnostics_still_work_without_target_relative_fields():
    before, after = diagnostic(20, 10), diagnostic(30, 20)
    before.pop("first_target_error_line")
    after.pop("first_target_error_line")
    assert LeanProofSearch._repair_progress([before, after])
