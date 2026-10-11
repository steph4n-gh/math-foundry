"""Regression checks for fair search and useful finite-graph proof seeds."""
from pathlib import Path
import json
import pytest
from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, InvariantNode
from autonomous_math.prover.flywheel import LemmaFlywheel
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.prover.trusted_lean import bootstrap_candidates, goal_specific_tactics
from autonomous_math.research_state import ALLOWED_AXIOMS, validate_receipt


@pytest.fixture(scope="module")
def bounds(tmp_path_factory):
    directory = tmp_path_factory.mktemp("finite_graph_bounds")
    prover = LeanProofSearch(max_attempts=4, timeout_per_attempt=30)
    results = []
    for candidate in bootstrap_candidates():
        result = prover.prove_conjecture(candidate, output_dir=directory)
        assert result.is_proven, result.diagnostics
        results.append((candidate, result))
    return results


@pytest.mark.parametrize("index", range(3))
def test_foundational_bounds_are_kernel_checked_and_explained(bounds, index):
    candidate, result = bounds[index]
    receipt, error = validate_receipt(result.receipt_path, candidate.id)
    assert receipt and not error
    assert set(receipt["axioms"]) <= ALLOWED_AXIOMS
    assert result.attempts_count == 1
    assert candidate.metadata["novelty_status"] == "KNOWN_FOUNDATIONAL"
    assert "known" in candidate.metadata["writeup"].lower() or "familiar" in candidate.metadata["writeup"].lower()
    assert result.search_key == receipt["search_key"]


def test_four_attempt_budget_keeps_fresh_tactics_with_large_library():
    goal = Conjecture.create(id="new_target", lhs=InvariantNode("clique_number"), rel="<=", rhs=InvariantNode("max_degree"))
    receipts = [{"theorem_name": f"old_{index}"} for index in range(30)]
    scripts = LeanProofSearch(max_attempts=4).candidate_tactics(goal, receipts)
    assert len(scripts) == 4
    assert "positivity" in scripts and "simp" in scripts
    assert sum("have " in script for script in scripts) == 2


def test_matching_uses_ast_and_never_the_label():
    real = bootstrap_candidates()[0]
    renamed = real.model_copy(update={"id": "different_label", "statement": "unrelated text"})
    assert goal_specific_tactics(real) == goal_specific_tactics(renamed)
    false = real.model_copy(update={"rhs_expr": ConstantNode(0)})
    assert not goal_specific_tactics(false)
    scripts = LeanProofSearch(max_attempts=4).candidate_tactics(real, [{"theorem_name": f"old_{i}"} for i in range(20)])
    assert scripts[0] == goal_specific_tactics(real)[0]
    assert "positivity" in scripts


def test_search_key_changes_with_goal_budget_dependencies_and_checked_library(bounds, tmp_path, monkeypatch):
    import autonomous_math.research_state as state
    goal = Conjecture.create(id="heldout", lhs=InvariantNode("clique_number"), rel="<=", rhs=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(2)))
    flywheel = LemmaFlywheel(storage_path=tmp_path / "lemmas.json")
    prover = LeanProofSearch(flywheel=flywheel, max_attempts=4, timeout_per_attempt=30)
    first = prover.search_key(goal)
    assert prover.search_key(goal) == first
    assert prover.search_key(goal.model_copy(update={"id": "renamed", "metadata": {"label": "changed"}})) == first
    assert prover.search_key(goal.model_copy(update={"rhs_expr": ConstantNode(2)})) != first
    prover.timeout_per_attempt = 29
    assert prover.search_key(goal) != first
    prover.timeout_per_attempt = 30
    prover.max_attempts = 3
    assert prover.search_key(goal) != first
    prover.max_attempts = 4
    candidate, result = bounds[1]
    flywheel.register_lemma(candidate, result.successful_tactic, receipt_path=result.receipt_path)
    learned = prover.search_key(goal)
    assert learned != first
    monkeypatch.setattr(state, "workspace_fingerprint", lambda _: "changed-dependencies")
    assert prover.search_key(goal) != learned


def test_polynomial_consequences_use_new_checked_library(bounds, tmp_path):
    flywheel = LemmaFlywheel(storage_path=tmp_path / "lemmas.json")
    for candidate, result in bounds:
        flywheel.register_lemma(candidate, result.successful_tactic, receipt_path=result.receipt_path)
    n, m, delta, omega = map(InvariantNode, ("order", "size", "max_degree", "clique_number"))
    goals = [
        Conjecture.create(id="more_degree_density", lhs=BinaryOpNode("*", ConstantNode(2), m), rel="<=", rhs=BinaryOpNode("*", n, BinaryOpNode("+", delta, ConstantNode(1)))),
        Conjecture.create(id="looser_clique_degree", lhs=omega, rel="<=", rhs=BinaryOpNode("+", delta, ConstantNode(2))),
        Conjecture.create(id="composed_clique_density", lhs=BinaryOpNode("*", omega, BinaryOpNode("-", omega, ConstantNode(1))), rel="<=", rhs=BinaryOpNode("*", n, delta)),
    ]
    for goal in goals:
        result = LeanProofSearch(flywheel=flywheel, max_attempts=4, timeout_per_attempt=30).prove_conjecture(goal, output_dir=tmp_path / "verified")
        assert result.is_proven, result.diagnostics
        assert "have " in result.successful_tactic
        assert result.attempts_count == 1
