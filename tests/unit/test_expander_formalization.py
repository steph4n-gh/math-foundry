"""Exact graph-code translation, conventions, and compatibility boundaries."""
import json
from pathlib import Path

import pytest

from autonomous_math.core.ast import Conjecture, GuardPredicate
from autonomous_math.prover.trusted_lean import (
    bootstrap_candidates, capability_report, expander_code_candidates,
    goal_specific_tactics, render_challenge,
)


ROOT = Path(__file__).resolve().parents[2]


def test_code_scalars_use_native_binary_kernel_and_hamming_weight():
    bridge = expander_code_candidates()[0]
    source, _ = render_challenge(bridge)
    assert "ZMod 2" in source and ".mulVecLin x = 0" in source
    assert "image hammingNorm" in source
    assert "S.Nonempty ∧ ¬ (∃ v w" in source
    assert "∀ u ∈ S, G.Adj v u → u = w" in source
    assert "{Fintype.card V + 1}" in source
    assert "weights.min'" in source and "- 1 : ℕ" in source
    assert source.count("theorem ") == 1
    assert source.count("open scoped BigOperators") == 1
    assert "h_guard" not in source
    assert "axiom " not in source and "def " not in source
    assert "Mathlib.Analysis.Matrix.Spectrum" not in source


def test_dimension_is_the_native_kernel_finrank():
    source, _ = render_challenge(expander_code_candidates()[1])
    assert "Module.finrank (ZMod 2) (LinearMap.ker" in source
    assert "Mathlib.LinearAlgebra.Dimension.Constructions" in source


def test_nonzero_code_guard_is_required_for_distance_at_most_length():
    target = expander_code_candidates()[2]
    source, _ = render_challenge(target)
    assert "h_guard" in source and "Module.finrank" in source
    assert goal_specific_tactics(target)
    unguarded = Conjecture.create(id="unguarded_false_code_bound", lhs=target.lhs_expr,
        rel=target.rel, rhs=target.rhs_expr)
    assert not goal_specific_tactics(unguarded)
    changed = Conjecture.create(id="different_premise", lhs=target.lhs_expr,
        rel=target.rel, rhs=target.rhs_expr,
        guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1))
    assert not goal_specific_tactics(changed)


def test_code_scope_exposes_finite_sentinel_and_separate_numeric_limit():
    metadata = capability_report()["code_semantics"]
    assert "n+1" in metadata["parity_code_distance"]
    assert "zero" in metadata["zero_code"]
    assert "16" in metadata["numerical_scope"]
    assert "all finite" in metadata["numerical_scope"]
    for candidate in expander_code_candidates():
        source, _ = render_challenge(candidate)
        assert "[Fintype V]" in source
        assert "≤ 16" not in source


def test_expander_foundations_are_separate_and_explained():
    ordinary = {c.id for c in bootstrap_candidates()}
    coding = expander_code_candidates()
    assert len(ordinary) == 3 and len(coding) == 4
    assert not ordinary.intersection(c.id for c in coding)
    assert all(c.metadata["novelty_status"] == "KNOWN_FOUNDATIONAL" for c in coding)
    assert all(len(c.metadata["writeup"].split()) >= 30 for c in coding)


@pytest.mark.parametrize("record", json.loads((ROOT / "library/catalog.json").read_text())["theorems"])
def test_existing_seven_theorem_sections_are_byte_identical(record):
    candidate = Conjecture.from_dict(record["conjecture"])
    actual, name = render_challenge(candidate)
    original = (ROOT / record["challenge"]).read_text()
    marker = f"theorem {name} "
    assert actual[actual.index(marker):] == original[original.index(marker):]
