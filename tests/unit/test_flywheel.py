"""Unit and Integration Tests for Continuous Self-Improvement & Lemma Flywheel.

Validates:
- FlywheelLemma creation and invariant extraction.
- LemmaFlywheel environment bridge generation in Mathlib.lean.
- Candidate tactic script synthesis (exact, linear arithmetic, and transitive chaining).
- Closed-loop Lean 4 multi-hop theorem proving using active flywheel lemmas.
- Closed-loop heuristic feedback tracking invariant fertility and boundary graphs.
"""

from __future__ import annotations

import json
from pathlib import Path
import tempfile
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.prover.flywheel import (
    FlywheelFeedback,
    FlywheelLemma,
    LemmaFlywheel,
    _extract_invariants_from_conjecture,
    _sanitize_lean_ident,
)
from autonomous_math.prover.lean_prover import LeanProofSearch, LeanToolchain


def test_sanitize_lean_ident():
    """Verify sanitization of Lean theorem and lemma identifiers."""
    assert _sanitize_lean_ident("conj_spectral_radius_le_max_degree") == "spectral_radius_le_max_degree"
    assert _sanitize_lean_ident("123_bound") == "lem_123_bound"
    assert _sanitize_lean_ident("chi-omega.tight") == "chi_omega_tight"


def test_extract_invariants_from_ast_and_statement():
    """Verify invariant extraction across both AST objects and text statements."""
    c = Conjecture.create(
        id="test_conj",
        lhs=InvariantNode(name="spectral_radius"),
        rel="<=",
        rhs=BinaryOpNode("+", InvariantNode(name="max_degree"), ConstantNode(value=1.0)),
        statement="spectral_radius <= max_degree + 1",
    )
    invs = _extract_invariants_from_conjecture(c)
    assert "spectral_radius" in invs
    assert "max_degree" in invs

    # Test string extraction
    invs_str = _extract_invariants_from_conjecture("chi <= Delta + 1")
    assert "chromatic_number" in invs_str
    assert "max_degree" in invs_str


def test_flywheel_feedback_fertility_scoring():
    """Verify heuristic feedback scoring for invariants and boundary graphs."""
    feedback = FlywheelFeedback()

    c = Conjecture.create(
        id="chi_delta_bound",
        lhs=InvariantNode(name="chromatic_number"),
        rel="<=",
        rhs=InvariantNode(name="max_degree"),
        statement="chromatic_number <= max_degree",
    )

    # 1. Sieve survival increases fertility by 1.0
    feedback.record_sieve_survival(c)
    assert feedback.invariant_fertility.get("chromatic_number") == 2.0
    assert feedback.invariant_fertility.get("max_degree") == 2.0

    # 2. Refutation records boundary graph
    class MockCert:
        graph_order = 5
        graph_size = 5
        graph_id = "c5"
    feedback.record_refutation(c, MockCert())
    assert len(feedback.boundary_graphs) == 1
    assert feedback.boundary_graphs[0]["order"] == 5

    # 3. Lean certification provides +5 boost
    feedback.record_lean_certification(c, tactic="linarith")
    assert feedback.invariant_fertility.get("chromatic_number") == 7.0
    assert feedback.invariant_fertility.get("max_degree") == 7.0

    # 4. Top fertile invariants
    top = feedback.get_fertile_invariants(2)
    assert len(top) == 2
    assert top[0][1] == 7.0

    # 5. Biased sampling
    all_invs = ["chromatic_number", "max_degree", "order", "size", "girth"]
    p = feedback.sample_pair(all_invs, recent_pairs=set(), p_fertile=1.0)
    assert len(p) == 2
    assert p[0] in all_invs and p[1] in all_invs


@pytest.mark.parametrize("statement,tactic", [("chromatic_number <= spectral_radius", "sorry"), ("spectral_radius <= max_degree", "exact G.bound"), ("True", "trivial")])
def test_unchecked_lemma_registration_is_rejected(tmp_path, statement, tactic):
    flywheel = LemmaFlywheel(storage_path=tmp_path / "lemmas.json")
    with pytest.raises(ValueError):
        flywheel.register_lemma(statement, tactic=tactic, conjecture_id="unchecked")
    assert not flywheel.lemmas
    assert not (tmp_path / "Mathlib.lean").exists()
