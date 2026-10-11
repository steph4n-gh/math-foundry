"""Adversarial stress-test suite for Milestone 3 Prover-Skeptic Engine.

Authored by empirical challenger challenger_m3_2 to stress-test:
1. DeductiveInferenceEngine & SMT Leap Verification:
   - LaTeX fraction parsing (simple, nested, multi-variable).
   - Multi-variable systems and transitive/linear chains.
   - Division by variables (constrained vs unconstrained denominators).
   - Contradictory premises (ex falso quodlibet).
   - Counter-model extraction on non-sequiturs with genuine numerical validation.
2. ProverSkepticSearch AO* Search Loop:
   - Proof synthesis on greedy bound, Caro-Wei bound, clique-chromatic bound.
   - Search depth budget exhaustion on open/unprovable conjectures (Hadwiger k=7).
   - Critique-driven backtracking (pruning rejected branches, verifying approved steps only).
3. AdversarialSkeptic Multi-Tier Auditing:
   - Multi-hop circularity detection.
   - Fine-grained hypothesis scope leak detection.
"""

from __future__ import annotations

import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
)
from autonomous_math.prover.dag import DeductionStep, LemmaDAG, ProofNode
from autonomous_math.prover.inference import (
    DeductiveInferenceEngine,
    LeapValidationResult,
)
from autonomous_math.prover.search import ProofResult, ProverSkepticSearch
from autonomous_math.prover.skeptic import AdversarialSkeptic


# ============================================================================
# 1. SMT LEAP VERIFICATION ADVERSARIAL STRESS TESTS
# ============================================================================

class TestSMTLeapVerificationAdversarial:
    """Stress tests DeductiveInferenceEngine on LaTeX fractions, variables, and models."""

    @pytest.fixture
    def engine(self):
        return DeductiveInferenceEngine(timeout_ms=5000)

    def test_latex_fraction_parsing_simple_and_nested(self, engine):
        """Verify parsing of LaTeX fractions including nested fractions."""
        # Simple fraction: \chi \ge \frac{n}{\alpha} with \alpha \le 2 ==> \chi \ge \frac{n}{2}
        res_simple = engine.verify_inequality_leap(
            premises=[r"\alpha \ge 1", r"n \ge 2", r"\chi \ge \frac{n}{\alpha}", r"\alpha \le 2"],
            conclusion=r"\chi \ge \frac{n}{2}",
        )
        assert res_simple.is_valid is True
        assert res_simple.counter_model is None

        # Nested fraction: x \ge \frac{\frac{a}{b}}{c}
        res_nested = engine.verify_inequality_leap(
            premises=[
                r"x \ge \frac{\frac{a}{b}}{c}",
                r"a \ge 12",
                r"b \le 2",
                r"b > 0",
                r"c \le 3",
                r"c > 0",
            ],
            conclusion=r"x \ge 2",
        )
        assert res_nested.is_valid is True

    def test_multivariable_inequality_transitive_system(self, engine):
        """Stress-test multi-variable transitivity chain with 6 variables."""
        chain_premises = [
            "x1 <= x2",
            "x2 <= x3",
            "x3 <= x4",
            "x4 <= x5",
            "x5 <= x6",
        ]
        res = engine.verify_inequality_leap(premises=chain_premises, conclusion="x1 <= x6")
        assert res.is_valid is True

        # Non-sequitur branch: x1 <= x6 does NOT imply x6 <= x1
        res_rev = engine.verify_inequality_leap(premises=chain_premises, conclusion="x6 <= x1")
        assert res_rev.is_valid is False
        assert res_rev.counter_model is not None

    def test_multivariable_linear_combination_arithmetic(self, engine):
        """Verify linear inequality arithmetic with fractions."""
        premises = [
            "2 * a + 3 * b >= 12",
            "a <= 3",
        ]
        # 3 * b >= 12 - 2 * 3 = 6 ==> b >= 2
        res_sound = engine.verify_inequality_leap(premises=premises, conclusion="b >= 2")
        assert res_sound.is_valid is True

        # False leap: b >= 3
        res_false = engine.verify_inequality_leap(premises=premises, conclusion="b >= 3")
        assert res_false.is_valid is False
        assert res_false.counter_model is not None
        # Check counter-model genuinely violates b >= 3
        b_val = res_false.counter_model["b"]
        assert b_val < 3

    def test_division_by_variables_constrained_vs_unconstrained(self, engine):
        """Test division by variables when denominator is strictly positive vs unconstrained."""
        # Constrained denominator: alpha > 0
        res_constrained = engine.verify_inequality_leap(
            premises=["n >= 10", "alpha > 0", "alpha <= 2", "chi >= n / alpha"],
            conclusion="chi >= 5",
        )
        assert res_constrained.is_valid is True

        # Unconstrained denominator: alpha can be negative or 0
        res_unconstrained = engine.verify_inequality_leap(
            premises=["n >= 10", "alpha <= 2", "chi >= n / alpha"],
            conclusion="chi >= 5",
        )
        assert res_unconstrained.is_valid is False
        assert res_unconstrained.counter_model is not None
        # Genuine numeric counter-example exists
        assert "alpha" in res_unconstrained.counter_model

    def test_contradictory_premises_ex_falso_quodlibet(self, engine):
        """Contradictory premises (x > 5 and x < 2) render premises unsat, so conclusion is vacuously sound."""
        res = engine.verify_inequality_leap(
            premises=["x > 5", "x < 2"],
            conclusion="chi <= -999",
        )
        assert res.is_valid is True
        assert res.counter_model is None
        assert "Unsat" in (res.details or "")

    def test_counter_model_extraction_genuine_numerical_assignments(self, engine):
        """Verify that counter-models contain authentic numeric valuations satisfying premises and violating conclusion."""
        premises = ["x >= 5", "y <= 2", "z >= 1"]
        conclusion = "x + y + z <= 6"

        res = engine.verify_inequality_leap(premises=premises, conclusion=conclusion)
        assert res.is_valid is False
        assert res.counter_model is not None

        model = res.counter_model
        assert "x" in model and "y" in model and "z" in model
        # Values must be int or float
        for k, v in model.items():
            assert isinstance(v, (int, float)), f"Variable {k} valuation {v} is not a genuine number"

        x, y, z = model["x"], model["y"], model["z"]
        # Verify premises hold under counter-model
        assert x >= 5
        assert y <= 2
        assert z >= 1
        # Verify conclusion fails under counter-model
        assert not (x + y + z <= 6)


# ============================================================================
# 2. PROVER-SKEPTIC SEARCH ENGINE AO* ADVERSARIAL STRESS TESTS
# ============================================================================

class TestProverSkepticSearchAdversarial:
    """Stress tests ProverSkepticSearch proof synthesis, budget exhaustion, and backtracking."""

    @pytest.fixture
    def prover(self):
        return ProverSkepticSearch()

    def test_proof_synthesis_greedy_bound(self, prover):
        """Synthesize greedy coloring bound: chi <= Delta + 1."""
        conj = Conjecture(
            id="conj_greedy_bound",
            statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )
        res = prover.prove(conj, max_depth=4)
        assert res.status == "PROVEN"
        assert res.is_proven is True
        assert len(res.minimal_proof_tree) > 0

        # Verify all steps in minimal proof tree are approved and verified
        for step in res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True
            assert step.is_verified is True

        # Verify topological sort
        topo = res.dag.topological_sort()
        assert "target_bound" in topo
        assert "axiom_greedy" in topo
        assert topo.index("axiom_greedy") < topo.index("target_bound")

    def test_proof_synthesis_caro_wei_bound(self, prover):
        """Synthesize Caro-Wei bound: alpha >= n / (Delta + 1)."""
        denom = BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0))
        rhs = BinaryOpNode("/", InvariantNode("order"), denom)
        conj = Conjecture(
            id="caro_wei_bound",
            statement="alpha >= n / (Delta + 1)",
            lhs_expr=InvariantNode("independence_number"),
            rel=">=",
            rhs_expr=rhs,
            complexity=4,
        )
        res = prover.prove(conj, max_depth=5)
        assert res.status == "PROVEN"
        assert res.is_proven is True
        assert len(res.minimal_proof_tree) >= 1
        for step in res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True

    def test_proof_synthesis_clique_chromatic_bound(self, prover):
        """Synthesize clique-chromatic bound: chi >= omega."""
        conj = Conjecture(
            id="chi_ge_omega",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        res = prover.prove(conj, max_depth=4)
        assert res.status == "PROVEN"
        assert res.is_proven is True
        assert len(res.minimal_proof_tree) >= 1
        for step in res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True

    def test_search_depth_budget_exhaustion_on_unprovable_conjectures(self, prover):
        """Test search depth budget exhaustion on open Hadwiger conjecture (k=7)."""
        open_conj = Conjecture(
            id="hadwiger_k7",
            statement="Hadwiger conjecture for k=7: every graph with chi >= 7 has K7 minor",
            lhs_expr=ConstantNode(7.0),
            rel="<=",
            rhs_expr=ConstantNode(7.0),
            complexity=5,
        )
        for depth in [0, 1, 2]:
            res = prover.prove(open_conj, max_depth=depth)
            assert res.status == "UNPROVEN"
            assert res.is_unproven is True
            assert res.minimal_proof_tree == []
            assert "Search depth exhausted" in res.critique_summary.get("reason", "")

    def test_critique_driven_backtracking_prunes_rejected_steps(self, prover):
        """Verify critique-driven backtracking prunes naive Brooks bound and approves sound path."""
        conj = Conjecture(
            id="greedy_bound",
            statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )
        res = prover.prove(conj, max_depth=5)
        summary = res.critique_summary

        # Naive Brooks step was audited and rejected
        assert summary["audited_steps"] >= 2
        assert summary["rejected_steps"] >= 1
        assert any(c["step_id"] == "step_naive_brooks" for c in summary["critiques"])
        assert any("odd cycle" in c["critique"].lower() for c in summary["critiques"])

        # Minimal proof tree MUST NOT contain the rejected step
        step_ids = [s.step_id for s in res.minimal_proof_tree]
        assert "step_naive_brooks" not in step_ids
        assert "step_transitivity" in step_ids

        # Every step in minimal proof tree has skeptic_approved == True and z3_verified == True
        for step in res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True


# ============================================================================
# 3. ADVERSARIAL SKEPTIC MULTI-TIER AUDIT STRESS TESTS
# ============================================================================

class TestAdversarialSkepticMultiTier:
    """Stress tests AdversarialSkeptic on circularities and hypothesis leaks."""

    @pytest.fixture
    def skeptic(self):
        return AdversarialSkeptic()

    def test_multi_hop_cycle_detection(self, skeptic):
        """Detect multi-hop directed cycle: N1 -> N2 -> N3 -> N4 -> N1."""
        dag = LemmaDAG(root_node_id="N1")
        for i in range(1, 5):
            dag.add_node(ProofNode(node_id=f"N{i}", label=f"N{i}", statement_latex=f"N{i}", statement_lean=f"N{i}"))

        dag.add_step(DeductionStep(step_id="s1", target_node_id="N2", premise_node_ids=["N1"], rule_type="STEP"))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="N3", premise_node_ids=["N2"], rule_type="STEP"))
        dag.add_step(DeductionStep(step_id="s3", target_node_id="N4", premise_node_ids=["N3"], rule_type="STEP"))

        cyclic_step = DeductionStep(
            step_id="s4_closing_cycle",
            target_node_id="N1",
            premise_node_ids=["N4"],
            rule_type="STEP",
        )
        approved, critique = skeptic.audit_step(dag, cyclic_step)
        assert approved is False
        assert "circular" in critique.lower() or "cycle" in critique.lower()

    def test_hypothesis_leak_multiple_missing_assumptions(self, skeptic):
        """Detect multiple missing local assumptions between premise and target scopes."""
        premise = ProofNode(
            node_id="prem_constrained",
            label="Planar and bipartite bound",
            statement_latex="chi <= 2",
            statement_lean="chi <= 2",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["is_planar", "is_bipartite", "girth >= 4"]},
        )
        target = ProofNode(
            node_id="target_only_planar",
            label="Planar bound",
            statement_latex="chi <= 2",
            statement_lean="chi <= 2",
            node_type="TARGET_CONJECTURE",
            scope={"assumptions": ["is_planar"]},
        )
        step = DeductionStep(
            step_id="leaky_step",
            target_node_id="target_only_planar",
            premise_node_ids=["prem_constrained"],
            rule_type="SUBSTITUTION",
        )
        has_leak, critique = skeptic.check_hypothesis_leak(step, [premise], target)
        assert has_leak is True
        assert "is_bipartite" in critique
        assert "girth >= 4" in critique
