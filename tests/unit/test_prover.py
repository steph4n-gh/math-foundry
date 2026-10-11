"""Comprehensive Unit Test Suite for Milestone 3 Prover-Skeptic Engine.

Tests all 5 core modules:
1. LemmaDAG architecture (Feature 8)
2. AxiomLibrary retrieval & representations (Feature 9)
3. DeductiveInferenceEngine Z3 SMT leap validation (Feature 10)
4. AdversarialSkeptic circularity, hypothesis leaks, & edge cases (Feature 11)
5. ProverSkepticSearch AO* proof loop, backtracking, & ProofResult (Feature 12)
"""

from __future__ import annotations

import json
import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    InvariantNode,
)
from autonomous_math.prover.axioms import AxiomLibrary
from autonomous_math.prover.dag import DeductionStep, LemmaDAG, ProofNode
from autonomous_math.prover.inference import (
    DeductiveInferenceEngine,
    LeapValidationResult,
)
from autonomous_math.prover.search import ProofResult, ProverSkepticSearch
from autonomous_math.prover.skeptic import AdversarialSkeptic


# ============================================================================
# 1. LEMMA DAG ARCHITECTURE (FEATURE 8)
# ============================================================================

class TestLemmaDAGArchitecture:
    """Unit tests for ProofNode, DeductionStep, and LemmaDAG."""

    def test_proof_node_creation_and_defaults(self):
        node = ProofNode(
            node_id="n1",
            label="chi <= Delta + 1",
            statement_latex=r"\chi \le \Delta + 1",
            statement_lean="chi <= Delta + 1",
            node_type="TARGET_CONJECTURE",
        )
        assert node.node_id == "n1"
        assert node.node_type == "TARGET_CONJECTURE"
        assert node.confidence_score == 1.0
        assert node.is_proven is False
        assert node.scope == {"assumptions": []}

    def test_deduction_step_creation_and_flags(self):
        step = DeductionStep(
            step_id="s1",
            target_node_id="target",
            premise_node_ids=["p1", "p2"],
            rule_type="INEQUALITY_CHAIN",
            rule_name="Transitivity",
            justification="Transitivity step",
        )
        assert step.step_id == "s1"
        assert step.premise_node_ids == ["p1", "p2"]
        assert step.z3_verified is False
        assert step.skeptic_approved is False

    def test_lemma_dag_node_and_step_management(self):
        dag = LemmaDAG(root_node_id="root")
        n1 = ProofNode(node_id="root", label="Root", statement_latex="R", statement_lean="R", node_type="TARGET_CONJECTURE")
        n2 = ProofNode(node_id="p1", label="P1", statement_latex="P", statement_lean="P", node_type="AXIOM")
        dag.add_node(n1)
        dag.add_node(n2)

        assert dag.get_node("root") == n1
        assert dag.get_node("p1") == n2
        assert dag.get_node("non_existent") is None

        step = DeductionStep(
            step_id="step1",
            target_node_id="root",
            premise_node_ids=["p1"],
            rule_type="AXIOM_APPLICATION",
            rule_name="Axiom",
            justification="Root from P1",
        )
        dag.add_step(step)
        assert dag.get_step("step1") == step
        assert "p1" in dag.get_antecedents("root")

    def test_topological_sort_soundness(self):
        dag = LemmaDAG(root_node_id="target_bound")
        dag.add_node(ProofNode(node_id="target_bound", label="Target", statement_latex="T", statement_lean="T", node_type="TARGET_CONJECTURE"))
        dag.add_node(ProofNode(node_id="axiom_greedy", label="Axiom", statement_latex="A", statement_lean="A", node_type="AXIOM"))
        dag.add_node(ProofNode(node_id="lemma_greedy_bound", label="Lemma", statement_latex="L", statement_lean="L", node_type="SUB_LEMMA"))

        step = DeductionStep(
            step_id="step_transitivity",
            target_node_id="target_bound",
            premise_node_ids=["axiom_greedy", "lemma_greedy_bound"],
            rule_type="INEQUALITY_CHAIN",
            rule_name="Transitivity",
            justification="Combining greedy bounds",
        )
        dag.add_step(step)

        topo = dag.topological_sort()
        assert "target_bound" in topo
        assert "axiom_greedy" in topo
        assert "lemma_greedy_bound" in topo
        # Premises must precede target in topological order
        assert topo.index("axiom_greedy") < topo.index("target_bound")
        assert topo.index("lemma_greedy_bound") < topo.index("target_bound")

    def test_cycle_detection(self):
        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="B", label="B", statement_latex="B", statement_lean="B", node_type="SUB_LEMMA"))
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"], rule_type="STEP", rule_name="S1", justification="J1"))
        assert dag.has_cycle() is False

        # Add cyclic edge B -> A
        dag.add_step(DeductionStep(step_id="s2", target_node_id="A", premise_node_ids=["B"], rule_type="STEP", rule_name="S2", justification="J2"))
        assert dag.has_cycle() is True

    def test_would_create_cycle(self):
        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="B", label="B", statement_latex="B", statement_lean="B", node_type="SUB_LEMMA"))
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"], rule_type="STEP", rule_name="S1", justification="J1"))

        candidate = DeductionStep(step_id="s2", target_node_id="A", premise_node_ids=["B"], rule_type="STEP", rule_name="S2", justification="J2")
        assert dag.would_create_cycle(candidate) is True

    def test_serialization_roundtrip(self):
        dag = LemmaDAG(root_node_id="root")
        dag.add_node(ProofNode(node_id="root", label="R", statement_latex="R", statement_lean="R", node_type="TARGET_CONJECTURE"))
        d = dag.to_dict()
        reconstructed = LemmaDAG.from_dict(d)
        assert reconstructed.root_node_id == dag.root_node_id
        assert "root" in reconstructed.nodes

    def test_to_tikz_rendering(self):
        dag = LemmaDAG(root_node_id="target")
        dag.add_node(ProofNode(node_id="target", label="chi <= Delta + 1", statement_latex=r"\chi \le \Delta + 1", statement_lean="chi <= Delta + 1", node_type="TARGET_CONJECTURE"))
        dag.add_node(ProofNode(node_id="ax", label="Greedy", statement_latex=r"\chi \le Greedy", statement_lean="chi <= greedy", node_type="AXIOM"))
        dag.add_step(DeductionStep(step_id="s1", target_node_id="target", premise_node_ids=["ax"], rule_type="AXIOM_APPLICATION", rule_name="Greedy"))

        tikz = dag.to_tikz()
        assert r"\begin{tikzpicture}" in tikz
        assert r"\end{tikzpicture}" in tikz
        assert "target" in tikz
        assert "ax" in tikz


# ============================================================================
# 2. AXIOM LIBRARY (FEATURE 9)
# ============================================================================

class TestAxiomLibrary:
    """Unit tests for AxiomLibrary enumeration and retrieval."""

    def test_axiom_enumeration_completeness(self):
        lib = AxiomLibrary()
        axioms = lib.list_axioms()
        assert isinstance(axioms, list)
        assert len(axioms) >= 8

        expected_subset = ["handshaking_lemma", "greedy_coloring_bound", "turan_theorem", "brooks_theorem", "caro_wei_theorem"]
        for expected in expected_subset:
            assert any(expected in ax.lower() for ax in axioms), f"Missing {expected}"

    def test_axiom_retrieval_and_node_structure(self):
        lib = AxiomLibrary()
        node = lib.get_axiom("greedy_coloring_bound")
        assert node is not None
        assert isinstance(node, ProofNode)
        assert node.node_type == "AXIOM"
        assert node.is_proven is True
        assert node.confidence_score == 1.0
        assert len(node.statement_latex) > 0
        assert len(node.statement_lean) > 0

    def test_unknown_axiom_returns_none(self):
        lib = AxiomLibrary()
        node = lib.get_axiom("completely_fictional_axiom_xyz")
        assert node is None

    def test_alias_resolution(self):
        lib = AxiomLibrary()
        assert lib.has_axiom("brooks") is True
        node = lib.get_axiom("brooks")
        assert node is not None
        assert node.node_id == "brooks_theorem"

    def test_lean_and_comparator_export(self):
        lib = AxiomLibrary()
        for ax_id in ["handshaking_lemma", "greedy_coloring_bound", "turan_theorem"]:
            lean_src = lib.get_lean_template(ax_id)
            assert "import Mathlib" in lean_src
            assert "namespace OAI" in lean_src
            assert "sorry" in lean_src

            comp_json = lib.get_comparator_json(ax_id)
            assert "challenge_module" in comp_json
            assert "theorem_names" in comp_json
            assert "permitted_axioms" in comp_json


# ============================================================================
# 3. DEDUCTIVE INFERENCE ENGINE (FEATURE 10)
# ============================================================================

class TestDeductiveInferenceEngine:
    """Unit tests for Z3 Real SMT deductive leap validation."""

    def test_sound_inequality_transitivity_leap(self):
        engine = DeductiveInferenceEngine()
        res = engine.verify_inequality_leap(
            premises=["n >= 1", "alpha >= 1", "chi >= n / alpha", "alpha <= 3"],
            conclusion="chi >= n / 3",
        )
        assert isinstance(res, LeapValidationResult)
        assert res.is_valid is True
        assert res.counter_model is None

    def test_sound_two_step_inequality_chain(self):
        engine = DeductiveInferenceEngine()
        res = engine.verify_inequality_leap(
            premises=["chi <= greedy", "greedy <= Delta + 1"],
            conclusion="chi <= Delta + 1",
        )
        assert res.is_valid is True

    def test_non_sequitur_detection_with_counter_model(self):
        engine = DeductiveInferenceEngine()
        res = engine.verify_inequality_leap(
            premises=["alpha <= 3"],
            conclusion="chi <= 3",
        )
        assert res.is_valid is False
        assert res.counter_model is not None

    def test_inequality_reversal_detection(self):
        engine = DeductiveInferenceEngine()
        res = engine.verify_inequality_leap(
            premises=["x <= 5"],
            conclusion="x >= 5",
        )
        assert res.is_valid is False
        assert res.counter_model is not None

    def test_normalize_string(self):
        engine = DeductiveInferenceEngine()
        s = r"\chi(G) \le \Delta(G) + 1"
        norm = engine.normalize_string(s)
        assert "<=" in norm
        assert "chi" in norm
        assert "Delta" in norm


# ============================================================================
# 4. ADVERSARIAL SKEPTIC (FEATURE 11)
# ============================================================================

class TestAdversarialSkeptic:
    """Unit tests for circularity, hypothesis leaks, and edge cases."""

    def test_audit_step_rejects_circular_step(self):
        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="B", label="B", statement_latex="B", statement_lean="B", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="C", label="C", statement_latex="C", statement_lean="C", node_type="SUB_LEMMA"))
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"], rule_type="STEP", rule_name="S1", justification="A->B"))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="C", premise_node_ids=["B"], rule_type="STEP", rule_name="S2", justification="B->C"))

        skeptic = AdversarialSkeptic()
        cyclic_step = DeductionStep(
            step_id="s3_circular",
            target_node_id="A",
            premise_node_ids=["C"],
            rule_type="STEP",
            rule_name="Cycle",
            justification="C->A",
        )
        approved, critique = skeptic.audit_step(dag, cyclic_step)
        assert approved is False
        assert critique is not None
        assert "circular" in critique.lower() or "cycle" in critique.lower()

    def test_check_hypothesis_leak_detects_scope_leak(self):
        skeptic = AdversarialSkeptic()
        premise = ProofNode(
            node_id="prem_bipartite",
            label="Bipartite chi <= 2",
            statement_latex=r"\chi \le 2",
            statement_lean="chi <= 2",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["is_bipartite"]},
        )
        target = ProofNode(
            node_id="target_unconstrained",
            label="All graphs chi <= 2",
            statement_latex=r"\chi \le 2",
            statement_lean="chi <= 2",
            node_type="TARGET_CONJECTURE",
            scope={"assumptions": []},
        )
        step = DeductionStep(
            step_id="leak_step",
            target_node_id="target_unconstrained",
            premise_node_ids=["prem_bipartite"],
            rule_type="SUBSTITUTION",
            rule_name="Leak",
            justification="Generalizing assumption",
        )

        has_leak, critique = skeptic.check_hypothesis_leak(step, [premise], target)
        assert has_leak is True or "leak" in (critique or "").lower()

    def test_check_hypothesis_leak_approves_safe_scope(self):
        skeptic = AdversarialSkeptic()
        premise = ProofNode(
            node_id="prem_general",
            label="General graph bound",
            statement_latex="A",
            statement_lean="A",
            node_type="AXIOM",
            scope={"assumptions": []},
        )
        target = ProofNode(
            node_id="target_bipartite",
            label="Bipartite target",
            statement_latex="A",
            statement_lean="A",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["is_bipartite"]},
        )
        step = DeductionStep(
            step_id="safe_step",
            target_node_id="target_bipartite",
            premise_node_ids=["prem_general"],
            rule_type="INSTANTIATION",
            rule_name="Safe",
            justification="Specializing general theorem",
        )
        has_leak, critique = skeptic.check_hypothesis_leak(step, [premise], target)
        assert has_leak is False

    def test_edge_case_stress_brooks_odd_cycle_exception(self):
        c5 = nx.cycle_graph(5)
        skeptic = AdversarialSkeptic()
        step = DeductionStep(
            step_id="naive_brooks",
            target_node_id="target",
            premise_node_ids=["prem"],
            rule_type="AXIOM_APPLICATION",
            rule_name="NaiveBrooks",
            justification="chi <= Delta without cycle exclusion",
        )
        has_counter, critique = skeptic.check_edge_cases(step, test_graphs=[c5])
        assert has_counter is True or "odd cycle" in (critique or "").lower() or "c5" in (critique or "").lower()


# ============================================================================
# 5. PROVER-SKEPTIC SEARCH ENGINE (FEATURE 12)
# ============================================================================

class TestProverSkepticSearch:
    """Unit tests for AO* proof loop, ProofResult, and minimal proof tree synthesis."""

    def test_proof_result_model_and_dict_serialization(self):
        conj = Conjecture(
            id="c1", statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"), rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3
        )
        dag = LemmaDAG(root_node_id="root")
        step = DeductionStep(
            step_id="s1", target_node_id="root", premise_node_ids=[],
            rule_type="AXIOM", rule_name="Test", justification="Just",
            z3_verified=True, skeptic_approved=True
        )
        res = ProofResult(
            status="PROVEN",
            conjecture=conj,
            minimal_proof_tree=[step],
            dag=dag,
            critique_summary={"audited_steps": 1, "approved_steps": 1, "rejected_steps": 0},
        )
        assert res.is_proven is True
        assert res.is_unproven is False
        assert res.is_refuted is False

        d = res.to_dict()
        assert d["status"] == "PROVEN"
        assert len(d["minimal_proof_tree"]) == 1

        reconstructed = ProofResult.from_dict(d)
        assert reconstructed.status == "PROVEN"
        assert reconstructed.conjecture.id == conj.id

    def test_prove_greedy_coloring_bound(self):
        conj = Conjecture(
            id="conj_greedy_bound",
            statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )
        prover = ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=4)

        assert proof_res.status == "PROVEN"
        assert proof_res.is_proven is True
        assert len(proof_res.minimal_proof_tree) > 0
        assert proof_res.dag is not None

        for step in proof_res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True

        topo = proof_res.dag.topological_sort()
        assert "target_bound" in topo
        assert "axiom_greedy" in topo
        assert topo.index("axiom_greedy") < topo.index("target_bound")

    def test_prove_caro_wei_bound(self):
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
        prover = ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=5)

        assert proof_res.status == "PROVEN"
        assert len(proof_res.minimal_proof_tree) > 0
        assert any("caro_wei" in s.step_id.lower() for s in proof_res.minimal_proof_tree)

    def test_prove_clique_chromatic_bound(self):
        conj = Conjecture(
            id="chi_ge_omega",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        prover = ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=4)

        assert proof_res.status == "PROVEN"
        assert len(proof_res.minimal_proof_tree) > 0

    def test_critique_driven_backtracking_logs(self):
        conj = Conjecture(
            id="backtrack_test_bound",
            statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )
        prover = ProverSkepticSearch()
        proof_res = prover.prove(conj, max_depth=5)

        summary = proof_res.critique_summary
        assert isinstance(summary, dict)
        assert summary.get("audited_steps", 0) >= 1
        for step in proof_res.minimal_proof_tree:
            assert step.skeptic_approved is True
            assert step.z3_verified is True

    def test_unproven_conjecture_handling(self):
        open_conj = Conjecture(
            id="open_hadwiger_k7",
            statement="Hadwiger conjecture for k=7",
            lhs_expr=ConstantNode(7.0),
            rel="<=",
            rhs_expr=ConstantNode(7.0),
            complexity=5,
        )
        prover = ProverSkepticSearch()
        proof_res = prover.prove(open_conj, max_depth=2)

        assert proof_res.status == "UNPROVEN"
        assert proof_res.is_unproven is True
        assert proof_res.minimal_proof_tree == []
        assert "Search depth exhausted" in proof_res.critique_summary.get("reason", "")
