"""Adversarial stress-test suite for Milestone 3 (Features 8-12).

Adversarially challenges:
1. LemmaDAG architecture, topological sort, circularity detection, arbitrary cyclic permutations,
   self-loops, disconnected DAGs, and multi-premise cycle anticipation.
2. AdversarialSkeptic hypothesis/scope leak detection with complex, multi-premise scopes and varied strings.
3. Pydantic serialization round-trips (ProofNode, DeductionStep, LemmaDAG) and LaTeX TikZ generation.
4. Documented edge-case vulnerabilities (KeyError on to_tikz() with cyclic graph, TypeError on None assumptions).
"""

from __future__ import annotations

import itertools
import json
import random
from typing import List
import networkx as nx
import pytest

from autonomous_math.prover.dag import DeductionStep, LemmaDAG, ProofNode
from autonomous_math.prover.skeptic import AdversarialSkeptic


# ============================================================================
# 1. LEMMA DAG CIRCULARITY & TOPOLOGICAL SORT CHALLENGES
# ============================================================================

class TestAdversarialLemmaDAGCircularityAndTopologicalSort:
    """Adversarially challenge cycle detection, would_create_cycle, and topological sort."""

    @pytest.mark.parametrize("cycle_len", [2, 3, 4, 5, 8, 12])
    def test_arbitrary_cyclic_permutations_n_cycles(self, cycle_len: int):
        """Test n-step cycles: v0 -> v1 -> ... -> v_{n-1} -> v0."""
        dag = LemmaDAG(root_node_id="v0")
        skeptic = AdversarialSkeptic()
        nodes = [f"v{i}" for i in range(cycle_len)]

        for v in nodes:
            dag.add_node(ProofNode(node_id=v, label=v, statement_latex=v, statement_lean=v))

        # Add forward chain: v0 -> v1 -> ... -> v_{n-1}
        for i in range(cycle_len - 1):
            step = DeductionStep(
                step_id=f"step_{i}",
                target_node_id=f"v{i+1}",
                premise_node_ids=[f"v{i}"],
                rule_name=f"Chain_{i}",
            )
            assert dag.would_create_cycle(step) is False
            dag.add_step(step)

        # Graph before closing edge MUST be acyclic
        assert dag.has_cycle() is False
        topo = dag.topological_sort()
        assert len(topo) == cycle_len
        for i in range(cycle_len - 1):
            assert topo.index(f"v{i}") < topo.index(f"v{i+1}")

        # Closing candidate step: v_{n-1} -> v0 (target is v0, premise is v_{n-1})
        closing_step = DeductionStep(
            step_id="step_closing_cycle",
            target_node_id="v0",
            premise_node_ids=[f"v{cycle_len-1}"],
            rule_name="CycleCloser",
        )

        # 1. would_create_cycle MUST anticipate the cycle
        assert dag.would_create_cycle(closing_step) is True

        # 2. Skeptic circularity check MUST detect the cycle
        has_cycle, critique = skeptic.check_circularity(dag, closing_step)
        assert has_cycle is True
        assert critique is not None
        assert "circular" in critique.lower() or "cycle" in critique.lower()

        # 3. Skeptic master audit MUST reject the step
        approved, audit_critique = skeptic.audit_step(dag, closing_step)
        assert approved is False
        assert closing_step.skeptic_approved is False

        # 4. If step is added, has_cycle() MUST be True
        dag.add_step(closing_step)
        assert dag.has_cycle() is True

        # 5. topological_sort MUST raise ValueError
        with pytest.raises(ValueError, match="contains a directed cycle"):
            dag.topological_sort()

    def test_all_24_permutations_of_4_cycle(self):
        """Adversarially evaluate all 4! = 24 cyclic permutations of nodes A, B, C, D."""
        node_names = ["A", "B", "C", "D"]
        all_perms = list(itertools.permutations(node_names))
        skeptic = AdversarialSkeptic()

        for perm in all_perms:
            dag = LemmaDAG(root_node_id=perm[0])
            for v in node_names:
                dag.add_node(ProofNode(node_id=v, label=v, statement_latex=v, statement_lean=v))

            # Add path perm[0] -> perm[1] -> perm[2] -> perm[3]
            for i in range(3):
                s = DeductionStep(
                    step_id=f"step_{i}",
                    target_node_id=perm[i+1],
                    premise_node_ids=[perm[i]],
                )
                assert dag.would_create_cycle(s) is False
                dag.add_step(s)

            # Closing step perm[3] -> perm[0]
            closing = DeductionStep(
                step_id="closing",
                target_node_id=perm[0],
                premise_node_ids=[perm[3]],
            )
            assert dag.would_create_cycle(closing) is True
            has_cycle, _ = skeptic.check_circularity(dag, closing)
            assert has_cycle is True

            dag.add_step(closing)
            assert dag.has_cycle() is True
            with pytest.raises(ValueError):
                dag.topological_sort()

    def test_self_loops_rejected_at_all_tiers(self):
        """Self-loops (A -> A) must be anticipated and rejected by would_create_cycle and skeptic."""
        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A"))
        skeptic = AdversarialSkeptic()

        self_step = DeductionStep(
            step_id="self_step",
            target_node_id="A",
            premise_node_ids=["A"],
            rule_name="SelfDerivation",
        )

        assert dag.would_create_cycle(self_step) is True
        has_cycle, critique = skeptic.check_circularity(dag, self_step)
        assert has_cycle is True
        assert "self-loop" in (critique or "").lower()

        approved, _ = skeptic.audit_step(dag, self_step)
        assert approved is False
        assert self_step.skeptic_approved is False

        # If forced into DAG
        dag.add_step(self_step)
        assert dag.has_cycle() is True
        with pytest.raises(ValueError):
            dag.topological_sort()

    def test_disconnected_dag_topological_sort_invariants(self):
        """Disconnected components and isolated nodes must be correctly ordered in topological sort."""
        dag = LemmaDAG(root_node_id="T")

        # Component 1: A -> B -> C
        # Component 2: X -> Y
        # Isolated nodes: I1, I2
        # Target: T derived from C and Y
        all_nodes = ["A", "B", "C", "X", "Y", "I1", "I2", "T"]
        for nid in all_nodes:
            dag.add_node(ProofNode(node_id=nid, label=nid, statement_latex=nid, statement_lean=nid))

        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"]))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="C", premise_node_ids=["B"]))
        dag.add_step(DeductionStep(step_id="s3", target_node_id="Y", premise_node_ids=["X"]))
        dag.add_step(DeductionStep(step_id="s4", target_node_id="T", premise_node_ids=["C", "Y"]))

        assert dag.has_cycle() is False
        topo = dag.topological_sort()

        # All nodes must be in topo sort
        assert set(topo) == set(all_nodes)
        assert len(topo) == len(all_nodes)

        # Strict ordering invariants
        assert topo.index("A") < topo.index("B") < topo.index("C")
        assert topo.index("X") < topo.index("Y")
        assert topo.index("C") < topo.index("T")
        assert topo.index("Y") < topo.index("T")

    def test_cycle_in_single_disconnected_component_invalidates_entire_dag(self):
        """A cycle in an auxiliary component must cause has_cycle=True and topological_sort to raise."""
        dag = LemmaDAG(root_node_id="T")
        for nid in ["A", "B", "X", "Y", "T"]:
            dag.add_node(ProofNode(node_id=nid, label=nid, statement_latex=nid, statement_lean=nid))

        # Sound component leading to target: A -> B -> T
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"]))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="T", premise_node_ids=["B"]))

        # Disconnected cyclic component: X -> Y -> X
        dag.add_step(DeductionStep(step_id="s3", target_node_id="Y", premise_node_ids=["X"]))
        dag.add_step(DeductionStep(step_id="s4", target_node_id="X", premise_node_ids=["Y"]))

        assert dag.has_cycle() is True
        with pytest.raises(ValueError):
            dag.topological_sort()

    def test_multi_premise_indirect_cycle_anticipation(self):
        """Test cycle anticipation when multi-premise step closes an indirect cycle."""
        dag = LemmaDAG(root_node_id="E")
        for nid in ["A", "B", "C", "D", "E"]:
            dag.add_node(ProofNode(node_id=nid, label=nid, statement_latex=nid, statement_lean=nid))

        # (A, B) -> C
        dag.add_step(DeductionStep(step_id="s1", target_node_id="C", premise_node_ids=["A", "B"]))
        # (C, D) -> E
        dag.add_step(DeductionStep(step_id="s2", target_node_id="E", premise_node_ids=["C", "D"]))

        skeptic = AdversarialSkeptic()

        # Closing candidate step: target is B, premises are [D, E]
        # Since B -> C -> E, adding E -> B creates B -> C -> E -> B cycle!
        closing = DeductionStep(
            step_id="s_close",
            target_node_id="B",
            premise_node_ids=["D", "E"],
        )

        assert dag.would_create_cycle(closing) is True
        has_cycle, critique = skeptic.check_circularity(dag, closing)
        assert has_cycle is True

    def test_stress_large_random_dag_50_nodes(self):
        """Generate a 50-node random DAG with ~120 edges and verify topological sort invariants and 50 back-edges."""
        random.seed(42)
        n = 50
        dag = LemmaDAG(root_node_id=f"node_{n-1}")
        for i in range(n):
            dag.add_node(ProofNode(node_id=f"node_{i}", label=f"Node {i}", statement_latex=f"N_{i}", statement_lean=f"n_{i}"))

        edges = []
        step_idx = 0
        for i in range(n):
            for j in range(i + 1, n):
                if random.random() < 0.1:  # 10% edge probability
                    step = DeductionStep(
                        step_id=f"step_{step_idx}",
                        target_node_id=f"node_{j}",
                        premise_node_ids=[f"node_{i}"],
                    )
                    assert dag.would_create_cycle(step) is False
                    dag.add_step(step)
                    edges.append((i, j))
                    step_idx += 1

        assert dag.has_cycle() is False
        topo = dag.topological_sort()
        assert len(topo) == n

        # Strict topological order invariant for all edges
        for i, j in edges:
            assert topo.index(f"node_{i}") < topo.index(f"node_{j}")

        # Adversarially test 50 back-edges (j -> i where i < j)
        skeptic = AdversarialSkeptic()
        for i, j in random.sample(edges, min(50, len(edges))):
            back_step = DeductionStep(
                step_id="back_step",
                target_node_id=f"node_{i}",
                premise_node_ids=[f"node_{j}"],
            )
            assert dag.would_create_cycle(back_step) is True
            has_cycle, _ = skeptic.check_circularity(dag, back_step)
            assert has_cycle is True

    def test_forward_shortcut_edges_do_not_create_cycle(self):
        """Legitimate forward edges (shortcuts) in a DAG must return would_create_cycle=False."""
        n = 15
        dag = LemmaDAG(root_node_id=f"node_{n-1}")
        for i in range(n):
            dag.add_node(ProofNode(node_id=f"node_{i}", label=f"Node {i}", statement_latex=f"N_{i}", statement_lean=f"n_{i}"))

        for i in range(n - 1):
            dag.add_step(DeductionStep(step_id=f"s_{i}", target_node_id=f"node_{i+1}", premise_node_ids=[f"node_{i}"]))

        # For all u < v - 1, forward shortcuts node_u -> node_v must NOT create a cycle
        for u in range(n):
            for v in range(u + 2, n):
                cand = DeductionStep(
                    step_id="forward_shortcut",
                    target_node_id=f"node_{v}",
                    premise_node_ids=[f"node_{u}"],
                )
                assert dag.would_create_cycle(cand) is False

    def test_candidate_step_with_new_unadded_nodes(self):
        """Candidate steps referencing new nodes not yet in DAG graph must not trigger false cycle alarms."""
        dag = LemmaDAG(root_node_id="root")
        dag.add_node(ProofNode(node_id="root", label="Root", statement_latex="R", statement_lean="R"))

        # Target exists, premise does not
        step1 = DeductionStep(step_id="s1", target_node_id="root", premise_node_ids=["brand_new_premise"])
        assert dag.would_create_cycle(step1) is False

        # Premise exists, target does not
        step2 = DeductionStep(step_id="s2", target_node_id="brand_new_target", premise_node_ids=["root"])
        assert dag.would_create_cycle(step2) is False

        # Neither exists
        step3 = DeductionStep(step_id="s3", target_node_id="brand_new_target_2", premise_node_ids=["brand_new_premise_2"])
        assert dag.would_create_cycle(step3) is False

        # Self-loop on unadded node MUST return True
        self_unadded = DeductionStep(step_id="s4", target_node_id="unadded_node", premise_node_ids=["unadded_node"])
        assert dag.would_create_cycle(self_unadded) is True


# ============================================================================
# 2. ADVERSARIAL HYPOTHESIS LEAK DETECTION
# ============================================================================

class TestAdversarialHypothesisLeakDetection:
    """Stress test hypothesis leak detection with multi-premise scopes and varied assumption strings."""

    def test_complex_multi_premise_valid_subsets(self):
        """Target with 4 assumptions allows any combination of premises possessing valid assumption subsets."""
        skeptic = AdversarialSkeptic()
        target = ProofNode(
            node_id="target",
            label="Target Theorem",
            statement_latex="T",
            statement_lean="T",
            scope={"assumptions": ["triangle_free", "bipartite", "connected", r"\Delta(G) \le 4"]},
        )
        p1 = ProofNode(node_id="p1", label="P1", statement_latex="P1", statement_lean="P1", scope={"assumptions": ["triangle_free"]})
        p2 = ProofNode(node_id="p2", label="P2", statement_latex="P2", statement_lean="P2", scope={"assumptions": ["bipartite", "connected"]})
        p3 = ProofNode(node_id="p3", label="P3", statement_latex="P3", statement_lean="P3", scope={"assumptions": [r"\Delta(G) \le 4"]})
        p4 = ProofNode(node_id="p4", label="P4", statement_latex="P4", statement_lean="P4", scope={"assumptions": []})
        p5 = ProofNode(node_id="p5", label="P5", statement_latex="P5", statement_lean="P5", scope=None)

        step = DeductionStep(step_id="step_valid", target_node_id="target", premise_node_ids=["p1", "p2", "p3", "p4", "p5"])
        has_leak, critique = skeptic.check_hypothesis_leak(step, [p1, p2, p3, p4, p5], target)
        assert has_leak is False
        assert critique is None

    def test_single_leaked_assumption_among_many_valid_premises(self):
        """If 4 premises are valid but 1 premise has an unstated local assumption, the leak must be flagged."""
        skeptic = AdversarialSkeptic()
        target = ProofNode(
            node_id="target",
            label="Target Theorem",
            statement_latex="T",
            statement_lean="T",
            scope={"assumptions": ["triangle_free", "connected"]},
        )
        p1 = ProofNode(node_id="p1", label="P1", statement_latex="P1", statement_lean="P1", scope={"assumptions": ["triangle_free"]})
        p2 = ProofNode(node_id="p2", label="P2", statement_latex="P2", statement_lean="P2", scope={"assumptions": ["connected"]})
        p3 = ProofNode(node_id="p3", label="P3", statement_latex="P3", statement_lean="P3", scope={"assumptions": []})
        p_leak = ProofNode(
            node_id="p_leak",
            label="PLeak",
            statement_latex="PL",
            statement_lean="PL",
            scope={"assumptions": ["triangle_free", "planar_graph"]},
        )

        step = DeductionStep(step_id="step_leaked", target_node_id="target", premise_node_ids=["p1", "p2", "p_leak", "p3"])
        has_leak, critique = skeptic.check_hypothesis_leak(step, [p1, p2, p_leak, p3], target)
        assert has_leak is True
        assert critique is not None
        assert "planar_graph" in critique
        assert "p_leak" in critique

    def test_varied_assumption_strings_latex_unicode_special_chars(self):
        """Assumption strings containing LaTeX, Unicode symbols, and complex math phrases."""
        skeptic = AdversarialSkeptic()
        target = ProofNode(
            node_id="target",
            label="Target",
            statement_latex="T",
            statement_lean="T",
            scope={"assumptions": ["χ(G) ≤ 3", "ω(G) = 2", r"|E(G)| \le \frac{n^2}{4}", "G has no K_5 minor"]},
        )
        p_valid = ProofNode(
            node_id="p_valid",
            label="PValid",
            statement_latex="PV",
            statement_lean="PV",
            scope={"assumptions": ["χ(G) ≤ 3", r"|E(G)| \le \frac{n^2}{4}"]},
        )
        p_leak_unicode = ProofNode(
            node_id="p_leak_uni",
            label="PLeakUni",
            statement_latex="PLU",
            statement_lean="PLU",
            scope={"assumptions": ["χ(G) ≤ 3", "λ_1(A) ≥ 4.0"]},
        )

        step = DeductionStep(step_id="step_test", target_node_id="target", premise_node_ids=["p_valid", "p_leak_unicode"])

        # p_valid alone has no leak
        has_leak, _ = skeptic.check_hypothesis_leak(step, [p_valid], target)
        assert has_leak is False

        # including p_leak_unicode flags λ_1(A) ≥ 4.0
        has_leak, critique = skeptic.check_hypothesis_leak(step, [p_valid, p_leak_unicode], target)
        assert has_leak is True
        assert "λ_1(A) ≥ 4.0" in critique

    def test_case_sensitivity_and_exact_assumption_matching(self):
        """Assumptions 'bipartite' vs 'Bipartite' are distinct and must not falsely match."""
        skeptic = AdversarialSkeptic()
        target = ProofNode(
            node_id="target",
            label="Target",
            statement_latex="T",
            statement_lean="T",
            scope={"assumptions": ["bipartite"]},
        )
        p_capital = ProofNode(
            node_id="p_cap",
            label="PCap",
            statement_latex="PC",
            statement_lean="PC",
            scope={"assumptions": ["Bipartite"]},
        )
        step = DeductionStep(step_id="step_case", target_node_id="target", premise_node_ids=["p_cap"])
        has_leak, critique = skeptic.check_hypothesis_leak(step, [p_capital], target)
        assert has_leak is True
        assert "Bipartite" in critique

    def test_audit_step_integration_sets_skeptic_approved_false_on_leak(self):
        """Full audit_step integration must reject step with hypothesis leak."""
        dag = LemmaDAG(root_node_id="target")
        target = ProofNode(
            node_id="target",
            label="Target",
            statement_latex="T",
            statement_lean="T",
            scope={"assumptions": []},
        )
        premise = ProofNode(
            node_id="premise",
            label="Premise",
            statement_latex="P",
            statement_lean="P",
            scope={"assumptions": ["is_bipartite"]},
        )
        dag.add_node(target)
        dag.add_node(premise)

        step = DeductionStep(
            step_id="step_audit_leak",
            target_node_id="target",
            premise_node_ids=["premise"],
            rule_type="SUBSTITUTION",
            rule_name="LeakedScope",
        )

        skeptic = AdversarialSkeptic()
        approved, critique = skeptic.audit_step(dag, step)
        assert approved is False
        assert step.skeptic_approved is False
        assert "leak" in (critique or "").lower()


# ============================================================================
# 3. PYDANTIC SERIALIZATION & TIKZ EXPORT
# ============================================================================

class TestAdversarialPydanticSerializationAndTikZ:
    """Stress test serialization round-trips (ProofNode, DeductionStep, LemmaDAG) and TikZ generation."""

    def test_proof_node_full_serialization_roundtrip(self):
        """Test ProofNode with rich attributes, custom extra fields, and scopes."""
        node = ProofNode(
            node_id="node_adv_1",
            label=r"Bound \chi \le 3",
            statement_latex=r"\chi(G) \le 3",
            statement_lean="G.chromaticNumber <= 3",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["triangle_free", "girth >= 5"], "context": "extremal"},
            confidence_score=0.92,
            is_proven=False,
            status="IN_PROGRESS",
            metadata={"source": "heuristic_agent", "depth": 3, "tags": ["chromatic", "planar"]},
            custom_extra_attr="adversarial_payload",
        )

        d = node.to_dict()
        node2 = ProofNode.from_dict(d)

        assert node2.node_id == node.node_id
        assert node2.label == node.label
        assert node2.statement_latex == node.statement_latex
        assert node2.statement_lean == node.statement_lean
        assert node2.node_type == node.node_type
        assert node2.scope == node.scope
        assert node2.confidence_score == pytest.approx(node.confidence_score)
        assert node2.is_proven == node.is_proven
        assert node2.status == node.status
        assert node2.metadata == node.metadata
        assert getattr(node2, "custom_extra_attr", None) == "adversarial_payload"

    def test_deduction_step_full_serialization_roundtrip(self):
        """Test DeductionStep round-trip with all boolean verification flags."""
        step = DeductionStep(
            step_id="step_adv_1",
            target_node_id="target_node",
            premise_node_ids=["prem_1", "prem_2", "prem_3"],
            rule_type="INEQUALITY_CHAIN",
            rule_name="TransitivityWithSlack",
            justification="Combining three inequalities",
            is_verified=True,
            z3_verified=True,
            skeptic_approved=True,
            confidence_score=0.985,
            metadata={"solver_time_ms": 14.2, "z3_model": {"x": 5.0}},
        )

        assert step.is_sound() is True

        d = step.to_dict()
        step2 = DeductionStep.from_dict(d)

        assert step2.step_id == step.step_id
        assert step2.target_node_id == step.target_node_id
        assert step2.premise_node_ids == step.premise_node_ids
        assert step2.is_sound() is True
        assert step2.metadata == step.metadata

    def test_lemma_dag_full_serialization_roundtrip_preserves_networkx_graph(self):
        """Test full LemmaDAG serialization roundtrip through JSON string."""
        dag = LemmaDAG(root_node_id="target_root")

        # Create 5 nodes
        for i in range(5):
            nid = f"n{i}"
            ntype = "TARGET_CONJECTURE" if i == 4 else ("AXIOM" if i in (0, 1) else "SUB_LEMMA")
            dag.add_node(
                ProofNode(
                    node_id=nid,
                    label=f"Node {i}",
                    statement_latex=f"L_{i}",
                    statement_lean=f"l_{i}",
                    node_type=ntype,
                )
            )

        # Create steps: n0, n1 -> n2; n2 -> n3; n3 -> n4 (target_root is n4)
        dag.add_step(DeductionStep(step_id="s1", target_node_id="n2", premise_node_ids=["n0", "n1"], rule_name="CombineAxioms"))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="n3", premise_node_ids=["n2"], rule_name="LemmaStep"))
        dag.add_step(DeductionStep(step_id="s3", target_node_id="n4", premise_node_ids=["n3"], rule_name="FinalStep"))

        # Serialize to dict -> JSON string -> dict -> from_dict
        d = dag.to_dict()
        json_str = json.dumps(d)
        d_loaded = json.loads(json_str)
        dag_recon = LemmaDAG.from_dict(d_loaded)

        assert dag_recon.root_node_id == "target_root"
        assert set(dag_recon.nodes.keys()) == set(dag.nodes.keys())
        assert set(dag_recon.steps.keys()) == set(dag.steps.keys())

        # Verify NetworkX graph reconstruction
        assert set(dag_recon.graph.nodes()) == set(dag.graph.nodes())
        assert set(dag_recon.graph.edges()) == set(dag.graph.edges())

        # Verify topological sort matches
        assert dag.topological_sort() == dag_recon.topological_sort()

        # Verify TikZ output matches exactly
        assert dag.to_tikz() == dag_recon.to_tikz()

    def test_to_tikz_rendering_structure_and_escaping(self):
        """Test TikZ LaTeX output format, math styles, and LaTeX underscore escaping."""
        dag = LemmaDAG(root_node_id="root_thm")
        dag.add_node(ProofNode(node_id="root_thm", label="target_bound_chi", statement_latex=r"\chi \le \Delta + 1", statement_lean="chi <= Delta + 1", node_type="TARGET_CONJECTURE"))
        dag.add_node(ProofNode(node_id="ax_greedy", label="axiom_greedy_bound", statement_latex=r"\chi \le greedy", statement_lean="chi <= greedy", node_type="AXIOM"))
        dag.add_step(DeductionStep(step_id="step_1", target_node_id="root_thm", premise_node_ids=["ax_greedy"], rule_name="rule_greedy_trans"))

        tikz = dag.to_tikz()

        assert r"\begin{tikzpicture}" in tikz
        assert r"\end{tikzpicture}" in tikz
        assert "axiom_node" in tikz
        assert "target_node" in tikz
        # Underscores must be escaped for LaTeX compatibility
        assert r"target\_bound\_chi" in tikz
        assert r"axiom\_greedy\_bound" in tikz
        assert r"rule\_greedy\_trans" in tikz

    def test_proof_propagation_and_minimal_proof_tree_in_or_branching_dag(self):
        """Test proof status propagation and minimal proof tree selection with alternative OR branches."""
        dag = LemmaDAG(root_node_id="T")
        dag.add_node(ProofNode(node_id="Ax", label="Axiom", statement_latex="A", statement_lean="A", node_type="AXIOM"))
        dag.add_node(ProofNode(node_id="UnprovenPrem", label="Unproven", statement_latex="U", statement_lean="U", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="BranchSound", label="Sound Branch", statement_latex="S", statement_lean="S", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="BranchDead", label="Dead Branch", statement_latex="D", statement_lean="D", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="T", label="Target", statement_latex="T", statement_lean="T", node_type="TARGET_CONJECTURE"))

        # Branch 1 (dead): UnprovenPrem -> BranchDead -> T
        dag.add_step(DeductionStep(step_id="s_dead_1", target_node_id="BranchDead", premise_node_ids=["UnprovenPrem"]))
        dag.add_step(DeductionStep(step_id="s_dead_2", target_node_id="T", premise_node_ids=["BranchDead"]))

        # Branch 2 (sound): Ax -> BranchSound -> T
        dag.add_step(DeductionStep(step_id="s_sound_1", target_node_id="BranchSound", premise_node_ids=["Ax"]))
        dag.add_step(DeductionStep(step_id="s_sound_2", target_node_id="T", premise_node_ids=["BranchSound"]))

        # Check proof status propagation
        assert dag.is_node_proven("BranchSound") is True
        assert dag.is_node_proven("BranchDead") is False
        assert dag.is_node_proven("T") is True

        # Minimal proof tree MUST pick the sound branch and omit the dead branch
        tree = dag.extract_minimal_proof_tree("T")
        selected_ids = {s.step_id for s in tree}
        assert "s_sound_1" in selected_ids
        assert "s_sound_2" in selected_ids
        assert "s_dead_1" not in selected_ids
        assert "s_dead_2" not in selected_ids


# ============================================================================
# 4. DOCUMENTED EDGE-CASE VULNERABILITY REPRODUCTIONS
# ============================================================================

class TestAdversarialVulnerabilityReproductions:
    """Document and empirically verify subtle edge-case failure modes discovered during review."""

    def test_hypothesis_leak_crashes_on_none_assumptions_vulnerability(self):
        """Vulnerability: ProofNode with scope={'assumptions': None} crashes check_hypothesis_leak with TypeError.

        In skeptic.py:85: `target_assumptions = set(target_scope.get('assumptions', []))`
        If 'assumptions' key is present with value None, .get() returns None instead of [].
        set(None) raises TypeError: 'NoneType' object is not iterable.
        """
        skeptic = AdversarialSkeptic()
        p = ProofNode(node_id="p", label="P", statement_latex="P", statement_lean="P", scope={"assumptions": ["A"]})
        target_malformed = ProofNode(node_id="t", label="T", statement_latex="T", statement_lean="T", scope={"assumptions": None})
        step = DeductionStep(step_id="s", target_node_id="t", premise_node_ids=["p"])

        with pytest.raises(TypeError, match="'NoneType' object is not iterable"):
            skeptic.check_hypothesis_leak(step, [p], target_malformed)

    def test_to_tikz_key_error_on_cyclic_graph_vulnerability(self):
        """Vulnerability: LemmaDAG.to_tikz() catches ValueError from topological_sort() but crashes with KeyError.

        In dag.py:354: `levels[nid] = (max([levels[p] for p in preds], default=-1) + 1)`
        When topological_sort() fails due to a cycle, fallback topo=list(self.nodes.keys()) visits nodes
        before their predecessors in a cycle, causing levels[p] to raise KeyError.
        """
        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A"))
        dag.add_node(ProofNode(node_id="B", label="B", statement_latex="B", statement_lean="B"))
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"]))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="A", premise_node_ids=["B"]))

        assert dag.has_cycle() is True
        with pytest.raises(KeyError):
            dag.to_tikz()
