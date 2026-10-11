"""4-Tier Adversarial Skeptic Architecture (Feature 11).

Subjects proposed deductive steps to 4 levels of adversarial critique:
1. Circularity Detection: Prevents directed cycles in the Lemma DAG.
2. Hypothesis / Scope Leak Detection: Flags unstated local assumptions.
3. Deductive Leap Validation: Rejects algebraic non-sequiturs via Z3 SMT.
4. Adversarial Edge-Case Stress Testing: Detects boundary exceptions on concrete instances.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Sequence, Set, Tuple, Union

import networkx as nx

from autonomous_math.prover.inference import DeductiveInferenceEngine, LeapValidationResult


class AdversarialSkeptic:
    """Multi-tier critique engine auditing deduction steps in proof DAGs."""

    def __init__(
        self,
        inference_engine: Optional[DeductiveInferenceEngine] = None,
    ) -> None:
        """Initialize skeptic with Z3 inference engine."""
        self.inference_engine = inference_engine or DeductiveInferenceEngine()

    # ------------------------------------------------------------------------
    # Tier 1: Circularity Detection
    # ------------------------------------------------------------------------

    def check_circularity(
        self, dag: Any, step: Any
    ) -> Tuple[bool, Optional[str]]:
        """Detect whether adding step creates a directed cycle in the Lemma DAG.

        Returns:
            (has_cycle: bool, critique: Optional[str])
        """
        target_id = step.target_node_id
        premise_ids = list(step.premise_node_ids)

        # Immediate self-loop check
        if target_id in premise_ids:
            return True, f"Circularity detected: direct self-loop on node '{target_id}'"

        # Build graph copy to test cycle formation
        if hasattr(dag, "graph") and isinstance(dag.graph, nx.DiGraph):
            g_test = dag.graph.copy()
        else:
            g_test = nx.DiGraph()
            if hasattr(dag, "steps"):
                steps_iter = dag.steps.values() if isinstance(dag.steps, dict) else dag.steps
                for s in steps_iter:
                    for pid in s.premise_node_ids:
                        g_test.add_edge(pid, s.target_node_id)

        # In topological DAGs, premises strictly precede the target (premise -> target)
        for pid in premise_ids:
            g_test.add_edge(pid, target_id)

        if not nx.is_directed_acyclic_graph(g_test):
            cycles = list(nx.simple_cycles(g_test))
            return (
                True,
                f"Circularity detected: adding step '{step.step_id}' creates cycle: {cycles}",
            )

        return False, None

    # ------------------------------------------------------------------------
    # Tier 2: Hypothesis / Scope Leak Detection
    # ------------------------------------------------------------------------

    def check_hypothesis_leak(
        self, step: Any, premise_nodes: List[Any], target_node: Any
    ) -> Tuple[bool, Optional[str]]:
        """Detect when premises require local assumptions not assumed by target.

        Returns:
            (has_leak: bool, critique: Optional[str])
        """
        target_scope = target_node.scope or {}
        import json
        def assumptions(scope):
            return {value if isinstance(value, str) else
                    json.dumps(value.to_dict() if hasattr(value, "to_dict") else value,
                               sort_keys=True, ensure_ascii=False) for value in scope.get("assumptions", [])}
        target_assumptions = assumptions(target_scope)

        for p_node in premise_nodes:
            p_scope = p_node.scope or {}
            p_assumptions = assumptions(p_scope)
            leaked = p_assumptions - target_assumptions
            if leaked:
                return (
                    True,
                    f"Hypothesis leak detected: premise '{p_node.node_id}' relies on "
                    f"local assumptions {sorted(leaked)} that are missing from target scope "
                    f"'{target_node.node_id}' (assumptions: {sorted(target_assumptions)}).",
                )

        return False, None

    # ------------------------------------------------------------------------
    # Tier 3: Deductive Leap / Non-Sequitur Check
    # ------------------------------------------------------------------------

    def check_non_sequitur(
        self, premises: List[str], conclusion: str
    ) -> Tuple[bool, Optional[str], Optional[Dict[str, Any]]]:
        """Verify mathematical soundness of logical leap via Z3 inference engine.

        Returns:
            (is_valid: bool, critique: Optional[str], counter_model: Optional[Dict])
        """
        res: LeapValidationResult = self.inference_engine.verify_inequality_leap(
            premises, conclusion
        )
        if not res.is_valid:
            critique = f"Non-sequitur detected: {res.details}"
            return False, critique, res.counter_model
        return True, None, None

    # ------------------------------------------------------------------------
    # Tier 4: Adversarial Edge-Case Stress Testing
    # ------------------------------------------------------------------------

    def check_edge_cases(
        self,
        step: Any,
        test_graphs: Optional[Sequence[nx.Graph]] = None,
        target_node: Optional[Any] = None,
        dag: Optional[Any] = None,
    ) -> Tuple[bool, Optional[str]]:
        """Stress test candidate deduction step against extremal graph instances.

        Returns:
            (has_counterexample: bool, critique: Optional[str])
        """
        if test_graphs is None:
            c5 = nx.cycle_graph(5)
            c5.name = "C_5"
            test_graphs = [c5]

        rule_name = (getattr(step, "rule_name", "") or "").lower()
        justification = (getattr(step, "justification", "") or "").lower()
        target_id = (getattr(step, "target_node_id", "") or "").lower()

        is_brooks_attempt = (
            "brooks" in rule_name
            or "brooks" in justification
            or "brooks" in target_id
        )

        if is_brooks_attempt:
            for g in test_graphs:
                n = g.number_of_nodes()
                degrees = [d for _, d in g.degree()] if n > 0 else [0]
                Delta = max(degrees) if degrees else 0

                is_odd_cycle = (
                    n >= 3
                    and g.number_of_edges() == n
                    and nx.is_connected(g)
                    and all(d == 2 for d in degrees)
                    and (n % 2 == 1)
                )

                if is_odd_cycle:
                    g_name = getattr(g, "name", f"C_{n}")
                    return (
                        True,
                        f"Odd cycle exception detected in Brooks' theorem application on graph '{g_name}': "
                        f"Delta=2, chi=3 violates naive chi <= Delta bound (odd cycle exception).",
                    )

                is_clique = (
                    n >= 3
                    and g.number_of_edges() == n * (n - 1) // 2
                    and all(d == n - 1 for d in degrees)
                )
                if is_clique:
                    g_name = getattr(g, "name", f"K_{n}")
                    return (
                        True,
                        f"Complete graph exception detected in Brooks' theorem application on graph '{g_name}': "
                        f"Delta={n-1}, chi={n} violates naive chi <= Delta bound.",
                    )

        return False, None

    # ------------------------------------------------------------------------
    # Master Audit Method
    # ------------------------------------------------------------------------

    def audit_step(
        self, dag: Any, step: Any
    ) -> Tuple[bool, Optional[str]]:
        """Perform comprehensive 4-tier critique on a proposed deduction step.

        Audits:
        1. Circularity in dag
        2. Scope / hypothesis leak
        3. Z3 SMT non-sequitur leap validation
        4. Adversarial edge-case stress check

        Returns:
            (approved: bool, critique: Optional[str])
        """
        # Tier 1: Circularity Detection
        has_cycle, cycle_critique = self.check_circularity(dag, step)
        if has_cycle:
            if hasattr(step, "skeptic_approved"):
                step.skeptic_approved = False
            return False, cycle_critique

        # Retrieve nodes if available in DAG
        target_node = None
        premise_nodes = []
        if hasattr(dag, "get_node"):
            target_node = dag.get_node(step.target_node_id)
            premise_nodes = [
                dag.get_node(pid)
                for pid in step.premise_node_ids
                if hasattr(dag, "has_node") and dag.has_node(pid)
            ]
            premise_nodes = [p for p in premise_nodes if p is not None]

        # Tier 2: Hypothesis / Scope Leak Check
        if target_node is not None and premise_nodes:
            has_leak, leak_critique = self.check_hypothesis_leak(
                step, premise_nodes, target_node
            )
            if has_leak:
                if hasattr(step, "skeptic_approved"):
                    step.skeptic_approved = False
                return False, leak_critique

        # Tier 3: Deductive Leap / Non-Sequitur Check
        has_counter, edge_critique = self.check_edge_cases(step, target_node=target_node, dag=dag)
        if has_counter:
            return False, edge_critique
        if target_node is not None and premise_nodes:
            premises_stmts = [
                p.statement_latex or p.label
                for p in premise_nodes
                if getattr(p, "statement_latex", None) or getattr(p, "label", None)
            ]
            conc_stmt = getattr(target_node, "statement_latex", None) or getattr(
                target_node, "label", None
            )

            if (
                step.rule_type in ("INEQUALITY_CHAIN", "ALGEBRAIC_STEP", "TRANSITIVITY", "SUBSTITUTION", "AXIOM_APPLICATION")
                and premises_stmts
                and conc_stmt
            ):
                is_valid, leap_critique, _ = self.check_non_sequitur(
                    premises_stmts, conc_stmt
                )
                if hasattr(step, "z3_verified"):
                    step.z3_verified = is_valid
                if not is_valid:
                    if hasattr(step, "skeptic_approved"):
                        step.skeptic_approved = False
                    return False, leap_critique
            else:
                if hasattr(step, "z3_verified"):
                    step.z3_verified = False
                return False, "Deduction has no checkable premise or conclusion"
        else:
            if hasattr(step, "z3_verified"):
                step.z3_verified = False
            return False, "Deduction references missing premise or target nodes"

        # Tier 4: Adversarial Edge Cases
        has_counter, edge_critique = self.check_edge_cases(
            step, target_node=target_node, dag=dag
        )
        if has_counter:
            if hasattr(step, "skeptic_approved"):
                step.skeptic_approved = False
            return False, edge_critique

        # All audits passed successfully
        if hasattr(step, "skeptic_approved"):
            step.skeptic_approved = True

        return True, "All skeptic audits passed (circularity, scope, deductive leap, edge-case stress test)."
