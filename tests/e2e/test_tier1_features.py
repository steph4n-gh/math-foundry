"""Tier 1 E2E Feature Coverage Test Suite.

Verifies primary functional behavior and interface contracts across Requirements R1-R5:
- R1: Autonomous Conjecture Generation (Features 1-4)
- R2: Empirical Falsification Sieve (Features 5-7)
- R3: Prover-Skeptic Search Engine (Features 8-12)
- R4: Dual Output Artifact Generation (Features 13-15)
- R5: Orchestration CLI & Demonstration Pipelines (Features 16-17)

Every test derives expected outputs from the authoritative reference oracles in conftest.py.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List

import networkx as nx
import numpy as np
import pytest

from .conftest import ReferenceGraphOracle, ReferenceArtifactValidator


# ============================================================================
# REQUIREMENT R1: AUTONOMOUS CONJECTURE GENERATION (FEATURES 1-4)
# ============================================================================

class TestRequirementR1ConjectureGeneration:
    """Feature coverage for R1: Invariant Engine, AST Grammar, Generators, Filters."""

    def test_r1_f1_invariant_engine_computes_exact_structural_invariants(
        self, graph_c5, graph_petersen, graph_k4, oracle
    ):
        """Feature 1: GraphInvariantEvaluator computes 15+ invariants matching reference oracle."""
        inv_mod = pytest.importorskip("autonomous_math.core.invariants")
        evaluator_cls = getattr(inv_mod, "GraphInvariantEvaluator")

        test_graphs = [
            ("C5", graph_c5),
            ("Petersen", graph_petersen),
            ("K4", graph_k4),
        ]
        invariants_to_test = [
            "order",
            "size",
            "max_degree",
            "min_degree",
            "density",
            "triangle_count",
            "is_triangle_free",
            "girth",
            "clique_number",
            "independence_number",
            "chromatic_number",
            "spectral_radius",
            "min_adjacency_eigenvalue",
            "algebraic_connectivity",
        ]

        for name, G in test_graphs:
            ref_values = oracle.evaluate_all(G)
            computed = evaluator_cls.evaluate(G, invariants_to_test)

            assert isinstance(computed, dict), f"Expected dict for {name}, got {type(computed)}"
            for inv in invariants_to_test:
                assert inv in computed, f"Missing invariant '{inv}' in evaluation of {name}"
                ref_val = ref_values[inv]
                comp_val = computed[inv]

                if isinstance(ref_val, (int, bool)):
                    assert comp_val == ref_val, (
                        f"Mismatch for invariant '{inv}' on {name}: computed {comp_val} != expected {ref_val}"
                    )
                else:
                    assert np.isclose(comp_val, ref_val, atol=1e-5), (
                        f"Float mismatch for invariant '{inv}' on {name}: computed {comp_val} != expected {ref_val}"
                    )

    def test_r1_f2_ast_expression_node_evaluation_and_relational_truth(
        self, graph_c5, graph_k4, oracle
    ):
        """Feature 2: AST models evaluate expressions and relations correctly on graphs."""
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")
        RelationNode = getattr(ast_mod, "RelationNode")
        Conjecture = getattr(ast_mod, "Conjecture")

        # Construct: chromatic_number >= clique_number (known universally true)
        lhs = InvariantNode("chromatic_number")
        rhs = InvariantNode("clique_number")
        rel = RelationNode(">=", lhs, rhs)
        conj_true = Conjecture(
            id="conj_chi_ge_omega",
            statement="chi(G) >= omega(G)",
            lhs_expr=lhs,
            rel=">=",
            rhs_expr=rhs,
            complexity=2,
        )

        # On K4: chi=4, omega=4 -> holds, (True, 4.0, 4.0)
        holds_k4, lhs_k4, rhs_k4 = conj_true.evaluate(graph_k4)
        assert holds_k4 is True
        assert lhs_k4 == 4.0
        assert rhs_k4 == 4.0

        # On C5: chi=3, omega=2 -> holds, (True, 3.0, 2.0)
        holds_c5, lhs_c5, rhs_c5 = conj_true.evaluate(graph_c5)
        assert holds_c5 is True
        assert lhs_c5 == 3.0
        assert rhs_c5 == 2.0

        # Construct false claim: chromatic_number <= clique_number - 1
        sub_rhs = BinaryOpNode("-", rhs, ast_mod.ConstantNode(1.0))
        conj_false = Conjecture(
            id="conj_false_bound",
            statement="chi(G) <= omega(G) - 1",
            lhs_expr=lhs,
            rel="<=",
            rhs_expr=sub_rhs,
            complexity=3,
        )
        holds_false, l_val, r_val = conj_false.evaluate(graph_c5)
        assert holds_false is False
        assert l_val == 3.0
        assert r_val == 1.0

    def test_r1_f3_conjecture_generator_exhaustive_enumeration(self, graph_c5):
        """Feature 3: ConjectureGenerator produces well-formed candidates with valid complexity."""
        gen_mod = pytest.importorskip("autonomous_math.conjecturing.generator")
        ConjectureGenerator = getattr(gen_mod, "ConjectureGenerator")

        generator = ConjectureGenerator()
        conjectures = generator.generate_exhaustive(max_depth=2, limit=10)

        assert isinstance(conjectures, list)
        assert len(conjectures) > 0, "Conjecture generator produced empty list"

        for conj in conjectures:
            assert hasattr(conj, "id") and conj.id
            assert hasattr(conj, "statement") and conj.statement
            assert hasattr(conj, "lhs_expr")
            assert hasattr(conj, "rhs_expr")
            assert hasattr(conj, "rel") and conj.rel in ["<=", ">=", "==", "<", ">"]
            assert hasattr(conj, "complexity") and conj.complexity >= 1
            # Verify evaluatability on a concrete graph instance
            result = conj.evaluate(graph_c5)
            assert isinstance(result, tuple) and len(result) == 3
            assert isinstance(result[0], bool)

    def test_r1_f4_conjecture_filtration_triviality_filter(self):
        """Feature 4: TrivialityFilter discards algebraic tautologies using SymPy."""
        filters_mod = pytest.importorskip("autonomous_math.conjecturing.filters")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        TrivialityFilter = getattr(filters_mod, "TrivialityFilter")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")
        Conjecture = getattr(ast_mod, "Conjecture")

        # Tautology: order <= order
        tautology = Conjecture(
            id="tautology_1",
            statement="order <= order",
            lhs_expr=InvariantNode("order"),
            rel="<=",
            rhs_expr=InvariantNode("order"),
            complexity=2,
        )

        # Tautology: order <= order + 1
        tautology_plus = Conjecture(
            id="tautology_2",
            statement="order <= order + 1",
            lhs_expr=InvariantNode("order"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("order"), ConstantNode(1.0)),
            complexity=3,
        )

        # Non-trivial claim: chromatic_number <= max_degree + 1 (Brooks-type)
        non_trivial = Conjecture(
            id="brooks_type",
            statement="chromatic_number <= max_degree + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )

        filtered = TrivialityFilter.filter([tautology, tautology_plus, non_trivial])
        filtered_ids = [c.id for c in filtered]

        assert "tautology_1" not in filtered_ids, "Triviality filter failed to eliminate order <= order"
        assert "tautology_2" not in filtered_ids, "Triviality filter failed to eliminate order <= order + 1"
        assert "brooks_type" in filtered_ids, "Triviality filter accidentally eliminated non-trivial claim"

    def test_r1_f4_conjecture_filtration_dalmatians_and_echo_subsumption(
        self, graph_c5, graph_petersen, graph_k4
    ):
        """Feature 4: Dalmatians and Echo filters eliminate strictly weaker and subsumed bounds."""
        filters_mod = pytest.importorskip("autonomous_math.conjecturing.filters")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        DalmatiansFilter = getattr(filters_mod, "DalmatiansFilter")
        EchoFilter = getattr(filters_mod, "EchoFilter")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")
        Conjecture = getattr(ast_mod, "Conjecture")

        # Bound 1: chi <= Delta + 1
        bound_tight = Conjecture(
            id="bound_tight",
            statement="chromatic_number <= max_degree + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )
        # Bound 2: chi <= Delta + 10 (strictly worse on every graph in test set)
        bound_loose = Conjecture(
            id="bound_loose",
            statement="chromatic_number <= max_degree + 10",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(10.0)),
            complexity=3,
        )

        test_instances = [graph_c5, graph_petersen, graph_k4]
        dalmatians_filtered = DalmatiansFilter.filter([bound_tight, bound_loose], test_instances)
        dalmatians_ids = [c.id for c in dalmatians_filtered]
        assert "bound_tight" in dalmatians_ids
        assert "bound_loose" not in dalmatians_ids, "Dalmatians failed to eliminate strictly loose bound"

        # Echo subsumption: If existing theorem covers bound, echo filter drops duplicate
        existing = [bound_tight]
        echo_filtered = EchoFilter.filter([bound_tight, bound_loose], existing_theorems=existing)
        echo_ids = [c.id for c in echo_filtered]
        assert "bound_tight" not in echo_ids or len(echo_filtered) == 0

    def test_r1_conjecture_serialization_roundtrip_contract(self, graph_c5):
        """R1 Contract: Conjecture serializes to and deserializes from JSON schema defined in PROJECT.md."""
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")
        Conjecture = getattr(ast_mod, "Conjecture")

        original = Conjecture(
            id="conj_ser_test_001",
            statement="alpha <= n / 2",
            lhs_expr=InvariantNode("independence_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("/", InvariantNode("order"), ConstantNode(2.0)),
            guard_predicate="is_connected",
            complexity=4,
        )

        # Check serialization schema keys
        d = original.to_dict() if hasattr(original, "to_dict") else original.model_dump()
        expected_keys = {"id", "statement", "lhs_expr", "rel", "rhs_expr", "guard_predicate", "complexity"}
        assert expected_keys.issubset(set(d.keys())), f"Missing keys in serialized schema: {expected_keys - set(d.keys())}"

        # JSON roundtrip
        json_str = json.dumps(d)
        loaded_dict = json.loads(json_str)

        reconstructed = (
            getattr(Conjecture, "from_dict")(loaded_dict)
            if hasattr(Conjecture, "from_dict")
            else getattr(Conjecture, "model_validate")(loaded_dict)
        )

        assert reconstructed.id == original.id
        assert reconstructed.statement == original.statement
        assert reconstructed.rel == original.rel
        assert reconstructed.guard_predicate == original.guard_predicate
        assert reconstructed.complexity == original.complexity

        # Evaluation equivalence
        orig_eval = original.evaluate(graph_c5)
        recon_eval = reconstructed.evaluate(graph_c5)
        assert orig_eval == recon_eval


# ============================================================================
# REQUIREMENT R2: EMPIRICAL FALSIFICATION SIEVE (FEATURES 5-7)
# ============================================================================

class TestRequirementR2EmpiricalFalsificationSieve:
    """Feature coverage for R2: Instance DB, Z3 SMT Sieve, Counterexample Certificates."""

    def test_r2_f5_instance_database_population_and_diversity(self, oracle):
        """Feature 5: InstanceDatabase houses diverse extremal graphs with precomputed invariants."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        InstanceDatabase = getattr(sieve_mod, "InstanceDatabase")

        db = InstanceDatabase()
        instances = db.get_instances()
        assert len(instances) >= 50, f"Instance database too small: {len(instances)}"

        # Check diversity of structural families
        has_cycles = any("C" in str(getattr(g, "name", "")) or (nx.is_regular(g) and dict(g.degree())[0] == 2) for g in instances if g.number_of_nodes() > 2)
        has_triangle_free = any(oracle.is_triangle_free(g) for g in instances if g.number_of_edges() > 0)
        has_non_bipartite = any(not nx.is_bipartite(g) for g in instances if g.number_of_edges() > 0)

        assert has_cycles, "Instance DB missing cycle families"
        assert has_triangle_free, "Instance DB missing triangle-free graphs"
        assert has_non_bipartite, "Instance DB missing non-bipartite graphs"

    def test_r2_f6_vectorized_sieve_falsifies_false_conjecture(self):
        """Feature 6: Empirical sieve rejects false conjecture: alpha * omega >= n."""
        sieve_mod = pytest.importorskip("autonomous_math.sieve.instance_db")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        InstanceDatabase = getattr(sieve_mod, "InstanceDatabase")
        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")

        # Conjecture: alpha * omega >= n (False on Petersen: 4 * 2 = 8 < 10)
        lhs = BinaryOpNode("*", InvariantNode("independence_number"), InvariantNode("clique_number"))
        rhs = InvariantNode("order")
        conj = Conjecture(
            id="false_ramsey_product",
            statement="alpha * omega >= n",
            lhs_expr=lhs,
            rel=">=",
            rhs_expr=rhs,
            complexity=3,
        )

        db = InstanceDatabase()
        sieve_result = db.sieve_conjecture(conj) if hasattr(db, "sieve_conjecture") else None
        if sieve_result is None:
            # Fallback to direct test if sieve method on separate class
            sieve_cls_mod = pytest.importorskip("autonomous_math.sieve.z3_sieve")
            sieve_runner = getattr(sieve_cls_mod, "EmpiricalSieveRunner")(db)
            sieve_result = sieve_runner.run(conj)

        assert sieve_result.status == "REFUTED"
        assert sieve_result.counterexample_certificate is not None
        assert sieve_result.tested_instances_count > 0

    def test_r2_f6_z3_smt_graph_synthesis_and_cegar(self, oracle):
        """Feature 6: Z3 CEGAR synthesizes C5 counterexample for triangle-free non-2-colorability."""
        cegar_mod = pytest.importorskip("autonomous_math.sieve.cegar")
        CEGARSieve = getattr(cegar_mod, "CEGARSieve")

        sieve = CEGARSieve()
        # Search for triangle-free graph with chromatic_number > 2 on order 5
        witness_graph = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
        )

        assert witness_graph is not None, "CEGAR failed to synthesize counterexample graph"
        assert witness_graph.number_of_nodes() == 5
        assert witness_graph.number_of_edges() == 5
        assert oracle.is_triangle_free(witness_graph) is True
        assert oracle.chromatic_number_exact(witness_graph) == 3
        assert nx.is_isomorphic(witness_graph, nx.cycle_graph(5))

    def test_r2_f7_counterexample_certificate_schema_contract(self, graph_c5, oracle):
        """Feature 7: CounterexampleCertificate matches exact JSON contract from PROJECT.md."""
        cert_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        CounterexampleCertificate = getattr(cert_mod, "CounterexampleCertificate")

        adj_matrix = nx.to_numpy_array(graph_c5, dtype=int).tolist()
        edges = list(graph_c5.edges())
        invariants = oracle.evaluate_all(graph_c5)

        cert = CounterexampleCertificate(
            conjecture_id="conj_tf_two_colorable",
            graph_order=5,
            graph_size=5,
            adjacency_matrix=adj_matrix,
            edges=edges,
            invariants=invariants,
            refutation_witness={
                "type": "odd_cycle",
                "details": [0, 1, 2, 3, 4, 0],
            },
            verification_hash="sha256_mock_hash_c5",
        )

        # Check required fields
        d = cert.to_dict() if hasattr(cert, "to_dict") else cert.model_dump()
        required_keys = {
            "conjecture_id",
            "graph_order",
            "graph_size",
            "adjacency_matrix",
            "edges",
            "invariants",
            "refutation_witness",
            "verification_hash",
        }
        assert required_keys.issubset(set(d.keys()))

    def test_r2_f7_counterexample_certificate_independent_verification(self, graph_c5):
        """Feature 7: CounterexampleCertificateVerifier independently verifies or refutes certificates."""
        cert_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        CounterexampleCertificate = getattr(cert_mod, "CounterexampleCertificate")
        CounterexampleCertificateVerifier = getattr(cert_mod, "CounterexampleCertificateVerifier")
        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")

        # Claim: chromatic_number <= 2
        conj = Conjecture(
            id="claim_chi_le_2",
            statement="chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ast_mod.ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        adj_matrix = nx.to_numpy_array(graph_c5, dtype=int).tolist()
        valid_cert = CounterexampleCertificate(
            conjecture_id="claim_chi_le_2",
            graph_order=5,
            graph_size=5,
            adjacency_matrix=adj_matrix,
            edges=list(graph_c5.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 3},
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 4, 0]},
            verification_hash="hash_valid",
        )

        # Valid certificate passes verification
        assert CounterexampleCertificateVerifier.verify(valid_cert, conj) is True

        # Tampered certificate (claiming bipartite graph is counterexample)
        k2 = nx.complete_graph(2)
        tampered_cert = CounterexampleCertificate(
            conjecture_id="claim_chi_le_2",
            graph_order=2,
            graph_size=1,
            adjacency_matrix=nx.to_numpy_array(k2, dtype=int).tolist(),
            edges=list(k2.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 2},
            refutation_witness={"type": "direct_evaluation", "details": None},
            verification_hash="hash_tampered",
        )
        assert CounterexampleCertificateVerifier.verify(tampered_cert, conj) is False

    def test_r2_c5_explicit_witness_verification(self, graph_c5, oracle):
        """Acceptance Criteria: Sieve confirms explicit C5 witness for triangle-free non-2-colorability."""
        assert oracle.is_triangle_free(graph_c5) is True
        assert oracle.chromatic_number_exact(graph_c5) == 3
        # Direct exhaustion: verify none of 2^5 = 32 binary colorings are proper
        nodes = list(graph_c5.nodes())
        n = len(nodes)
        for assignment in range(1 << n):
            color = {nodes[i]: (assignment >> i) & 1 for i in range(n)}
            monochromatic = any(color[u] == color[v] for u, v in graph_c5.edges())
            assert monochromatic, f"Found improper 2-coloring on C5: {color}"


# ============================================================================
# REQUIREMENT R3: PROVER-SKEPTIC SEARCH ENGINE (FEATURES 8-12)
# ============================================================================

class TestRequirementR3ProverSkepticSearchEngine:
    """Feature coverage for R3: Lemma DAG, Axioms, Deductive Steps, Skeptic, Search Loop."""

    def test_r3_f8_lemma_dag_and_or_decomposition_and_topological_sort(self):
        """Feature 8: LemmaDAG supports AND/OR nodes and produces valid topological sort."""
        dag_mod = pytest.importorskip("autonomous_math.prover.dag")
        LemmaDAG = getattr(dag_mod, "LemmaDAG")
        ProofNode = getattr(dag_mod, "ProofNode")
        DeductionStep = getattr(dag_mod, "DeductionStep")

        dag = LemmaDAG(root_node_id="target_bound")
        n_root = ProofNode(
            node_id="target_bound",
            label="chi <= Delta + 1",
            statement_latex=r"\chi(G) \le \Delta(G) + 1",
            statement_lean="G.chromaticNumber <= G.maxDegree + 1",
            node_type="TARGET_CONJECTURE",
        )
        n_lemma1 = ProofNode(
            node_id="lemma_greedy_bound",
            label="Greedy coloring uses <= Delta + 1 colors",
            statement_latex=r"\text{Greedy}(G) \le \Delta(G) + 1",
            statement_lean="GreedyColoring G <= G.maxDegree + 1",
            node_type="SUB_LEMMA",
        )
        n_axiom = ProofNode(
            node_id="axiom_greedy",
            label="Greedy ordering axiom",
            statement_latex=r"\chi(G) \le \text{Greedy}(G)",
            statement_lean="G.chromaticNumber <= GreedyColoring G",
            node_type="AXIOM",
        )

        dag.add_node(n_root)
        dag.add_node(n_lemma1)
        dag.add_node(n_axiom)

        step = DeductionStep(
            step_id="step_transitivity",
            target_node_id="target_bound",
            premise_node_ids=["axiom_greedy", "lemma_greedy_bound"],
            rule_type="INEQUALITY_CHAIN",
            rule_name="Transitivity",
            justification="Combining greedy bounds yields target bound",
        )
        dag.add_step(step)

        topo = dag.topological_sort()
        assert "target_bound" in topo
        assert "axiom_greedy" in topo
        # Premises must precede target in topological order
        assert topo.index("axiom_greedy") < topo.index("target_bound")
        assert topo.index("lemma_greedy_bound") < topo.index("target_bound")

    def test_r3_f9_axiom_library_retrieval_and_application(self):
        """Feature 9: AxiomLibrary provides Handshaking, Turan, Brooks, Greedy bounds."""
        axioms_mod = pytest.importorskip("autonomous_math.prover.axioms")
        AxiomLibrary = getattr(axioms_mod, "AxiomLibrary")

        lib = AxiomLibrary()
        expected_axioms = ["handshaking_lemma", "greedy_coloring_bound", "turan_theorem"]
        available = lib.list_axioms() if hasattr(lib, "list_axioms") else []
        for ax in expected_axioms:
            assert ax in available or any(ax in a.lower() for a in available), f"Missing axiom: {ax}"

    def test_r3_f10_formal_deductive_step_and_smt_leap_validation(self):
        """Feature 10: DeductiveInferenceEngine validates algebraic and logical steps with Z3."""
        inf_mod = pytest.importorskip("autonomous_math.prover.inference")
        DeductiveInferenceEngine = getattr(inf_mod, "DeductiveInferenceEngine")

        engine = DeductiveInferenceEngine()

        # Valid step: n >= 1, alpha >= 1, chi >= n / alpha, alpha <= 3 ==> chi >= n / 3
        valid_res = engine.verify_inequality_leap(
            premises=["n >= 1", "alpha >= 1", "chi >= n / alpha", "alpha <= 3"],
            conclusion="chi >= n / 3",
        )
        assert valid_res.is_valid is True

        # Invalid non-sequitur: alpha <= 3 ==> chi <= 3 (counter-example exists)
        invalid_res = engine.verify_inequality_leap(
            premises=["alpha <= 3"],
            conclusion="chi <= 3",
        )
        assert invalid_res.is_valid is False
        assert invalid_res.counter_model is not None

    def test_r3_f11_adversarial_skeptic_circularity_detection(self):
        """Feature 11: AdversarialSkeptic rejects cyclic deductive derivations."""
        skeptic_mod = pytest.importorskip("autonomous_math.prover.skeptic")
        dag_mod = pytest.importorskip("autonomous_math.prover.dag")
        AdversarialSkeptic = getattr(skeptic_mod, "AdversarialSkeptic")
        LemmaDAG = getattr(dag_mod, "LemmaDAG")
        ProofNode = getattr(dag_mod, "ProofNode")
        DeductionStep = getattr(dag_mod, "DeductionStep")

        dag = LemmaDAG(root_node_id="A")
        dag.add_node(ProofNode(node_id="A", label="A", statement_latex="A", statement_lean="A", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="B", label="B", statement_latex="B", statement_lean="B", node_type="SUB_LEMMA"))
        dag.add_node(ProofNode(node_id="C", label="C", statement_latex="C", statement_lean="C", node_type="SUB_LEMMA"))

        # Add steps A -> B and B -> C
        dag.add_step(DeductionStep(step_id="s1", target_node_id="B", premise_node_ids=["A"], rule_type="INEQUALITY_CHAIN", rule_name="Step1", justification="A implies B"))
        dag.add_step(DeductionStep(step_id="s2", target_node_id="C", premise_node_ids=["B"], rule_type="INEQUALITY_CHAIN", rule_name="Step2", justification="B implies C"))

        skeptic = AdversarialSkeptic()
        # Attempt circular step: C -> A
        cyclic_step = DeductionStep(
            step_id="s3_circular",
            target_node_id="A",
            premise_node_ids=["C"],
            rule_type="INEQUALITY_CHAIN",
            rule_name="CircularStep",
            justification="C implies A",
        )

        approved, critique = skeptic.audit_step(dag, cyclic_step)
        assert approved is False
        assert critique is not None
        assert "circular" in critique.lower() or "cycle" in critique.lower()

    def test_r3_f11_adversarial_skeptic_hypothesis_leak_and_non_sequitur(self):
        """Feature 11: AdversarialSkeptic catches hypothesis leaks across proof scopes."""
        skeptic_mod = pytest.importorskip("autonomous_math.prover.skeptic")
        dag_mod = pytest.importorskip("autonomous_math.prover.dag")
        AdversarialSkeptic = getattr(skeptic_mod, "AdversarialSkeptic")
        ProofNode = getattr(dag_mod, "ProofNode")
        DeductionStep = getattr(dag_mod, "DeductionStep")

        skeptic = AdversarialSkeptic()

        # Premise has local assumption 'is_bipartite', but target claims property for general graphs
        premise_node = ProofNode(
            node_id="premise_bipartite",
            label="Bipartite graph has chi <= 2",
            statement_latex=r"\chi(G) \le 2",
            statement_lean="G.chromaticNumber <= 2",
            node_type="SUB_LEMMA",
            scope={"assumptions": ["is_bipartite"]},
        )
        target_node = ProofNode(
            node_id="target_unconstrained",
            label="All graphs have chi <= 2",
            statement_latex=r"\chi(G) \le 2",
            statement_lean="G.chromaticNumber <= 2",
            node_type="TARGET_CONJECTURE",
            scope={"assumptions": []},
        )

        step = DeductionStep(
            step_id="leak_step",
            target_node_id=target_node.node_id,
            premise_node_ids=[premise_node.node_id],
            rule_type="SUBSTITUTION",
            rule_name="LeakedScope",
            justification="Generalizing bipartite claim",
        )

        has_leak, critique = skeptic.check_hypothesis_leak(step, [premise_node], target_node)
        assert has_leak is True or "leak" in (critique or "").lower()

    def test_r3_f12_prover_skeptic_search_loop_completes_proof(self):
        """Feature 12: ProverSkepticSearch constructs and verifies proof of greedy bound."""
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        ProverSkepticSearch = getattr(search_mod, "ProverSkepticSearch")
        Conjecture = getattr(ast_mod, "Conjecture")
        InvariantNode = getattr(ast_mod, "InvariantNode")
        ConstantNode = getattr(ast_mod, "ConstantNode")
        BinaryOpNode = getattr(ast_mod, "BinaryOpNode")

        conj = Conjecture(
            id="conj_greedy_bound",
            statement="chi <= Delta + 1",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=BinaryOpNode("+", InvariantNode("max_degree"), ConstantNode(1.0)),
            complexity=3,
        )

        prover = ProverSkepticSearch()
        proof_result = prover.prove(conj, max_depth=4)

        assert proof_result.status == "PROVEN"
        assert len(proof_result.minimal_proof_tree) > 0
        assert proof_result.dag is not None


# ============================================================================
# REQUIREMENT R4: DUAL OUTPUT ARTIFACT GENERATION (FEATURES 13-15)
# ============================================================================

class TestRequirementR4DualOutputGeneration:
    """Feature coverage for R4: LaTeX Preprint, Lean 4 Comparator, Syntax Validator."""

    def test_r4_f13_latex_preprint_generation_structure(self, tmp_path, graph_c5):
        """Feature 13: LatexPreprintGenerator produces modular LaTeX manuscript with all required files."""
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        sieve_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")
        SieveResult = getattr(sieve_mod, "SieveResult")
        CounterexampleCertificate = getattr(sieve_mod, "CounterexampleCertificate")
        Conjecture = getattr(ast_mod, "Conjecture")

        conj = Conjecture(
            id="conj_c5_test",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ast_mod.ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        cert = CounterexampleCertificate(
            conjecture_id="conj_c5_test",
            graph_order=5,
            graph_size=5,
            adjacency_matrix=nx.to_numpy_array(graph_c5, dtype=int).tolist(),
            edges=list(graph_c5.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 3},
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 4, 0]},
            verification_hash="hash_test",
        )

        result = SieveResult(
            status="REFUTED",
            conjecture=conj,
            tested_instances_count=1,
            counterexample_certificate=cert,
        )

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(result, output_dir=tmp_path / "paper")

        assert (out_dir / "main.tex").exists()
        assert (out_dir / "preamble.tex").exists()
        assert (out_dir / "references.bib").exists()
        assert (out_dir / "figures" / "lemma_dag.tex").exists()
        assert (out_dir / "sections" / "abstract.tex").exists()
        assert (out_dir / "sections" / "introduction.tex").exists()
        assert (out_dir / "sections" / "formulation.tex").exists()
        assert (out_dir / "sections" / "proof_or_cert.tex").exists()

    def test_r4_f13_latex_preprint_tikz_dag_and_matrix_rendering(self, tmp_path, graph_c5):
        """Feature 13: Generated LaTeX includes valid TikZ environment and counterexample matrix."""
        latex_mod = pytest.importorskip("autonomous_math.export.latex_generator")
        sieve_mod = pytest.importorskip("autonomous_math.sieve.certificates")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        LatexPreprintGenerator = getattr(latex_mod, "LatexPreprintGenerator")

        conj = ast_mod.Conjecture(
            id="c5_claim", statement="claim", lhs_expr=ast_mod.ConstantNode(1.0),
            rel="<=", rhs_expr=ast_mod.ConstantNode(2.0), complexity=1
        )
        cert = sieve_mod.CounterexampleCertificate(
            conjecture_id="c5_claim", graph_order=5, graph_size=5,
            adjacency_matrix=nx.to_numpy_array(graph_c5, dtype=int).tolist(),
            edges=list(graph_c5.edges()),
            invariants={}, refutation_witness={"type": "odd_cycle", "details": []},
            verification_hash="h",
        )
        res = sieve_mod.SieveResult(status="REFUTED", conjecture=conj, tested_instances_count=1, counterexample_certificate=cert)

        gen = LatexPreprintGenerator()
        out_dir = gen.generate(res, output_dir=tmp_path / "paper_tikz")

        tikz_content = (out_dir / "figures" / "lemma_dag.tex").read_text()
        assert "\\begin{tikzpicture}" in tikz_content
        assert "\\end{tikzpicture}" in tikz_content

        proof_tex = (out_dir / "sections" / "proof_or_cert.tex").read_text()
        assert "pmatrix" in proof_tex or "matrix" in proof_tex

    def test_r4_f14_lean4_comparator_json_schema_compliance(self, tmp_path):
        """Feature 14: Lean 4 JSON export matches exact schema from math/lean/ComparatorChallenges."""
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        prover_mod = pytest.importorskip("autonomous_math.prover.dag")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")

        conj = ast_mod.Conjecture(
            id="chromatic_bound", statement="chi <= Delta + 1",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"), rel="<=",
            rhs_expr=ast_mod.BinaryOpNode("+", ast_mod.InvariantNode("max_degree"), ast_mod.ConstantNode(1.0)),
            complexity=3
        )
        proof_res = search_mod.ProofResult(
            conjecture=conj,
            dag=prover_mod.LemmaDAG(root_node_id="root"),
            status="PROVEN",
            minimal_proof_tree=[],
            critique_summary={},
        )

        gen = LeanComparatorGenerator()
        json_path, lean_path = gen.generate(proof_res, output_dir=tmp_path / "lean")

        assert json_path.exists()
        assert lean_path.exists()

        is_valid, errors = ReferenceArtifactValidator.validate_lean_comparator_json(json_path.read_text())
        assert is_valid, f"Lean comparator JSON schema violations: {errors}"

    def test_r4_f14_lean4_scaffolding_mathlib_syntax(self, tmp_path):
        """Feature 14: Lean 4 scaffold contains valid Mathlib SimpleGraph theorem syntax."""
        lean_mod = pytest.importorskip("autonomous_math.export.lean_generator")
        ast_mod = pytest.importorskip("autonomous_math.core.ast")
        search_mod = pytest.importorskip("autonomous_math.prover.search")
        prover_mod = pytest.importorskip("autonomous_math.prover.dag")
        LeanComparatorGenerator = getattr(lean_mod, "LeanComparatorGenerator")

        conj = ast_mod.Conjecture(
            id="chi_le_delta_plus_one", statement="chi <= Delta + 1",
            lhs_expr=ast_mod.InvariantNode("chromatic_number"), rel="<=",
            rhs_expr=ast_mod.ConstantNode(3.0), complexity=2
        )
        res = search_mod.ProofResult(
            conjecture=conj, dag=prover_mod.LemmaDAG(root_node_id="root"),
            status="PROVEN", minimal_proof_tree=[], critique_summary={}
        )

        gen = LeanComparatorGenerator()
        _, lean_path = gen.generate(res, output_dir=tmp_path / "lean_syntax")

        lean_code = lean_path.read_text()
        is_valid, errors = ReferenceArtifactValidator.validate_lean_source(lean_code)
        assert is_valid, f"Lean source syntax errors: {errors}"

    def test_r4_f15_artifact_syntax_and_integrity_validation(self, tmp_path):
        """Feature 15: OutputSyntaxValidator accurately detects both valid and corrupt outputs."""
        validator_mod = pytest.importorskip("autonomous_math.export.validator")
        OutputSyntaxValidator = getattr(validator_mod, "OutputSyntaxValidator")

        # Clean LaTeX
        clean_latex = (
            "\\begin{document}\n"
            "\\begin{theorem}\nClaim.\n\\end{theorem}\n"
            "\\end{document}\n"
        )
        valid, errs = OutputSyntaxValidator.validate_latex_content(clean_latex)
        assert valid is True
        assert len(errs) == 0

        # Corrupt LaTeX (unclosed theorem environment)
        corrupt_latex = (
            "\\begin{document}\n"
            "\\begin{theorem}\nClaim.\n"
            "\\end{document}\n"
        )
        corrupt_valid, corrupt_errs = OutputSyntaxValidator.validate_latex_content(corrupt_latex)
        assert corrupt_valid is False
        assert len(corrupt_errs) > 0


# ============================================================================
# REQUIREMENT R5: ORCHESTRATION CLI & AUTOMATED VERIFICATION (FEATURES 16-17)
# ============================================================================

class TestRequirementR5OrchestrationCLI:
    """Feature coverage for R5: Unified CLI Entrypoint and Discovery Demonstrations."""

    def test_r5_f16_cli_conjecture_subcommand(self, tmp_path):
        """Feature 16: CLI conjecture subcommand generates candidates."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        out_file = tmp_path / "conjectures.json"
        exit_code = main_entry(["conjecture", "--limit", "5", "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

    def test_r5_f16_cli_sieve_subcommand(self, tmp_path):
        """Feature 16: CLI sieve subcommand filters candidate conjectures."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        conj_file = tmp_path / "test_conj.json"
        conj_file.write_text(json.dumps([
            {"id": "c1", "statement": "alpha * omega >= n", "rel": ">=", "complexity": 3}
        ]))
        out_file = tmp_path / "sieve_results.json"

        exit_code = main_entry(["sieve", "--input", str(conj_file), "--output", str(out_file)])
        assert exit_code == 0
        assert out_file.exists()

    def test_r5_f16_cli_prove_subcommand(self, tmp_path):
        """Feature 16: CLI prove subcommand executes proof search."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        conj_file = tmp_path / "to_prove.json"
        conj_file.write_text(json.dumps({
            "id": "c_prove", "statement": "chi <= Delta + 1", "rel": "<=", "complexity": 3
        }))
        out_file = tmp_path / "proof.json"

        exit_code = main_entry(["prove", "--input", str(conj_file), "--output", str(out_file)])
        assert exit_code == 0

    def test_r5_f16_cli_export_subcommand(self, tmp_path):
        """Feature 16: CLI export subcommand produces preprint and Lean comparator files."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        res_file = tmp_path / "proof_result.json"
        res_file.write_text(json.dumps({
            "conjecture": {"id": "c_export", "statement": "chi <= Delta + 1"},
            "status": "PROVEN",
            "minimal_proof_tree": []
        }))
        out_dir = tmp_path / "exports"

        exit_code = main_entry(["export", "--input", str(res_file), "--output-dir", str(out_dir)])
        assert exit_code == 0

    def test_r5_f17_cli_demo_subcommand_exits_zero(self):
        """Feature 17: CLI demo runs discovery pipeline and exits with code 0."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        exit_code = main_entry(["demo", "--scenario", "c5_refutation"])
        assert exit_code == 0

    def test_r5_cli_invalid_arguments_exit_code(self):
        """Feature 16: CLI returns standardized non-zero exit code on invalid arguments."""
        cli_mod = pytest.importorskip("autonomous_math.cli.main")
        main_entry = getattr(cli_mod, "main")

        with pytest.raises(SystemExit) as exc_info:
            main_entry(["--unknown-flag-12345"])
        assert exc_info.value.code != 0
