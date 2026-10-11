"""Adversarial stress-testing suite for CEGARSieve, Z3Sieve, and EmpiricalSieveRunner.

Specifically targets:
1. CEGAR synthesis under varying constraints:
   - max_order=4, is_triangle_free=True, target_chromatic_lower_bound=3 (must return None / UNSAT).
   - max_order=5, is_triangle_free=True, target_chromatic_lower_bound=3 (must return graph strictly isomorphic to C5).
   - target_chromatic_lower_bound=4, is_triangle_free=True with max_order=5 (must return None / UNSAT, Grötzsch requires n=11).
   - Non-triangle-free variations (K3, K4) and boundary bounds.
2. Timeout resilience:
   - Tight timeout_ms (50ms, 10ms, 1ms, 0ms, negative) to ensure graceful None return instead of unhandled exceptions.
   - Order boundary inputs (order <= 0, target > max_order).
3. Z3Sieve synthesis & general bounded SMT search:
   - String guard vs GuardPredicate object.
   - Chromatic alias handling ("chi" vs "chromatic_number").
   - Certificate generation and independent 5-step verification.
4. EmpiricalSieveRunner two-tier coordination:
   - Tier 1 catches database counterexamples without invoking SMT.
   - Tier 2 invokes SMT when enabled and Tier 1 misses.
   - Fallback disabling prevents Tier 2 SMT invocation.
   - Cumulative instance counting across tiers.
"""

from __future__ import annotations

import time
from typing import Optional
from unittest.mock import MagicMock

import networkx as nx
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.sieve.cegar import CEGARSieve
from autonomous_math.sieve.certificates import (
    CounterexampleCertificateVerifier,
    SieveResult,
)
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.z3_sieve import EmpiricalSieveRunner, Z3Sieve


# ============================================================================
# 1. CEGAR Synthesis Under Varying Constraints
# ============================================================================


class TestCEGARSieveAdversarialConstraints:
    """Stress-tests for CEGARSieve under varying mathematical constraints."""

    def test_cegar_synthesis_order_4_triangle_free_chi_3_returns_none(self):
        """Order <= 4 triangle-free graphs are strictly bipartite; chi >= 3 is UNSAT."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=4,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
            timeout_ms=5000,
        )
        assert witness is None, (
            f"Expected None for max_order=4, triangle-free, chi>=3, but got {witness}"
        )

    def test_cegar_synthesis_order_5_triangle_free_chi_3_returns_strictly_c5(self):
        """Order 5 triangle-free graph with chi >= 3 must be strictly isomorphic to C5."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
            timeout_ms=5000,
        )
        assert witness is not None, "CEGAR failed to synthesize C5 counterexample"
        assert witness.number_of_nodes() == 5, f"Expected 5 nodes, got {witness.number_of_nodes()}"
        assert witness.number_of_edges() == 5, f"Expected 5 edges, got {witness.number_of_edges()}"

        # Invariant checks: 2-regular, triangle-free, non-bipartite
        degrees = [d for _, d in witness.degree()]
        assert all(d == 2 for d in degrees), f"Expected 2-regular graph, got degrees {degrees}"
        assert nx.triangles(witness) == {i: 0 for i in witness.nodes()}, "Graph contains triangles!"
        assert not nx.is_bipartite(witness), "Graph must be non-bipartite (has odd cycle)"

        # Strict isomorphism to cycle graph C_5
        c5 = nx.cycle_graph(5)
        assert nx.is_isomorphic(witness, c5), "Witness is not isomorphic to C5!"

    def test_cegar_synthesis_order_5_triangle_free_chi_4_returns_none(self):
        """Order 5 triangle-free cannot have chi >= 4 (Grötzsch graph requires n=11)."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=4,
            timeout_ms=5000,
        )
        assert witness is None, (
            f"Expected None for order 5 triangle-free chi>=4, but got {witness}"
        )

    def test_cegar_synthesis_order_6_and_7_triangle_free_chi_4_returns_none(self):
        """Order 6 and 7 triangle-free graphs cannot have chi >= 4."""
        sieve = CEGARSieve()
        for order in [6, 7]:
            witness = sieve.synthesize_counterexample(
                max_order=order,
                min_order=order,
                is_triangle_free=True,
                target_chromatic_lower_bound=4,
                timeout_ms=4000,
            )
            assert witness is None, (
                f"Expected None for order {order} triangle-free chi>=4, but got {witness}"
            )

    def test_cegar_non_triangle_free_order_3_chi_3_returns_k3(self):
        """Without triangle-free constraint, minimal chi >= 3 graph is K3."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=3,
            is_triangle_free=False,
            target_chromatic_lower_bound=3,
            timeout_ms=5000,
        )
        assert witness is not None
        assert witness.number_of_nodes() == 3
        assert witness.number_of_edges() == 3
        assert nx.is_isomorphic(witness, nx.complete_graph(3))

    def test_cegar_non_triangle_free_order_4_chi_4_returns_k4(self):
        """Without triangle-free constraint, minimal chi >= 4 graph is K4."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=4,
            is_triangle_free=False,
            target_chromatic_lower_bound=4,
            timeout_ms=5000,
        )
        assert witness is not None
        assert witness.number_of_nodes() == 4
        assert witness.number_of_edges() == 6
        assert nx.is_isomorphic(witness, nx.complete_graph(4))

    def test_cegar_non_triangle_free_order_2_chi_3_returns_none(self):
        """Order 2 cannot have chi >= 3."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=2,
            is_triangle_free=False,
            target_chromatic_lower_bound=3,
            timeout_ms=2000,
        )
        assert witness is None

    def test_cegar_trivial_lower_bound_2_returns_k2(self):
        """target_chromatic_lower_bound=2 returns a graph with at least 1 edge."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=2,
            is_triangle_free=True,
            target_chromatic_lower_bound=2,
            timeout_ms=2000,
        )
        assert witness is not None
        assert witness.number_of_nodes() == 2
        assert witness.number_of_edges() == 1

    def test_cegar_trivial_lower_bound_1_returns_edge_graph_at_order_2(self):
        """target_chromatic_lower_bound=1 returns a graph with at least 1 edge when max_order >= 2."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=2,
            is_triangle_free=True,
            target_chromatic_lower_bound=1,
            timeout_ms=2000,
        )
        assert witness is not None
        assert witness.number_of_nodes() == 2
        assert witness.number_of_edges() >= 1

    def test_cegar_order_1_simple_graph_no_edges_returns_none(self):
        """At max_order=1, simple graphs cannot have edges, so chromatic search returns None."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=1,
            is_triangle_free=True,
            target_chromatic_lower_bound=1,
            timeout_ms=2000,
        )
        assert witness is None

    def test_cegar_min_order_configuration(self):
        """min_order restricts the search window properly."""
        sieve = CEGARSieve()
        # min_order=5, max_order=5 synthesizes C5
        witness = sieve.synthesize_counterexample(
            max_order=5,
            min_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
        )
        assert witness is not None
        assert nx.is_isomorphic(witness, nx.cycle_graph(5))

        # min_order=6, max_order=5 is an invalid search window -> returns None
        witness_inv = sieve.synthesize_counterexample(
            max_order=5,
            min_order=6,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
        )
        assert witness_inv is None


# ============================================================================
# 2. Timeout and Boundary Resilience
# ============================================================================


class TestCEGARSieveTimeoutAndBoundaryResilience:
    """Stress-tests for timeout resilience and boundary parameter handling."""

    def test_cegar_timeout_resilience_50ms(self):
        """Tight 50ms timeout on impossible synthesis returns None without unhandled exception."""
        sieve = CEGARSieve()
        t0 = time.time()
        witness = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=4,
            timeout_ms=50,
        )
        elapsed_ms = (time.time() - t0) * 1000
        assert witness is None
        assert elapsed_ms < 1000  # Terminated quickly within grace threshold

    def test_cegar_timeout_resilience_tight_10ms_on_hard_query(self):
        """10ms timeout on larger order search terminates cleanly."""
        sieve = CEGARSieve()
        t0 = time.time()
        witness = sieve.synthesize_counterexample(
            max_order=8,
            is_triangle_free=True,
            target_chromatic_lower_bound=4,
            timeout_ms=10,
        )
        elapsed_ms = (time.time() - t0) * 1000
        assert witness is None
        assert elapsed_ms < 1000

    def test_cegar_timeout_resilience_1ms(self):
        """1ms timeout returns None cleanly."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
            timeout_ms=1,
        )
        assert witness is None

    def test_cegar_timeout_resilience_zero_and_negative(self):
        """0ms and negative timeouts return None immediately without crashing."""
        sieve = CEGARSieve()
        for t in [0, -1, -50]:
            witness = sieve.synthesize_counterexample(
                max_order=5,
                is_triangle_free=True,
                target_chromatic_lower_bound=3,
                timeout_ms=t,
            )
            assert witness is None

    def test_cegar_boundary_order_zero_and_negative(self):
        """max_order <= 0 returns None immediately."""
        sieve = CEGARSieve()
        assert sieve.synthesize_counterexample(max_order=0) is None
        assert sieve.synthesize_counterexample(max_order=-5) is None

    def test_cegar_boundary_target_exceeding_order(self):
        """target_chromatic_lower_bound > max_order returns None (pigeonhole principle)."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=4,
            is_triangle_free=False,
            target_chromatic_lower_bound=5,
        )
        assert witness is None

        witness_large = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=100,
        )
        assert witness_large is None

    def test_cegar_odd_cycle_witness_structure(self):
        """find_odd_cycle_witness returns valid closed odd cycles."""
        sieve = CEGARSieve()

        # C5 witness
        c5 = nx.cycle_graph(5)
        walk5 = sieve.find_odd_cycle_witness(c5)
        assert len(walk5) == 6, f"Expected length 6 for closed C5 walk, got {walk5}"
        assert walk5[0] == walk5[-1], "Walk must be closed"
        assert len(set(walk5[:-1])) == 5, "Walk must visit 5 distinct vertices"

        # C7 witness
        c7 = nx.cycle_graph(7)
        walk7 = sieve.find_odd_cycle_witness(c7)
        assert len(walk7) == 8
        assert walk7[0] == walk7[-1]
        assert len(set(walk7[:-1])) == 7


# ============================================================================
# 3. Z3Sieve Synthesis & General Bounded SMT Search
# ============================================================================


class TestZ3SieveAdversarial:
    """Stress-tests for Z3Sieve synthesis, guards, and certificate generation."""

    def test_z3_sieve_synthesize_c5_with_string_guard(self):
        """Z3Sieve synthesizes C5 when guard_predicate is a string 'is_triangle_free'."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_tf_chi_le_2_str",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=5)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 5
        assert cert.graph_size == 5
        assert cert.refutation_witness["type"] == "odd_cycle"
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_z3_sieve_synthesize_c5_with_guard_predicate_object(self):
        """Z3Sieve synthesizes C5 when guard_predicate is a GuardPredicate instance."""
        sieve = Z3Sieve()
        gp = GuardPredicate(predicate_type="property", property_name="is_triangle_free")
        conj = Conjecture(
            id="conj_tf_chi_le_2_obj",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate=gp,
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=5)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 5
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_z3_sieve_synthesize_c5_with_chi_alias(self):
        """Z3Sieve recognizes 'chi' invariant alias in conjecture."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_chi_alias",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chi"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=5)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.graph_order == 5

    def test_z3_sieve_triangle_free_chi_le_3_order_5_survives(self):
        """Bounded order 5 search finds no counterexample for chi <= 3 (status SURVIVED)."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_tf_chi_le_3",
            statement="is_triangle_free ==> chi <= 3",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(3.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=5)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None

    def test_z3_sieve_general_bounded_smt_search_order_bound(self):
        """General bounded SMT search refutes false conjecture n <= 2."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_order_le_2",
            statement="n <= 2",
            lhs_expr=InvariantNode("order"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=3)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.graph_order == 3
        assert CounterexampleCertificateVerifier.verify(res.counterexample_certificate, conj) is True

    def test_z3_sieve_general_bounded_smt_search_size_bound(self):
        """General bounded SMT search refutes false conjecture m <= 0."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_size_le_0",
            statement="m <= 0",
            lhs_expr=InvariantNode("size"),
            rel="<=",
            rhs_expr=ConstantNode(0.0),
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=2)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.graph_size >= 1
        assert CounterexampleCertificateVerifier.verify(res.counterexample_certificate, conj) is True

    def test_z3_sieve_tight_timeout_graceful_handling(self):
        """Z3Sieve handles tight timeout gracefully without throwing unhandled exceptions."""
        sieve = Z3Sieve()
        conj = Conjecture(
            id="hard_conjecture",
            statement="is_triangle_free ==> chi <= 3",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(3.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = sieve.sieve_conjecture(conj, max_order=7, timeout_ms=5)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None


# ============================================================================
# 4. EmpiricalSieveRunner Two-Tier Coordination
# ============================================================================


class TestEmpiricalSieveRunnerTwoTierCoordination:
    """Stress-tests for EmpiricalSieveRunner two-tier coordination."""

    def test_runner_tier1_hit_bypasses_smt_completely(self):
        """When Tier 1 instance database catches a counterexample, SMT is NOT invoked."""
        db = InstanceDatabase()
        mock_z3 = MagicMock(spec=Z3Sieve)
        runner = EmpiricalSieveRunner(instance_db=db, z3_sieve=mock_z3)

        # False Ramsey bound: alpha * omega >= n (refuted on Petersen / C5 in db)
        conj = Conjecture(
            id="false_ramsey_bound",
            statement="alpha * omega >= n",
            lhs_expr=BinaryOpNode(
                "*",
                InvariantNode("independence_number"),
                InvariantNode("clique_number"),
            ),
            rel=">=",
            rhs_expr=InvariantNode("order"),
            complexity=3,
        )

        t0 = time.time()
        res = runner.run(conj)
        elapsed_ms = (time.time() - t0) * 1000

        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        # Crucial check: SMT solver was NEVER called
        assert mock_z3.sieve_conjecture.call_count == 0
        assert mock_z3.synthesize_counterexample.call_count == 0
        assert elapsed_ms < 50.0  # Sub-50ms database lookup

    def test_runner_tier1_hit_guarded_conjecture_bypasses_smt(self):
        """Tier 1 catches triangle-free non-2-colorability without invoking SMT."""
        db = InstanceDatabase()
        mock_z3 = MagicMock(spec=Z3Sieve)
        runner = EmpiricalSieveRunner(instance_db=db, z3_sieve=mock_z3)

        conj = Conjecture(
            id="tf_chi_le_2",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = runner.run(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert mock_z3.sieve_conjecture.call_count == 0

    def test_runner_tier1_miss_tier2_fallback_invokes_smt_and_refutes(self):
        """When Tier 1 database misses counterexample, Tier 2 SMT is invoked and refutes."""
        # Custom mock DB that fails to find counterexample
        class MissDatabase:
            def sieve_conjecture(self, c: Conjecture) -> SieveResult:
                return SieveResult(
                    status="SURVIVED",
                    conjecture=c,
                    tested_instances_count=100,
                )

        real_z3 = Z3Sieve()
        runner = EmpiricalSieveRunner(
            instance_db=MissDatabase(),
            z3_sieve=real_z3,
            enable_z3_fallback=True,
        )

        conj = Conjecture(
            id="tf_chi_le_2_fallback",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = runner.run(conj, max_smt_order=5)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.graph_order == 5
        assert CounterexampleCertificateVerifier.verify(res.counterexample_certificate, conj) is True
        # Tested count includes Tier 1 (100) + Tier 2 (5 * 10 = 50)
        assert res.tested_instances_count == 150

    def test_runner_tier1_miss_tier2_disabled_does_not_invoke_smt_and_survives(self):
        """When Tier 2 is disabled, Tier 1 miss returns SURVIVED without invoking SMT."""
        mock_db = MagicMock()
        mock_conj = Conjecture(
            id="dummy_conj",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        mock_db.sieve_conjecture.return_value = SieveResult(
            status="SURVIVED",
            conjecture=mock_conj,
            tested_instances_count=50,
        )

        mock_z3 = MagicMock(spec=Z3Sieve)
        runner = EmpiricalSieveRunner(
            instance_db=mock_db,
            z3_sieve=mock_z3,
            enable_z3_fallback=False,  # SMT disabled
        )

        res = runner.run(mock_conj)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None
        assert mock_z3.sieve_conjecture.call_count == 0

    def test_runner_surviving_claim_accumulates_tested_counts(self):
        """Surviving claim across both tiers correctly accumulates tested instance counts."""
        db = InstanceDatabase()
        runner = EmpiricalSieveRunner(instance_db=db, enable_z3_fallback=True)

        conj = Conjecture(
            id="clique_chromatic_theorem",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        res = runner.run(conj, max_smt_order=3)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None
        # Tier 1 tested all catalog graphs (>= 1000), Tier 2 tested max_smt_order * 10
        assert res.tested_instances_count >= len(db) + 30

    def test_runner_grotzsch_tier1_refutation(self):
        """Grötzsch graph (M4) in database refutes triangle-free chi <= 3."""
        db = InstanceDatabase()
        runner = EmpiricalSieveRunner(instance_db=db)

        conj = Conjecture(
            id="tf_chi_le_3",
            statement="is_triangle_free ==> chi <= 3",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(3.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = runner.run(conj)
        assert res.status == "REFUTED"
        cert = res.counterexample_certificate
        assert cert is not None
        assert cert.graph_order == 11  # Grötzsch order
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True
