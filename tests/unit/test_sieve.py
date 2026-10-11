"""Unit tests for InstanceDatabase, CEGARSieve, Z3Sieve, and EmpiricalSieveRunner (Features 5 & 6)."""

from __future__ import annotations

import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.sieve.cegar import CEGARSieve
from autonomous_math.sieve.certificates import (
    CounterexampleCertificateVerifier,
    SieveResult,
)
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.z3_sieve import EmpiricalSieveRunner, Z3Sieve


class TestInstanceDatabase:
    """Tests for InstanceDatabase catalog and vectorized sieving (Feature 5)."""

    def test_database_population_and_size(self):
        """Database contains 1,000+ cached instances across multiple graph families."""
        db = InstanceDatabase()
        instances = db.get_instances()
        assert len(instances) >= 1000
        assert len(db) == len(instances)

        # Check graph instances and invariants
        gi_list = db.get_graph_instances()
        assert len(gi_list) == len(instances)
        invs = db.get_precomputed_invariants()
        assert len(invs) == len(instances)

        # Verify table of arrays
        table = db.get_invariants_table()
        assert "order" in table
        assert "chromatic_number" in table
        assert "clique_number" in table
        assert len(table["order"]) == len(instances)

    def test_database_family_diversity(self):
        """Database includes cycles, cliques, bipartite, Turan, Mycielski, Paley, SRG, and random."""
        db = InstanceDatabase()
        instances = db.get_instances()
        names = [getattr(g, "name", "") for g in instances]

        has_cycles = any("C_" in n for n in names)
        has_cliques = any("K_" in n for n in names)
        has_turan = any("Turan_" in n for n in names)
        has_mycielski = any("Mycielski_" in n for n in names)
        has_paley = any("Paley_" in n for n in names)
        has_petersen = any("Petersen" in n for n in names)
        has_clebsch = any("Clebsch" in n for n in names)
        has_random = any("ER_" in n or "RR_" in n for n in names)

        assert has_cycles is True
        assert has_cliques is True
        assert has_turan is True
        assert has_mycielski is True
        assert has_paley is True
        assert has_petersen is True
        assert has_clebsch is True
        assert has_random is True

    def test_add_custom_instance(self):
        """Test dynamically adding a custom graph instance."""
        db = InstanceDatabase()
        initial_count = len(db)

        # Add wheel graph
        w5 = nx.wheel_graph(5)
        w5.name = "CustomWheel5"
        db.add_instance(w5)

        assert len(db) == initial_count + 1
        instances = db.get_instances()
        assert instances[-1].name == "CustomWheel5"

    def test_vectorized_sieve_true_theorem_survives(self):
        """Universal theorem chi >= omega must survive across all catalog graphs."""
        db = InstanceDatabase()
        conj = Conjecture(
            id="clique_chromatic_theorem",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None
        assert res.tested_instances_count == len(db)
        assert res.execution_time_ms < 20.0  # sub-20ms vectorized scan

    def test_vectorized_sieve_false_conjecture_refuted(self):
        """False bound alpha * omega >= n is refuted with valid certificate."""
        db = InstanceDatabase()
        conj = Conjecture(
            id="false_ramsey_bound",
            statement="alpha * omega >= n",
            lhs_expr=BinaryOpNode("*", InvariantNode("independence_number"), InvariantNode("clique_number")),
            rel=">=",
            rhs_expr=InvariantNode("order"),
            complexity=3,
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.conjecture_id == conj.id
        assert res.tested_instances_count > 0
        assert CounterexampleCertificateVerifier.verify(res.counterexample_certificate, conj) is True

    def test_guarded_conjecture_sieve(self):
        """Premise-guarded claim: triangle-free graphs have chi <= 2 is refuted."""
        db = InstanceDatabase()
        conj = Conjecture(
            id="tf_two_colorable",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.invariants["is_triangle_free"] is True
        assert cert.invariants["chromatic_number"] > 2
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_batch_sieve_conjectures(self):
        """Test batch sieving of multiple conjectures."""
        db = InstanceDatabase()
        conj1 = Conjecture(
            id="c1",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        conj2 = Conjecture(
            id="c2",
            statement="alpha * omega >= n",
            lhs_expr=BinaryOpNode("*", InvariantNode("independence_number"), InvariantNode("clique_number")),
            rel=">=",
            rhs_expr=InvariantNode("order"),
            complexity=3,
        )

        results = db.sieve_conjectures([conj1, conj2])
        assert len(results) == 2
        assert results[0].status == "SURVIVED"
        assert results[1].status == "REFUTED"


class TestCEGARSieve:
    """Tests for CEGARSieve graph synthesis (Feature 6)."""

    def test_synthesize_c5_counterexample(self):
        """CEGAR synthesizes C5 for triangle-free non-2-colorability."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=5,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
        )
        assert witness is not None
        assert witness.number_of_nodes() == 5
        assert witness.number_of_edges() == 5
        # Must be triangle-free and non-bipartite
        assert nx.triangles(witness) == {i: 0 for i in witness.nodes()}
        assert not nx.is_bipartite(witness)
        assert nx.is_isomorphic(witness, nx.cycle_graph(5))

    def test_find_odd_cycle_witness(self):
        """Test extracting odd cycle walk from synthesized graph."""
        sieve = CEGARSieve()
        c5 = nx.cycle_graph(5)
        walk = sieve.find_odd_cycle_witness(c5)
        assert len(walk) == 6  # 5 vertices + closed return
        assert walk[0] == walk[-1]
        assert len(set(walk[:-1])) == 5

    def test_infeasible_order_returns_none(self):
        """Order <= 4 cannot contain a triangle-free graph with chi >= 3."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=4,
            is_triangle_free=True,
            target_chromatic_lower_bound=3,
        )
        assert witness is None

    def test_trivial_chromatic_bound(self):
        """target_chromatic_lower_bound=2 returns a graph with at least 1 edge."""
        sieve = CEGARSieve()
        witness = sieve.synthesize_counterexample(
            max_order=3,
            is_triangle_free=True,
            target_chromatic_lower_bound=2,
        )
        assert witness is not None
        assert witness.number_of_edges() >= 1


class TestZ3SieveAndEmpiricalRunner:
    """Tests for Z3Sieve and EmpiricalSieveRunner coordination."""

    def test_z3_sieve_chromatic_bound(self):
        """Z3Sieve refutes chi <= 2 on triangle-free graphs via CEGAR."""
        z3_sieve = Z3Sieve()
        conj = Conjecture(
            id="conj_tf_chi_le_2",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

        res = z3_sieve.sieve_conjecture(conj, max_order=5)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.counterexample_certificate.graph_order == 5
        assert res.counterexample_certificate.refutation_witness["type"] == "odd_cycle"

    def test_empirical_sieve_runner_tier1_hit(self):
        """EmpiricalSieveRunner uses Tier 1 database first when counterexample is pre-cached."""
        runner = EmpiricalSieveRunner()
        conj = Conjecture(
            id="false_ramsey_bound",
            statement="alpha * omega >= n",
            lhs_expr=BinaryOpNode("*", InvariantNode("independence_number"), InvariantNode("clique_number")),
            rel=">=",
            rhs_expr=InvariantNode("order"),
            complexity=3,
        )

        res = runner.run(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        assert res.tested_instances_count > 0

    def test_empirical_sieve_runner_surviving_claim(self):
        """EmpiricalSieveRunner evaluates valid theorem chi >= omega."""
        runner = EmpiricalSieveRunner()
        conj = Conjecture(
            id="true_clique_bound",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )

        res = runner.run(conj, max_smt_order=3)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None
