"""Unit tests for CounterexampleCertificate, SieveResult, and Verifier (Feature 7)."""

from __future__ import annotations

import json
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
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    CounterexampleCertificateVerifier,
    SieveResult,
    build_c5_counterexample_certificate,
)


class TestCounterexampleCertificateModel:
    """Tests for CounterexampleCertificate data model and serialization."""

    def test_c5_certificate_factory(self):
        """Test build_c5_counterexample_certificate produces valid C5 certificate."""
        cert = build_c5_counterexample_certificate()
        assert cert.conjecture_id == "triangle_free_not_two_colorable"
        assert cert.graph_order == 5
        assert cert.graph_size == 5
        assert len(cert.edges) == 5
        assert len(cert.adjacency_matrix) == 5
        assert cert.invariants["is_triangle_free"] is True
        assert cert.invariants["chromatic_number"] == 3
        assert cert.refutation_witness["type"] == "odd_cycle"
        assert cert.refutation_witness["details"] == [0, 1, 2, 3, 4, 0]
        assert len(cert.verification_hash) == 64  # SHA-256 hex digest

    def test_to_dict_and_roundtrip(self):
        """Test serialization to dict and reconstruction."""
        cert = build_c5_counterexample_certificate("custom_id")
        d = cert.to_dict()
        assert d["conjecture_id"] == "custom_id"
        assert d["graph_order"] == 5

        reconstructed = CounterexampleCertificate.from_dict(d)
        assert reconstructed.conjecture_id == cert.conjecture_id
        assert reconstructed.edges == cert.edges
        assert reconstructed.adjacency_matrix == cert.adjacency_matrix

    def test_to_json_and_roundtrip(self):
        """Test JSON string serialization and reconstruction."""
        cert = build_c5_counterexample_certificate()
        json_str = cert.to_json()
        assert isinstance(json_str, str)

        reconstructed = CounterexampleCertificate.from_json(json_str)
        assert reconstructed.graph_order == 5
        assert reconstructed.graph_size == 5
        assert reconstructed.verification_hash == cert.verification_hash

    def test_to_networkx_conversion(self):
        """Test conversion of certificate to NetworkX Graph."""
        cert = build_c5_counterexample_certificate()
        G = cert.to_networkx()
        assert isinstance(G, nx.Graph)
        assert G.number_of_nodes() == 5
        assert G.number_of_edges() == 5
        assert nx.is_isomorphic(G, nx.cycle_graph(5))

    def test_to_graph_instance_conversion(self):
        """Test conversion of certificate to GraphInstance."""
        cert = build_c5_counterexample_certificate()
        gi = cert.to_graph_instance()
        assert gi.order == 5
        assert gi.size == 5
        assert len(gi.edges) == 5
        assert (0, 1) in gi.edges

    def test_to_latex_matrix(self):
        """Test LaTeX pmatrix rendering."""
        cert = build_c5_counterexample_certificate()
        latex = cert.to_latex_matrix()
        assert "\\begin{pmatrix}" in latex
        assert "\\end{pmatrix}" in latex
        assert "0 & 1 & 0 & 0 & 1" in latex

        # Empty matrix test
        empty_cert = CounterexampleCertificate(
            conjecture_id="empty",
            graph_order=0,
            graph_size=0,
            adjacency_matrix=[],
            edges=[],
        )
        assert "\\begin{pmatrix}\\end{pmatrix}" == empty_cert.to_latex_matrix()

    def test_from_counterexample_graph_factory(self):
        """Test creating certificate directly from a NetworkX graph."""
        c5 = nx.cycle_graph(5)
        conj = Conjecture(
            id="conj_tf",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )
        cert = CounterexampleCertificate.from_counterexample_graph(c5, conj)
        assert cert.graph_order == 5
        assert cert.graph_size == 5
        assert cert.conjecture_id == "conj_tf"
        assert cert.refutation_witness["type"] == "odd_cycle"


class TestSieveResultModel:
    """Tests for SieveResult container."""

    def test_sieve_result_properties(self):
        """Test status predicates and defaults."""
        conj = Conjecture(
            id="test_conj",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        survived = SieveResult(
            status="SURVIVED",
            conjecture=conj,
            tested_instances_count=100,
        )
        assert survived.is_survived is True
        assert survived.is_refuted is False
        assert survived.counterexample_certificate is None
        assert survived.execution_time_ms == 0.0

        cert = build_c5_counterexample_certificate(conj.id)
        refuted = SieveResult(
            status="REFUTED",
            conjecture=conj,
            tested_instances_count=50,
            counterexample_certificate=cert,
            execution_time_ms=1.5,
        )
        assert refuted.is_refuted is True
        assert refuted.is_survived is False
        assert refuted.counterexample_certificate is not None
        assert refuted.execution_time_ms == 1.5

    def test_sieve_result_serialization(self):
        """Test SieveResult serialization to and from dict/json."""
        conj = Conjecture(
            id="test_conj",
            statement="chi >= omega",
            lhs_expr=InvariantNode("chromatic_number"),
            rel=">=",
            rhs_expr=InvariantNode("clique_number"),
            complexity=2,
        )
        cert = build_c5_counterexample_certificate(conj.id)
        res = SieveResult(
            status="REFUTED",
            conjecture=conj,
            tested_instances_count=42,
            counterexample_certificate=cert,
        )
        d = res.to_dict()
        assert d["status"] == "REFUTED"
        assert d["tested_instances_count"] == 42

        reconstructed = SieveResult.from_dict(d)
        assert reconstructed.status == "REFUTED"
        assert reconstructed.tested_instances_count == 42


class TestCounterexampleCertificateVerifier:
    """Tests for independent 5-step verification logic."""

    @pytest.fixture
    def target_conjecture(self):
        return Conjecture(
            id="tf_two_colorable",
            statement="Triangle-free graphs are 2-colorable",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

    def test_valid_c5_certificate_verifies_true(self, target_conjecture):
        """Genuine C5 certificate refuting triangle-free 2-colorability passes verification."""
        cert = build_c5_counterexample_certificate(target_conjecture.id)
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is True
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is True
        assert len(errs) == 0

    def test_step1_rejects_asymmetric_matrix(self, target_conjecture):
        """Step 1 catches asymmetric adjacency matrix."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, 1], [0, 0]],  # Asymmetric!
            edges=[(0, 1)],
            verification_hash="mock",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, err = CounterexampleCertificateVerifier.verify_matrix_structure(cert)
        assert ok is False
        assert "asymmetric" in (err or "").lower()

    def test_step1_rejects_dimension_mismatch(self, target_conjecture):
        """Step 1 catches dimension mismatch between graph_order and matrix rows."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=3,
            graph_size=1,
            adjacency_matrix=[[0, 1], [1, 0]],  # Only 2 rows for order 3!
            edges=[(0, 1)],
            verification_hash="mock",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, err = CounterexampleCertificateVerifier.verify_matrix_structure(cert)
        assert ok is False
        assert "does not match" in (err or "").lower()

    def test_step1_rejects_self_loops(self, target_conjecture):
        """Step 1 catches non-zero diagonal entries."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[1, 0], [0, 0]],  # Diagonal self loop!
            edges=[(0, 0)],
            verification_hash="mock",
        )
        ok, err = CounterexampleCertificateVerifier.verify_matrix_structure(cert)
        assert ok is False
        assert "self-loop" in (err or "").lower()

    def test_step2_rejects_edge_list_mismatch(self, target_conjecture):
        """Step 2 catches mismatch between edges list and matrix."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, 1], [1, 0]],
            edges=[(0, 1), (1, 0)],  # Duplicate / wrong size!
            verification_hash="mock",
        )
        ok, err = CounterexampleCertificateVerifier.verify_edge_consistency(cert)
        assert ok is False
        assert "does not match graph_size" in (err or "").lower()

    def test_step3_rejects_premise_violation(self, target_conjecture):
        """Step 3 rejects certificate containing triangles when premise is is_triangle_free."""
        # K3 contains a triangle, so premise is_triangle_free does not hold
        k3 = nx.complete_graph(3)
        adj = nx.to_numpy_array(k3, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=3,
            graph_size=3,
            adjacency_matrix=adj,
            edges=list(k3.edges()),
            verification_hash="mock",
        )
        G = cert.to_networkx()
        ok, err = CounterexampleCertificateVerifier.verify_premise_guard(cert, target_conjecture, G)
        assert ok is False
        assert "is_triangle_free" in (err or "").lower()

    def test_step4_rejects_fake_odd_cycle(self, target_conjecture):
        """Step 4 rejects odd cycle witness containing missing edges or even length."""
        cert = build_c5_counterexample_certificate(target_conjecture.id)
        # Tamper with witness details: claim cycle [0, 2, 4, 0] (no edge between 0 and 2)
        tampered_cert = CounterexampleCertificate(
            conjecture_id=cert.conjecture_id,
            graph_order=cert.graph_order,
            graph_size=cert.graph_size,
            adjacency_matrix=cert.adjacency_matrix,
            edges=cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 2, 4, 0]},
            verification_hash="mock",
        )
        G = tampered_cert.to_networkx()
        ok, err = CounterexampleCertificateVerifier.verify_refutation_witness(tampered_cert, target_conjecture, G)
        assert ok is False
        assert "does not exist in graph" in (err or "").lower()

    def test_step5_rejects_graph_satisfying_conjecture(self, target_conjecture):
        """Step 5 rejects graph if the conjecture actually holds on it (e.g. K2 has chi=2 <= 2)."""
        k2 = nx.complete_graph(2)
        adj = nx.to_numpy_array(k2, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=adj,
            edges=list(k2.edges()),
            invariants={"triangle_count": 0, "chromatic_number": 2},
            refutation_witness={"type": "direct_evaluation", "details": None},
            verification_hash="mock",
        )
        G = cert.to_networkx()
        ok, err = CounterexampleCertificateVerifier.verify_conjecture_refutation(cert, target_conjecture, G)
        assert ok is False
        assert "conjecture holds on graph" in (err or "").lower()
        # Full verify returns False
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
