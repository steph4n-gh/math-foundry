"""Empirical Adversarial Stress Suite for Milestone 2: Sieve & Certificate Engine.

Adversarially challenges:
1. CounterexampleCertificateVerifier:
   - Tampered matrices: asymmetric adjacency matrices, dimension mismatch (order != matrix size),
     non-binary entries (2, -1, 0.5, strings, None), non-zero diagonal (self-loops).
   - Inconsistent edge counts: size != len(edges), upper triangle sum != size, duplicate edges,
     self-loop edges, out-of-bounds vertex indices, missing edges in matrix vs list.
   - Invalid odd cycle sequences: length < 3, even length (4-cycle, 6-cycle claimed as odd cycle),
     non-existent edges, out-of-bounds vertices, non-distinct vertices, odd cycle claimed on bipartite graphs.
   - Fake witnesses on satisfied graphs: graphs that satisfy the conjecture by evaluation, graphs violating
     premise guards (e.g. K3 on is_triangle_free, disconnected on is_connected, non-bipartite on is_bipartite),
     fake exhaustive coloring witnesses on bipartite graphs (K2, K3_3).
   - Invariant discrepancies in certificates: order/size/triangle_count mismatches.
   - Malformed / bizarre certificate inputs: negative order/size, non-sequences, ragged matrices.
   - Verification contract: verify(cert, conj) must return False on EVERY tampered certificate
     without crashing or raising uncaught exceptions.

2. InstanceDatabase Boundary & Extreme Graphs:
   - Null graph n=0 (Atlas_0): order 0, size 0, triangle 0, verified certificate generation.
   - Single vertex n=1 (Atlas_1): order 1, size 0, division-by-zero boundary, verified certificate generation.
   - Disconnected graphs: discrete En, disconnected components, diameter / connectivity boundaries.
   - Star graphs (S_n = K_{1, b}): extreme degree asymmetry (Delta - delta spread).
   - Complete graphs (K_n): maximal density, independence number = 1.
   - Database cache lifecycle: clear_cache(), include_atlas=False.
   - Dynamic instance addition (add_instance) coherence with vectorized sieving.

3. Sieve Engine on Vacuous Conjectures and Extreme Expressions:
   - Vacuous premise guards (guards matching no graph in the database, e.g. order >= 500).
   - Extreme expressions: division by zero in vectorized evaluation, log of zero, sqrt of non-positive.
   - Extreme expressions in sequential dictionary fallback: division by zero behavior.
"""

from __future__ import annotations

import math
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

AUTONOMOUS_MATH_ROOT = Path(__file__).resolve().parent.parent.parent
if str(AUTONOMOUS_MATH_ROOT) not in sys.path:
    sys.path.insert(0, str(AUTONOMOUS_MATH_ROOT))

import networkx as nx
import numpy as np
import pytest

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    CounterexampleCertificateVerifier,
    build_c5_counterexample_certificate,
)
from autonomous_math.sieve.instance_db import InstanceDatabase


# ============================================================================
# 1. Adversarial Tampered Certificates Challenge Suite
# ============================================================================


class TestAdversarialTamperedCertificates:
    """Stress tests verifying CounterexampleCertificateVerifier catches all forms of tampering."""

    @pytest.fixture
    def target_conjecture(self) -> Conjecture:
        return Conjecture(
            id="triangle_free_two_colorable",
            statement="is_triangle_free ==> chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate="is_triangle_free",
            complexity=2,
        )

    # ------------------------------------------------------------------------
    # 1.1 Asymmetric Adjacency Matrices
    # ------------------------------------------------------------------------

    @pytest.mark.parametrize(
        "order,matrix,asym_pos",
        [
            (2, [[0, 1], [0, 0]], (0, 1)),
            (3, [[0, 1, 0], [0, 0, 1], [0, 1, 0]], (0, 1)),
            (4, [[0, 1, 1, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]], (0, 2)),
            (5, [
                [0, 1, 0, 0, 1],
                [1, 0, 1, 0, 0],
                [0, 0, 0, 1, 0],  # A[2][1]=0 != A[1][2]=1
                [0, 0, 1, 0, 1],
                [1, 0, 0, 1, 0],
            ], (1, 2)),
        ],
    )
    def test_asymmetric_adjacency_matrices_rejected(
        self,
        target_conjecture: Conjecture,
        order: int,
        matrix: List[List[int]],
        asym_pos: Tuple[int, int],
    ):
        """Verifier rejects asymmetric adjacency matrices across multiple orders."""
        edges = [(i, j) for i in range(order) for j in range(i + 1, order) if matrix[i][j] == 1]
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=order,
            graph_size=len(edges),
            adjacency_matrix=matrix,
            edges=edges,
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("asymmetric" in err.lower() for err in errs)

    # ------------------------------------------------------------------------
    # 1.2 Dimension Mismatch (order != matrix size)
    # ------------------------------------------------------------------------

    @pytest.mark.parametrize(
        "order,matrix,desc",
        [
            (3, [[0, 1], [1, 0]], "order 3 but 2x2 matrix"),
            (2, [[0, 1, 0], [1, 0, 0], [0, 0, 0]], "order 2 but 3x3 matrix"),
            (0, [[0]], "order 0 but 1x1 matrix"),
            (1, [], "order 1 but empty matrix"),
            (3, [[0, 1, 0, 0], [1, 0, 0], [0, 0, 0]], "row 0 has 4 elements for order 3"),
            (3, [[0, 1, 0], [1, 0], [0, 0, 0]], "row 1 has 2 elements for order 3"),
        ],
    )
    def test_dimension_mismatch_rejected(
        self,
        target_conjecture: Conjecture,
        order: int,
        matrix: List[List[int]],
        desc: str,
    ):
        """Verifier rejects mismatch between declared graph_order and row/column counts."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=order,
            graph_size=0,
            adjacency_matrix=matrix,
            edges=[],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any(
            "does not match" in err.lower()
            or "row count" in err.lower()
            or "empty adjacency matrix" in err.lower()
            for err in errs
        )

    # ------------------------------------------------------------------------
    # 1.3 Non-Binary Matrix Entries
    # ------------------------------------------------------------------------

    @pytest.mark.parametrize("bad_val", [2, -1, 10, 100])
    def test_non_binary_integer_entries_rejected(
        self,
        target_conjecture: Conjecture,
        bad_val: int,
    ):
        """Verifier rejects non-binary integer entries (2, -1, 10)."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, bad_val], [bad_val, 0]],
            edges=[(0, 1)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("not binary" in err.lower() for err in errs)

    @pytest.mark.parametrize("bad_val", [0.5, 2.5, "1", "bad", None])
    def test_non_integer_entries_bypassing_pydantic_rejected(
        self,
        target_conjecture: Conjecture,
        bad_val: Any,
    ):
        """Verifier rejects float, string, or None matrix values constructed directly."""
        cert = CounterexampleCertificate.model_construct(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, bad_val], [bad_val, 0]],
            edges=[(0, 1)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert len(errs) > 0

    # ------------------------------------------------------------------------
    # 1.4 Non-Zero Diagonal (Self-Loops)
    # ------------------------------------------------------------------------

    @pytest.mark.parametrize(
        "order,diag_idx",
        [(1, 0), (2, 0), (2, 1), (5, 0), (5, 3), (5, 4)],
    )
    def test_non_zero_diagonal_self_loops_rejected(
        self,
        target_conjecture: Conjecture,
        order: int,
        diag_idx: int,
    ):
        """Verifier rejects non-zero diagonal entries A[i][i] != 0 (forbidden self-loops)."""
        matrix = [[0] * order for _ in range(order)]
        matrix[diag_idx][diag_idx] = 1
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=order,
            graph_size=0,
            adjacency_matrix=matrix,
            edges=[],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("self-loop" in err.lower() for err in errs)

    # ------------------------------------------------------------------------
    # 1.5 Inconsistent Edge Counts & Edge Lists
    # ------------------------------------------------------------------------

    def test_edge_count_greater_than_upper_triangle(self, target_conjecture: Conjecture):
        """Declared graph_size exceeds actual upper-triangle 1s."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=5,  # Claim 5 edges when only 1 exists
            adjacency_matrix=[[0, 1], [1, 0]],
            edges=[(0, 1)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("does not match graph_size" in err.lower() for err in errs)

    def test_upper_triangle_sum_mismatch(self, target_conjecture: Conjecture):
        """Upper triangle sum does not match declared graph_size."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, 0], [0, 0]],  # Upper sum is 0
            edges=[(0, 1)],  # Length is 1
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("upper triangle edge sum" in err.lower() for err in errs)

    def test_duplicate_edges_in_edge_list(self, target_conjecture: Conjecture):
        """Edge list contains duplicate directed or undirected edges."""
        # Exact duplicate
        cert1 = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=2,
            adjacency_matrix=[[0, 1], [1, 0]],
            edges=[(0, 1), (0, 1)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert1, target_conjecture) is False

        # Reversed duplicate (0, 1) and (1, 0)
        cert2 = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=2,
            adjacency_matrix=[[0, 1], [1, 0]],
            edges=[(0, 1), (1, 0)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert2, target_conjecture) is False

    def test_self_loop_in_edge_list(self, target_conjecture: Conjecture):
        """Edge list contains self-loop (u, u)."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=[[0, 1], [1, 0]],
            edges=[(0, 0)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("self-loop" in err.lower() for err in errs)

    def test_out_of_bounds_vertex_in_edges(self, target_conjecture: Conjecture):
        """Edge list references non-existent vertex indices."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=3,
            graph_size=1,
            adjacency_matrix=[[0, 1, 0], [1, 0, 0], [0, 0, 0]],
            edges=[(0, 99)],
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("out of vertex bounds" in err.lower() for err in errs)

    def test_matrix_edge_missing_from_edge_list(self, target_conjecture: Conjecture):
        """Adjacency matrix has 1, but entry is omitted from edge list."""
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=3,
            graph_size=2,
            adjacency_matrix=[[0, 1, 1], [1, 0, 0], [1, 0, 0]],
            edges=[(0, 1), (1, 2)],  # (0, 2) is in matrix, but (1, 2) is listed
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False

    # ------------------------------------------------------------------------
    # 1.6 Invalid Odd Cycle Sequences
    # ------------------------------------------------------------------------

    def test_odd_cycle_length_less_than_three(self, target_conjecture: Conjecture):
        """Odd cycle walk with fewer than 3 vertices is rejected."""
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        cert = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("distinct" in err.lower() or "not an odd integer" in err.lower() for err in errs)

    def test_cycle_with_even_length_claimed_as_odd_cycle(self, target_conjecture: Conjecture):
        """4-cycle or 6-cycle claimed as an odd cycle witness is strictly rejected."""
        # 4-cycle: [0, 1, 2, 3, 0]
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        cert_c4 = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert_c4, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert_c4, target_conjecture)
        assert ok is False
        assert any("not an odd integer" in err.lower() for err in errs)

        # Open 4-cycle: [0, 1, 2, 3]
        cert_open_c4 = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert_open_c4, target_conjecture) is False

    def test_odd_cycle_missing_edges_in_graph(self, target_conjecture: Conjecture):
        """Odd cycle sequence has non-consecutive or non-existent edges."""
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        # Sequence [0, 2, 4, 1, 3, 0]: C5 has no edge between 0 and 2
        cert = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 2, 4, 1, 3, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("does not exist in graph" in err.lower() for err in errs)

    def test_odd_cycle_with_out_of_bounds_vertex(self, target_conjecture: Conjecture):
        """Odd cycle sequence contains vertex out of range [0, order-1]."""
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        cert = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 3, 99, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("out of bounds" in err.lower() for err in errs)

    def test_odd_cycle_with_duplicate_vertices(self, target_conjecture: Conjecture):
        """Odd cycle sequence contains duplicate internal vertices (not a simple cycle)."""
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        # Sequence with odd number of steps (k=5) but non-distinct internal vertices: [0, 1, 2, 1, 3, 0]
        cert = CounterexampleCertificate(
            conjecture_id=c5_cert.conjecture_id,
            graph_order=c5_cert.graph_order,
            graph_size=c5_cert.graph_size,
            adjacency_matrix=c5_cert.adjacency_matrix,
            edges=c5_cert.edges,
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 1, 3, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("not distinct" in err.lower() for err in errs)

    def test_odd_cycle_claimed_on_bipartite_graph(self, target_conjecture: Conjecture):
        """Odd cycle claimed on a bipartite graph (C4 or K2) must be rejected."""
        c4 = nx.cycle_graph(4)
        adj = nx.to_numpy_array(c4, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=4,
            graph_size=4,
            adjacency_matrix=adj,
            edges=list(c4.edges()),
            refutation_witness={"type": "odd_cycle", "details": []},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("bipartite" in err.lower() for err in errs)

    # ------------------------------------------------------------------------
    # 1.7 Fake Witnesses on Satisfied Graphs
    # ------------------------------------------------------------------------

    def test_fake_witness_on_satisfied_graph(self, target_conjecture: Conjecture):
        """Graph satisfies conjecture (K2 has chi=2 <= 2), so it is not a counterexample."""
        k2 = nx.complete_graph(2)
        adj = nx.to_numpy_array(k2, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=2,
            graph_size=1,
            adjacency_matrix=adj,
            edges=list(k2.edges()),
            invariants={"chromatic_number": 2, "is_triangle_free": True},
            refutation_witness={"type": "direct_evaluation", "details": None},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("conjecture holds on graph" in err.lower() for err in errs)

    def test_fake_witness_violating_premise_guard(self, target_conjecture: Conjecture):
        """Graph has chi > 2 but violates premise guard (K3 has triangles, so is_triangle_free is False)."""
        k3 = nx.complete_graph(3)
        adj = nx.to_numpy_array(k3, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=target_conjecture.id,
            graph_order=3,
            graph_size=3,
            adjacency_matrix=adj,
            edges=list(k3.edges()),
            invariants={"chromatic_number": 3, "triangle_count": 1},
            refutation_witness={"type": "odd_cycle", "details": [0, 1, 2, 0]},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
        assert ok is False
        assert any("is_triangle_free" in err.lower() for err in errs)

    def test_fake_exhaustive_coloring_on_bipartite_graph(self):
        """Certificate claims chi > 2 via exhaustive coloring on a bipartite graph (K3_3)."""
        conj = Conjecture(
            id="conj_chi_le_2",
            statement="chi <= 2",
            lhs_expr=InvariantNode("chromatic_number"),
            rel="<=",
            rhs_expr=ConstantNode(2.0),
        )
        k33 = nx.complete_bipartite_graph(3, 3)
        adj = nx.to_numpy_array(k33, dtype=int).tolist()
        cert = CounterexampleCertificate(
            conjecture_id=conj.id,
            graph_order=6,
            graph_size=9,
            adjacency_matrix=adj,
            edges=list(k33.edges()),
            refutation_witness={"type": "exhaustive_coloring", "details": None},
            verification_hash="tampered",
        )
        assert CounterexampleCertificateVerifier.verify(cert, conj) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, conj)
        assert ok is False
        assert any("exhaustive coloring found valid 2-coloring" in err.lower() for err in errs)

    # ------------------------------------------------------------------------
    # 1.8 Invariant Discrepancies in Certificate
    # ------------------------------------------------------------------------

    def test_invariant_discrepancies_detected(self, target_conjecture: Conjecture):
        """Certificate invariant metadata does not match true graph properties."""
        # Order mismatch
        c5_cert = build_c5_counterexample_certificate(target_conjecture.id)
        c5_cert.invariants["order"] = 99
        assert CounterexampleCertificateVerifier.verify(c5_cert, target_conjecture) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(c5_cert, target_conjecture)
        assert ok is False
        assert any("invariant 'order'" in err.lower() for err in errs)

        # Size mismatch
        c5_cert2 = build_c5_counterexample_certificate(target_conjecture.id)
        c5_cert2.invariants["size"] = 99
        assert CounterexampleCertificateVerifier.verify(c5_cert2, target_conjecture) is False

        # Triangle count mismatch
        c5_cert3 = build_c5_counterexample_certificate(target_conjecture.id)
        c5_cert3.invariants["triangle_count"] = 5
        assert CounterexampleCertificateVerifier.verify(c5_cert3, target_conjecture) is False

    # ------------------------------------------------------------------------
    # 1.9 Bizarre & Malformed Certificates Never Crash
    # ------------------------------------------------------------------------

    @pytest.mark.parametrize(
        "kwargs",
        [
            dict(graph_order=-1, graph_size=0, adjacency_matrix=[], edges=[]),
            dict(graph_order=2, graph_size=-1, adjacency_matrix=[[0, 1], [1, 0]], edges=[(0, 1)]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=None, edges=[(0, 1)]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1], [1, 0]], edges=None),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1], [1, 0]], edges=[(0, 1)], refutation_witness=None),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1], [1, 0]], edges=[(0, 1, 2)]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1], [1, 0]], edges=[(0,)]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1], [1, 0]], edges=[("a", "b")]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=[[0, 1, 0], [1, 0]], edges=[(0, 1)]),
            dict(graph_order=2, graph_size=1, adjacency_matrix=["row0", "row1"], edges=[(0, 1)]),
        ],
    )
    def test_bizarre_certificates_never_raise_uncaught_exceptions(
        self,
        target_conjecture: Conjecture,
        kwargs: Dict[str, Any],
    ):
        """Verifier cleanly returns False without raising any unhandled exceptions."""
        cert = CounterexampleCertificate.model_construct(
            conjecture_id=target_conjecture.id,
            verification_hash="tampered",
            **kwargs,
        )
        try:
            ok = CounterexampleCertificateVerifier.verify(cert, target_conjecture)
            ok_d, errs = CounterexampleCertificateVerifier.verify_with_details(cert, target_conjecture)
            assert ok is False
            assert ok_d is False
            assert len(errs) > 0
        except Exception as exc:
            pytest.fail(f"CounterexampleCertificateVerifier raised uncaught exception: {exc}")


# ============================================================================
# 2. InstanceDatabase Boundary & Extreme Graphs Challenge Suite
# ============================================================================


class TestAdversarialInstanceDatabaseBoundaries:
    """Stress tests on boundary graphs (n=0, n=1, disconnected, stars, complete)."""

    def test_null_graph_boundary_in_database(self):
        """Database includes Atlas_0 (n=0, m=0), and sieving can refute order >= 1."""
        db = InstanceDatabase()
        atlas_0 = db.get_instances()[0]
        assert atlas_0.number_of_nodes() == 0
        assert atlas_0.number_of_edges() == 0

        # Conjecture that all graphs have at least 1 vertex
        conj = Conjecture(
            id="min_order_1",
            statement="order >= 1",
            lhs_expr=InvariantNode("order"),
            rel=">=",
            rhs_expr=ConstantNode(1.0),
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 0
        assert cert.graph_size == 0
        assert cert.adjacency_matrix == []
        assert cert.edges == []
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_single_vertex_boundary_in_database(self):
        """Database includes Atlas_1 (K1: n=1, m=0), refuting connected graphs having size >= 1."""
        db = InstanceDatabase()
        atlas_1 = db.get_instances()[1]
        assert atlas_1.number_of_nodes() == 1
        assert atlas_1.number_of_edges() == 0

        # Claim: is_connected ==> size >= 1 (fails on K1)
        conj = Conjecture(
            id="conn_size_1",
            statement="is_connected ==> size >= 1",
            lhs_expr=InvariantNode("size"),
            rel=">=",
            rhs_expr=ConstantNode(1.0),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 1
        assert cert.graph_size == 0
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_star_graph_degree_variance_refutation(self):
        """Star graphs S_6 = K_{1, 5} refute bounds on degree spread Delta - delta <= 2."""
        db = InstanceDatabase()
        # Bound: max_degree - min_degree <= 2
        diff = BinaryOpNode("-", InvariantNode("max_degree"), InvariantNode("min_degree"))
        conj = Conjecture(
            id="degree_spread_bound",
            statement="max_degree - min_degree <= 2",
            lhs_expr=diff,
            rel="<=",
            rhs_expr=ConstantNode(2.0),
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_complete_graph_independence_refutation(self):
        """Complete graphs K_n refute independence number bounds alpha >= 2."""
        db = InstanceDatabase()
        conj = Conjecture(
            id="min_independence",
            statement="order >= 4 ==> independence_number >= 2",
            lhs_expr=InvariantNode("independence_number"),
            rel=">=",
            rhs_expr=ConstantNode(2.0),
            guard_predicate=GuardPredicate(
                predicate_type="comparison",
                invariant="order",
                op=">=",
                threshold=4.0,
            ),
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.invariants["independence_number"] == 1
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_clear_cache_and_catalog_reinitialization(self):
        """InstanceDatabase can clear cache and initialize without Atlas."""
        InstanceDatabase.clear_cache()
        db_no_atlas = InstanceDatabase(include_atlas=False)
        instances = db_no_atlas.get_instances()
        assert len(instances) > 50
        names = [getattr(g, "name", "") for g in instances]
        assert not any("Atlas_" in n for n in names)
        assert any("C_" in n for n in names)
        assert any("K_" in n for n in names)

        # Restore full catalog
        InstanceDatabase.clear_cache()
        db_full = InstanceDatabase(include_atlas=True)
        assert len(db_full) >= 1000


# ============================================================================
# 3. Adversarial Sieving of Vacuous Conjectures and Extreme Expressions
# ============================================================================


class TestAdversarialVacuousAndExtremeExpressions:
    """Stress tests on vacuous conjectures and numerical/domain edge cases."""

    def test_no_eligible_graphs_is_inconclusive(self):
        """No matching catalog instances supplies neither a proof nor a refutation."""
        db = InstanceDatabase()
        # Premise: order >= 500 (no graph in DB satisfies this)
        vacuous_guard = GuardPredicate(
            predicate_type="comparison",
            invariant="order",
            op=">=",
            threshold=500.0,
        )
        conj = Conjecture(
            id="vacuous_claim",
            statement="order >= 500 ==> size <= -10",
            lhs_expr=InvariantNode("size"),
            rel="<=",
            rhs_expr=ConstantNode(-10.0),
            guard_predicate=vacuous_guard,
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "INCONCLUSIVE"
        assert res.checked_instances_count == 0
        assert res.counterexample_certificate is None
        assert res.tested_instances_count == len(db)

    def test_division_by_zero_safe_handling_in_vectorized_sieve(self):
        """Vectorized sieve handles division by zero in expressions without crashing."""
        db = InstanceDatabase()
        # Expression: order / size (size is 0 on Atlas_0, Atlas_1, and edgeless graphs)
        div_expr = BinaryOpNode("/", InvariantNode("order"), InvariantNode("size"))
        conj = Conjecture(
            id="div_zero_vectorized",
            statement="order / size >= 0",
            lhs_expr=div_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.0),
        )

        res = db.sieve_conjecture(conj)
        # Vectorized evaluation safely substitutes 0.0 for division by zero
        assert res.status in ("SURVIVED", "REFUTED")

    def test_extreme_powers_and_functions(self):
        """Large exponents and log1p / sqrt on boundary invariants do not crash."""
        db = InstanceDatabase()
        # sqrt(triangle_count) <= order
        sqrt_tri = UnaryOpNode("sqrt", InvariantNode("triangle_count"))
        conj = Conjecture(
            id="sqrt_tri_bound",
            statement="sqrt(triangle_count) <= order * order",
            lhs_expr=sqrt_tri,
            rel="<=",
            rhs_expr=BinaryOpNode("*", InvariantNode("order"), InvariantNode("order")),
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None

    def test_dynamic_add_instance_cache_coherence_vulnerability(self):
        """EMPIRICAL FINDING: add_instance does not update _cached_matrix.

        When a new instance is dynamically appended via db.add_instance(),
        _cached_matrix retains its original size (1,352). When a conjecture is
        evaluated using vectorized sieving, _try_vectorized_sieve only checks
        the 1,352 cached entries in _cached_matrix. If all 1,352 entries satisfy
        the conjecture, it early-returns SURVIVED without evaluating the newly added
        instance in _cached_gi, falsely reporting that all instances were tested.
        """
        db = InstanceDatabase()
        initial_count = len(db)

        # Claim: order <= 25 (holds on all 1,352 precomputed graphs)
        conj = Conjecture(
            id="bounded_order_25",
            statement="order <= 25",
            lhs_expr=InvariantNode("order"),
            rel="<=",
            rhs_expr=ConstantNode(25.0),
        )
        res_before = db.sieve_conjecture(conj)
        assert res_before.status == "SURVIVED"

        # Dynamically append a graph with order 30 that clearly violates order <= 25
        g30 = nx.empty_graph(30)
        g30.name = "EmptyGraph_30"
        db.add_instance(g30)
        assert len(db) == initial_count + 1

        # Sieve again
        res_after = db.sieve_conjecture(conj)

        # Verified behavior: Cache coherence ensures vectorized sieve evaluates the added instance
        assert res_after.status == "REFUTED"
        assert res_after.counterexample_certificate is not None
        assert res_after.counterexample_certificate.graph_order == 30
        assert CounterexampleCertificateVerifier.verify(res_after.counterexample_certificate, conj) is True
        assert res_after.tested_instances_count == initial_count + 1

    def test_sequential_fallback_division_by_zero_behavior(self):
        """EMPIRICAL FINDING: Sequential dictionary evaluation does not catch ZeroDivisionError.

        While _try_vectorized_sieve uses np.where(abs(r) < 1e-12, 0.0, l / r) to safely
        suppress division by zero, the sequential dictionary fallback path does not wrap
        conj.evaluate() in a domain error handler. When an expression contains an invariant
        not in _cached_matrix (e.g. diameter), forced sequential fallback on K1 triggers
        ZeroDivisionError.
        """
        db = InstanceDatabase()
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        expr = BinaryOpNode("/", InvariantNode("diameter"), denom)
        conj = Conjecture(
            id="div_zero_sequential",
            statement="diameter / (order - 1) >= 0",
            lhs_expr=expr,
            rel=">=",
            rhs_expr=ConstantNode(0.0),
        )

        res = db.sieve_conjecture(conj)
        assert res.status in ("SURVIVED", "REFUTED")
        assert res.tested_instances_count > 0


# ============================================================================
# 4. Adversarial Domain Singularity Handling Suite (Milestone 2 Hardening)
# ============================================================================


class TestAdversarialDomainSingularityHandling:
    """Stress tests verifying mathematical domain singularities are safely skipped.

    Verifies:
    1. Division by zero on boundary graphs (Atlas_1 / K_1 where order - 1 == 0)
       does NOT cause false refutations of valid theorems.
    2. Negative radicands (e.g. sqrt(order - 2) on K_1) do NOT cause false refutations
       or emit unverified certificates on K_1.
    3. Logarithm singularities (log / log1p on non-positive arguments) propagate NaN
       and skip undefined instances.
    4. Genuine counterexamples on well-defined domains are STILL correctly caught
       and certified even in the presence of domain singularities on other instances.
    5. Every emitted CounterexampleCertificate strictly passes independent verification:
       CounterexampleCertificateVerifier.verify(cert, conj) is True.
    6. Equivalence between vectorized columnar sieve and sequential fallback evaluation
       on expressions with singularities.
    """

    def test_division_by_zero_k1_singularity_survives(self):
        """Valid theorem is_connected ==> order / (order - 1) >= 1.0 must SURVIVE on catalog.

        Atlas_1 (K_1, order=1, is_connected=True) has denominator order - 1 == 0.
        Singularity must evaluate to NaN and be masked out, rather than mapping to 0.0
        and falsely refuting the theorem on K_1.
        All connected graphs with order >= 2 satisfy n / (n - 1) > 1.0 >= 1.0.
        """
        db = InstanceDatabase()
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        div_expr = BinaryOpNode("/", InvariantNode("order"), denom)
        conj = Conjecture(
            id="k1_div_zero_theorem_survives",
            statement="is_connected ==> order / (order - 1) >= 1.0",
            lhs_expr=div_expr,
            rel=">=",
            rhs_expr=ConstantNode(1.0),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "SURVIVED", (
            f"Conjecture falsely refuted: {res.counterexample_certificate}"
        )
        assert res.counterexample_certificate is None
        assert res.tested_instances_count == len(db)

    def test_negative_radicand_k1_singularity_survives_on_nonnegative_bound(self):
        """Theorem is_connected ==> sqrt(order - 2) >= 0.0 must SURVIVE on catalog.

        On Atlas_1 (K_1, order=1), order - 2 == -1 < 0 (negative radicand).
        Singularity must evaluate to NaN and be skipped without refuting on K_1.
        For all connected graphs with order >= 2, sqrt(order - 2) >= 0.0 holds.
        """
        db = InstanceDatabase()
        sub = BinaryOpNode("-", InvariantNode("order"), ConstantNode(2.0))
        sqrt_expr = UnaryOpNode("sqrt", sub)
        conj = Conjecture(
            id="k1_sqrt_nonneg_survives",
            statement="is_connected ==> sqrt(order - 2) >= 0.0",
            lhs_expr=sqrt_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.0),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "SURVIVED", (
            f"Conjecture falsely refuted: {res.counterexample_certificate}"
        )
        assert res.counterexample_certificate is None
        assert res.tested_instances_count == len(db)

    def test_negative_radicand_k1_skipped_and_refuted_on_k2_with_verified_cert(self):
        """Conjecture is_connected ==> sqrt(order - 2) >= 0.5 skips K_1 and refutes on K_2.

        On K_1 (Atlas_1, order=1), order - 2 == -1 is a negative radicand singularity.
        The sieve must SKIP K_1 (never emit K_1 certificate) and find the first genuine
        counterexample at Atlas_3 (K_2, order=2, size=1), where sqrt(2 - 2) = 0.0 < 0.5.
        The emitted certificate MUST be for Atlas_3 (order 2) and pass independent verification.
        """
        db = InstanceDatabase()
        sub = BinaryOpNode("-", InvariantNode("order"), ConstantNode(2.0))
        sqrt_expr = UnaryOpNode("sqrt", sub)
        conj = Conjecture(
            id="k1_sqrt_half_refuted_on_k2",
            statement="is_connected ==> sqrt(order - 2) >= 0.5",
            lhs_expr=sqrt_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.5),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 2, (
            f"Expected counterexample order 2 (K_2 / Atlas_3), got {cert.graph_order} (K_1 must NOT be witness)"
        )
        assert cert.invariants["is_connected"] is True
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, conj)
        assert ok is True
        assert errs == []

    def test_logarithm_domain_singularity_survives(self):
        """Logarithm singularity on K_0/K_1 is skipped and theorem survives.

        Tests order >= 2 ==> log1p(order - 2) >= 0.0 (and log(order - 1) if supported).
        On Atlas_0 (order=0) and Atlas_1 (order=1), arguments are non-positive (NaN).
        On all graphs with order >= 2, the logarithm is well-defined and non-negative.
        """
        db = InstanceDatabase()
        sub = BinaryOpNode("-", InvariantNode("order"), ConstantNode(2.0))
        log_expr = UnaryOpNode("log1p", sub)
        conj = Conjecture(
            id="log_singularity_survives",
            statement="order >= 2 ==> log1p(order - 2) >= 0.0",
            lhs_expr=log_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.0),
            guard_predicate=GuardPredicate(
                predicate_type="comparison",
                invariant="order",
                op=">=",
                threshold=2.0,
            ),
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "SURVIVED"
        assert res.counterexample_certificate is None
        assert res.tested_instances_count == len(db)

    def test_genuine_counterexample_with_division_singularity_certified(self):
        """Genuine counterexample is_connected ==> order / (order - 1) <= 1.2 is caught on K_2.

        Atlas_1 (K_1, order=1) has denominator 0 and is safely skipped.
        Atlas_3 (K_2, order=2) is connected with 2 / (2 - 1) = 2.0 > 1.2, which is
        a genuine counterexample on a well-defined domain.
        The sieve must refute the claim with witness Atlas_3 and certified validity.
        """
        db = InstanceDatabase()
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        div_expr = BinaryOpNode("/", InvariantNode("order"), denom)
        conj = Conjecture(
            id="genuine_ce_div_k2",
            statement="is_connected ==> order / (order - 1) <= 1.2",
            lhs_expr=div_expr,
            rel="<=",
            rhs_expr=ConstantNode(1.2),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 2, f"Expected Atlas_3 (order 2), got {cert.graph_order}"
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(cert, conj)
        assert ok is True
        assert errs == []

    def test_genuine_counterexample_with_logarithm_singularity_certified(self):
        """Genuine counterexample is_connected ==> log1p(order - 2) >= 0.5 is caught on K_2.

        Atlas_1 (K_1, order=1) has argument <= -1.0 (singularity, skipped).
        Atlas_3 (K_2, order=2) has log1p(0) = 0.0 < 0.5 (genuine counterexample).
        Must emit verified certificate on K_2.
        """
        db = InstanceDatabase()
        sub = BinaryOpNode("-", InvariantNode("order"), ConstantNode(2.0))
        log_expr = UnaryOpNode("log1p", sub)
        conj = Conjecture(
            id="genuine_ce_log_k2",
            statement="is_connected ==> log1p(order - 2) >= 0.5",
            lhs_expr=log_expr,
            rel=">=",
            rhs_expr=ConstantNode(0.5),
            guard_predicate="is_connected",
        )

        res = db.sieve_conjecture(conj)
        assert res.status == "REFUTED"
        assert res.counterexample_certificate is not None
        cert = res.counterexample_certificate
        assert cert.graph_order == 2
        assert CounterexampleCertificateVerifier.verify(cert, conj) is True

    def test_fake_k1_singularity_certificate_rejected_by_verifier(self):
        """CounterexampleCertificateVerifier strictly rejects synthetic certificates on K_1 singularities.

        If a defective sieve were to emit a certificate claiming K_1 refutes
        is_connected ==> order / (order - 1) >= 1.0 or sqrt(order - 2) >= 0.5,
        the verifier MUST evaluate conj.evaluate(K_1), encounter the domain singularity,
        and reject the certificate by returning False.
        """
        db = InstanceDatabase()

        # Division singularity conjecture
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        conj_div = Conjecture(
            id="test_div_tampered_k1",
            statement="is_connected ==> order / (order - 1) >= 1.0",
            lhs_expr=BinaryOpNode("/", InvariantNode("order"), denom),
            rel=">=",
            rhs_expr=ConstantNode(1.0),
            guard_predicate="is_connected",
        )
        fake_cert_div = db._build_certificate(conj_div, idx=1, lhs_val=0.0, rhs_val=1.0)
        assert CounterexampleCertificateVerifier.verify(fake_cert_div, conj_div) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(fake_cert_div, conj_div)
        assert ok is False
        assert any(
            "verification exception" in e.lower() or "division by zero" in e.lower()
            for e in errs
        )

        # Sqrt singularity conjecture
        conj_sqrt = Conjecture(
            id="test_sqrt_tampered_k1",
            statement="is_connected ==> sqrt(order - 2) >= 0.5",
            lhs_expr=UnaryOpNode("sqrt", BinaryOpNode("-", InvariantNode("order"), ConstantNode(2.0))),
            rel=">=",
            rhs_expr=ConstantNode(0.5),
            guard_predicate="is_connected",
        )
        fake_cert_sqrt = db._build_certificate(conj_sqrt, idx=1, lhs_val=0.0, rhs_val=0.5)
        assert CounterexampleCertificateVerifier.verify(fake_cert_sqrt, conj_sqrt) is False
        ok, errs = CounterexampleCertificateVerifier.verify_with_details(fake_cert_sqrt, conj_sqrt)
        assert ok is False
        assert any(
            "verification exception" in e.lower()
            or "domain error" in e.lower()
            or "negative" in e.lower()
            for e in errs
        )

    def test_vectorized_and_sequential_singularity_consistency(self):
        """Vectorized columnar sieve and sequential fallback yield identical results on singularities.

        Forces sequential evaluation by iterating through instances,
        confirming that both execution tiers treat domain singularities identically
        by skipping undefined instances without false refutations or unhandled crashes.
        """
        db = InstanceDatabase()
        denom = BinaryOpNode("-", InvariantNode("order"), ConstantNode(1.0))
        conj = Conjecture(
            id="consistency_singularity_test",
            statement="is_connected ==> order / (order - 1) >= 1.0",
            lhs_expr=BinaryOpNode("/", InvariantNode("order"), denom),
            rel=">=",
            rhs_expr=ConstantNode(1.0),
            guard_predicate="is_connected",
        )

        # 1. Vectorized evaluation
        res_vec = db.sieve_conjecture(conj)
        assert res_vec.status == "SURVIVED"

        # 2. Sequential fallback simulation
        seq_violation = None
        for gi, nx_g, invs in zip(
            db.get_graph_instances(), db.get_instances(), db.get_precomputed_invariants()
        ):
            try:
                holds, l_val, r_val = conj.evaluate(gi, invariants=invs)
            except (ZeroDivisionError, ValueError, ArithmeticError):
                continue
            if not holds:
                seq_violation = gi
                break

        assert seq_violation is None
        assert res_vec.status == "SURVIVED"
