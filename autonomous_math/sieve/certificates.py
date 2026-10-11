"""Counterexample Certificate Schema and Independent 5-Step Verifier.

Feature 7:
Provides:
- CounterexampleCertificate: Pydantic model representing verifiable graph counterexamples.
- SieveResult: Pipeline result object wrapping survived or refuted conjecture outcomes.
- CounterexampleCertificateVerifier: Independent 5-step verifier detecting valid vs tampered certificates.
- build_c5_counterexample_certificate: Canonical benchmark C5 certificate factory.
"""

from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from typing import Any, Dict, List, Literal, Optional, Sequence, Set, Tuple, Union

import networkx as nx
import numpy as np
from pydantic import BaseModel, ConfigDict, Field

from autonomous_math.core.ast import Conjecture, GuardPredicate
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import compute_triangle_count


# ============================================================================
# 1. CounterexampleCertificate Model
# ============================================================================


class CounterexampleCertificate(BaseModel):
    """Verifiable certificate representing an empirical counterexample graph."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    conjecture_id: str
    graph_order: int
    graph_size: int
    adjacency_matrix: List[List[int]]
    edges: List[Tuple[int, int]]
    invariants: Dict[str, Any] = Field(default_factory=dict)
    refutation_witness: Dict[str, Any] = Field(default_factory=dict)
    verification_hash: str = Field(default="")
    created_at: Optional[str] = Field(
        default_factory=lambda: datetime.now(timezone.utc).isoformat()
    )

    def to_dict(self) -> Dict[str, Any]:
        """Convert certificate to dictionary."""
        return self.model_dump()

    def to_json(self, indent: Optional[int] = None) -> str:
        """Convert certificate to JSON string."""
        return self.model_dump_json(indent=indent)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> CounterexampleCertificate:
        """Reconstruct certificate from dictionary."""
        return cls.model_validate(data)

    @classmethod
    def from_json(cls, json_str: str) -> CounterexampleCertificate:
        """Reconstruct certificate from JSON string."""
        return cls.model_validate_json(json_str)

    def to_networkx(self) -> nx.Graph:
        """Convert certificate to NetworkX simple undirected graph."""
        G = nx.Graph()
        G.add_nodes_from(range(self.graph_order))
        if self.edges:
            G.add_edges_from(self.edges)
        elif self.adjacency_matrix:
            n = len(self.adjacency_matrix)
            for i in range(n):
                for j in range(i + 1, n):
                    if self.adjacency_matrix[i][j]:
                        G.add_edge(i, j)
        G.name = f"counterexample_{self.conjecture_id}"
        return G

    def to_graph_instance(self) -> GraphInstance:
        """Convert certificate to immutable canonical GraphInstance."""
        canon_edges = tuple(sorted((min(u, v), max(u, v)) for u, v in self.edges))
        witness_type = "unknown"
        if isinstance(self.refutation_witness, dict):
            witness_type = self.refutation_witness.get("type", "unknown")
        return GraphInstance(
            order=self.graph_order,
            edges=canon_edges,
            name=f"counterexample_{self.conjecture_id}",
            metadata={
                "conjecture_id": self.conjecture_id,
                "verification_hash": self.verification_hash,
                "witness_type": witness_type,
            },
        )

    def to_latex_matrix(self) -> str:
        """Format adjacency matrix as LaTeX pmatrix environment."""
        if not self.adjacency_matrix:
            return "\\begin{pmatrix}\\end{pmatrix}"
        lines = ["\\begin{pmatrix}"]
        for row in self.adjacency_matrix:
            lines.append("  " + " & ".join(str(int(x)) for x in row) + " \\\\")
        lines.append("\\end{pmatrix}")
        return "\n".join(lines)

    @staticmethod
    def compute_verification_hash(
        conjecture_id: str,
        graph_order: int,
        edges: Sequence[Tuple[int, int]],
        refutation_witness: Dict[str, Any],
    ) -> str:
        """Compute deterministic SHA-256 verification hash over canonical data."""
        canon_edges = sorted((min(u, v), max(u, v)) for u, v in edges)
        witness_repr = json.dumps(refutation_witness, sort_keys=True)
        raw = f"{conjecture_id}|{graph_order}|{canon_edges}|{witness_repr}"
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    def compute_hash(self) -> str:
        """Compute the certificate's canonical SHA-256 hash."""
        return self.compute_verification_hash(
            self.conjecture_id,
            self.graph_order,
            self.edges,
            self.refutation_witness,
        )

    @classmethod
    def from_counterexample_graph(
        cls,
        G: Union[nx.Graph, GraphInstance],
        conj: Conjecture,
        witness: Optional[Dict[str, Any]] = None,
        invariants: Optional[Dict[str, Any]] = None,
    ) -> CounterexampleCertificate:
        """Factory creating a valid CounterexampleCertificate from a counterexample graph."""
        nx_g = G.to_networkx() if isinstance(G, GraphInstance) else GraphInstance.from_networkx(G).to_networkx()
        order = nx_g.number_of_nodes()
        edges = sorted((min(u, v), max(u, v)) for u, v in nx_g.edges())
        size = len(edges)

        adj_matrix = [[0] * order for _ in range(order)]
        for u, v in edges:
            adj_matrix[u][v] = 1
            adj_matrix[v][u] = 1

        inv_data = dict(invariants) if invariants is not None else {}
        if "order" not in inv_data:
            inv_data["order"] = order
        if "size" not in inv_data:
            inv_data["size"] = size

        if witness is None:
            # Automatic witness synthesis
            if not nx.is_bipartite(nx_g) and size > 0:
                try:
                    cycles = nx.cycle_basis(nx_g)
                    odd_c = next((c for c in cycles if len(c) % 2 == 1), None)
                    if odd_c:
                        closed_c = list(odd_c) + [odd_c[0]]
                        witness = {"type": "odd_cycle", "details": closed_c}
                    else:
                        witness = {"type": "odd_cycle", "details": []}
                except Exception:
                    witness = {"type": "odd_cycle", "details": []}
            else:
                witness = {"type": "direct_evaluation", "details": None}

        v_hash = cls.compute_verification_hash(conj.id, order, edges, witness)

        return cls(
            conjecture_id=conj.id,
            graph_order=order,
            graph_size=size,
            adjacency_matrix=adj_matrix,
            edges=edges,
            invariants=inv_data,
            refutation_witness=witness,
            verification_hash=v_hash,
        )


# ============================================================================
# 2. SieveResult Model
# ============================================================================


class SieveResult(BaseModel):
    """Result of passing a candidate conjecture through the empirical falsification sieve."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    status: Literal["SURVIVED", "REFUTED", "INCONCLUSIVE"]
    conjecture: Conjecture
    tested_instances_count: int
    checked_instances_count: int = 0
    undefined_instances_count: int = 0
    counterexample_certificate: Optional[CounterexampleCertificate] = None
    execution_time_ms: float = 0.0

    @property
    def is_refuted(self) -> bool:
        """True if conjecture was falsified by a concrete counterexample."""
        return self.status == "REFUTED"

    @property
    def is_survived(self) -> bool:
        """True if conjecture survived all tested sieve instances."""
        return self.status == "SURVIVED"

    def to_dict(self) -> Dict[str, Any]:
        """Convert SieveResult to dictionary."""
        return self.model_dump()

    def to_json(self, indent: Optional[int] = None) -> str:
        """Convert SieveResult to JSON string."""
        return self.model_dump_json(indent=indent)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> SieveResult:
        """Reconstruct SieveResult from dictionary."""
        return cls.model_validate(data)

    @classmethod
    def from_json(cls, json_str: str) -> SieveResult:
        """Reconstruct SieveResult from JSON string."""
        return cls.model_validate_json(json_str)


# ============================================================================
# 3. CounterexampleCertificateVerifier
# ============================================================================


class CounterexampleCertificateVerifier:
    """Independent 5-step verifier for CounterexampleCertificate objects."""

    @classmethod
    def verify_matrix_structure(
        cls,
        cert: CounterexampleCertificate,
    ) -> Tuple[bool, Optional[str]]:
        """Step 1: Structural matrix verification (square, order matches, binary, zero diagonal, symmetric)."""
        order = cert.graph_order
        A = cert.adjacency_matrix

        if not isinstance(order, (int, np.integer)) or order < 0:
            return False, f"graph_order must be a non-negative integer, got {order}"
        if not isinstance(A, (list, tuple)):
            return False, f"adjacency_matrix must be a sequence, got {type(A)}"

        if order == 0:
            if len(A) != 0:
                return False, f"Order 0 graph must have empty adjacency matrix, got {len(A)} rows"
            return True, None

        if len(A) != order:
            return False, f"Adjacency matrix row count {len(A)} does not match graph_order {order}"

        for i, row in enumerate(A):
            if not isinstance(row, (list, tuple)):
                return False, f"Row {i} is not a sequence"
            if len(row) != order:
                return False, f"Row {i} length {len(row)} does not match graph_order {order}"
            for j, val in enumerate(row):
                if not isinstance(val, (int, np.integer)) or val not in (0, 1):
                    return False, f"Entry A[{i}][{j}] = {val} is not binary (0 or 1)"

        # Zero diagonal check (no self-loops in simple graphs)
        for i in range(order):
            if A[i][i] != 0:
                return False, f"Diagonal entry A[{i}][{i}] = {A[i][i]} != 0 (self-loop)"

        # Symmetry check
        for i in range(order):
            for j in range(i + 1, order):
                if A[i][j] != A[j][i]:
                    return False, f"Adjacency matrix is asymmetric at ({i}, {j}): {A[i][j]} != {A[j][i]}"

        return True, None

    @classmethod
    def verify_edge_consistency(
        cls,
        cert: CounterexampleCertificate,
    ) -> Tuple[bool, Optional[str]]:
        """Step 2: Edge list consistency with adjacency matrix."""
        order = cert.graph_order
        size = cert.graph_size
        edges = cert.edges
        A = cert.adjacency_matrix

        if not isinstance(size, (int, np.integer)) or size < 0:
            return False, f"graph_size must be a non-negative integer, got {size}"
        if not isinstance(edges, (list, tuple)):
            return False, f"edges must be a list or tuple, got {type(edges)}"

        if len(edges) != size:
            return False, f"Edge list length {len(edges)} does not match graph_size {size}"

        # Count 1s in upper triangle
        upper_sum = sum(A[i][j] for i in range(order) for j in range(i + 1, order))
        if upper_sum != size:
            return False, f"Upper triangle edge sum {upper_sum} does not match graph_size {size}"

        canon_edges: Set[Tuple[int, int]] = set()
        for idx, e in enumerate(edges):
            if not isinstance(e, (list, tuple)) or len(e) != 2:
                return False, f"Edge at index {idx} is not a 2-tuple: {e}"
            u, v = int(e[0]), int(e[1])
            if not (0 <= u < order and 0 <= v < order):
                return False, f"Edge ({u}, {v}) out of vertex bounds [0, {order - 1}]"
            if u == v:
                return False, f"Self-loop edge ({u}, {v}) is forbidden in simple graphs"
            if A[u][v] != 1 or A[v][u] != 1:
                return False, f"Edge ({u}, {v}) not present in adjacency matrix"
            pair = (min(u, v), max(u, v))
            if pair in canon_edges:
                return False, f"Duplicate edge ({u}, {v}) in edge list"
            canon_edges.add(pair)

        # Check all matrix 1s are in edge list
        for i in range(order):
            for j in range(i + 1, order):
                if A[i][j] == 1 and (i, j) not in canon_edges:
                    return False, f"Matrix entry A[{i}][{j}] == 1 missing from edge list"

        return True, None

    @classmethod
    def verify_premise_guard(
        cls,
        cert: CounterexampleCertificate,
        conj: Conjecture,
        G: nx.Graph,
    ) -> Tuple[bool, Optional[str]]:
        """Step 3: Premise guard verification (e.g. Trace(A^3)==0 for triangle-free, connectivity)."""
        guard = conj.guard_predicate
        if guard is None or guard == "universal":
            return True, None

        guard_name = guard.property_name if isinstance(guard, GuardPredicate) else str(guard)

        # Premise: is_triangle_free
        if guard_name == "is_triangle_free" or (
            isinstance(guard, GuardPredicate) and guard.property_name == "is_triangle_free"
        ):
            if cert.graph_order >= 3:
                A_mat = np.array(cert.adjacency_matrix, dtype=np.int64)
                A3 = np.linalg.matrix_power(A_mat, 3)
                trace_val = int(np.trace(A3))
            else:
                trace_val = 0
            if trace_val != 0:
                return (
                    False,
                    f"Premise 'is_triangle_free' violated: Trace(A^3) = {trace_val} != 0 "
                    f"({trace_val // 6} triangles present)",
                )
            gi = GraphInstance.from_networkx(G)
            if compute_triangle_count(gi) != 0:
                return False, "Premise 'is_triangle_free' violated: graph has triangles"
            return True, None

        # Premise: is_connected
        if guard_name == "is_connected":
            if cert.graph_order > 1 and not nx.is_connected(G):
                return False, "Premise 'is_connected' violated: graph is disconnected"
            return True, None

        # Premise: is_bipartite
        if guard_name == "is_bipartite":
            if cert.graph_size > 0 and not nx.is_bipartite(G):
                return False, "Premise 'is_bipartite' violated: graph is not bipartite"
            return True, None

        # General guard predicate check
        if not conj.applies(G):
            return False, f"Premise guard '{guard_name}' does not hold on graph"

        return True, None

    @classmethod
    def verify_refutation_witness(
        cls,
        cert: CounterexampleCertificate,
        conj: Conjecture,
        G: nx.Graph,
    ) -> Tuple[bool, Optional[str]]:
        """Step 4: Refutation witness verification (odd cycle, exhaustive coloring, direct evaluation)."""
        witness = cert.refutation_witness
        if not isinstance(witness, dict):
            return False, f"refutation_witness must be a dictionary, got {type(witness)}"

        w_type = witness.get("type")
        details = witness.get("details")
        n = cert.graph_order
        A = cert.adjacency_matrix

        # Witness Type: odd_cycle
        if w_type == "odd_cycle":
            if isinstance(details, (list, tuple)) and len(details) >= 3:
                if len(details) >= 4 and details[0] == details[-1]:
                    cycle = list(details[:-1])
                else:
                    cycle = list(details)
                k = len(cycle)
                if k < 3 or k % 2 == 0:
                    return False, f"Odd cycle witness length {k} is not an odd integer >= 3"
                if len(set(cycle)) != k:
                    return False, f"Odd cycle witness vertices are not distinct: {cycle}"
                for v in cycle:
                    if not (0 <= v < n):
                        return False, f"Cycle vertex {v} out of bounds [0, {n - 1}]"
                # Check consecutive edges in A
                for idx in range(k):
                    u = cycle[idx]
                    v = cycle[(idx + 1) % k]
                    if A[u][v] != 1:
                        return False, f"Odd cycle edge ({u}, {v}) does not exist in graph"
            else:
                # Fallback: confirm non-bipartiteness directly
                if nx.is_bipartite(G):
                    return False, "Odd cycle witness claimed, but graph is bipartite (has no odd cycles)"
            return True, None

        # Witness Type: exhaustive_coloring
        if w_type == "exhaustive_coloring":
            if n <= 20:
                nodes = list(range(n))
                edges = list(G.edges())
                for assignment in range(1 << n):
                    color = {nodes[i]: (assignment >> i) & 1 for i in range(n)}
                    monochromatic = any(color[u] == color[v] for u, v in edges)
                    if not monochromatic:
                        return False, f"Exhaustive coloring found valid 2-coloring: {color}"
            else:
                if nx.is_bipartite(G):
                    return False, "Exhaustive coloring claimed chi > 2, but graph is bipartite"
            return True, None

        # Witness Type: direct_evaluation
        if w_type == "direct_evaluation":
            return True, None

        return True, None

    @classmethod
    def verify_conjecture_refutation(
        cls,
        cert: CounterexampleCertificate,
        conj: Conjecture,
        G: nx.Graph,
    ) -> Tuple[bool, Optional[str]]:
        """Step 5: Direct conjecture evaluation verification (conj.evaluate(G) holds is False)."""
        holds, lhs_val, rhs_val = conj.evaluate(G)
        if holds:
            return (
                False,
                f"Conjecture holds on graph (LHS={lhs_val}, RHS={rhs_val}); "
                f"graph is satisfied and therefore NOT a counterexample",
            )

        # Invariant consistency spot-check
        if cert.invariants:
            if "order" in cert.invariants and cert.invariants["order"] != cert.graph_order:
                return False, f"Invariant 'order' ({cert.invariants['order']}) mismatch with {cert.graph_order}"
            if "size" in cert.invariants and cert.invariants["size"] != cert.graph_size:
                return False, f"Invariant 'size' ({cert.invariants['size']}) mismatch with {cert.graph_size}"
            if "triangle_count" in cert.invariants:
                if cert.graph_order >= 3:
                    A_mat = np.array(cert.adjacency_matrix, dtype=np.int64)
                    A3 = np.linalg.matrix_power(A_mat, 3)
                    calc_triangles = int(np.trace(A3)) // 6
                else:
                    calc_triangles = 0
                if cert.invariants["triangle_count"] != calc_triangles:
                    return (
                        False,
                        f"Invariant 'triangle_count' ({cert.invariants['triangle_count']}) "
                        f"mismatch with calculated {calc_triangles}",
                    )

        return True, None

    @classmethod
    def verify_with_details(
        cls,
        cert: CounterexampleCertificate,
        conj: Conjecture,
    ) -> Tuple[bool, List[str]]:
        """Run independent 5-step verification and return (is_valid, list_of_errors)."""
        errors: List[str] = []

        try:
            # Step 1: Structural matrix verification
            ok, err = cls.verify_matrix_structure(cert)
            if not ok:
                errors.append(f"Step 1 failed: {err}")
                return False, errors

            # Step 2: Edge list consistency
            ok, err = cls.verify_edge_consistency(cert)
            if not ok:
                errors.append(f"Step 2 failed: {err}")
                return False, errors

            # Reconstruct graph
            G = cert.to_networkx()

            # Step 3: Premise guard verification
            ok, err = cls.verify_premise_guard(cert, conj, G)
            if not ok:
                errors.append(f"Step 3 failed: {err}")
                return False, errors

            # Step 4: Refutation witness verification
            ok, err = cls.verify_refutation_witness(cert, conj, G)
            if not ok:
                errors.append(f"Step 4 failed: {err}")
                return False, errors

            # Step 5: Direct conjecture evaluation
            ok, err = cls.verify_conjecture_refutation(cert, conj, G)
            if not ok:
                errors.append(f"Step 5 failed: {err}")
                return False, errors

        except Exception as exc:
            errors.append(f"Verification exception: {exc}")
            return False, errors

        return True, []

    @classmethod
    def verify(
        cls,
        cert: CounterexampleCertificate,
        conj: Conjecture,
    ) -> bool:
        """Independently verify whether certificate genuinely refutes conjecture."""
        valid, _ = cls.verify_with_details(cert, conj)
        return valid


# ============================================================================
# 4. Canonical C5 Benchmark Certificate Factory
# ============================================================================


def build_c5_counterexample_certificate(
    conjecture_id: str = "triangle_free_not_two_colorable",
) -> CounterexampleCertificate:
    """Build the canonical C5 counterexample certificate refuting triangle-free 2-colorability."""
    order = 5
    size = 5
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]
    adj_matrix = [
        [0, 1, 0, 0, 1],
        [1, 0, 1, 0, 0],
        [0, 1, 0, 1, 0],
        [0, 0, 1, 0, 1],
        [1, 0, 0, 1, 0],
    ]
    invariants = {
        "order": 5,
        "size": 5,
        "triangle_count": 0,
        "is_triangle_free": True,
        "chromatic_number": 3,
        "clique_number": 2,
        "independence_number": 2,
        "girth": 5.0,
        "is_bipartite": False,
        "is_connected": True,
        "is_regular": True,
        "max_degree": 2,
        "min_degree": 2,
        "density": 0.5,
    }
    witness = {
        "type": "odd_cycle",
        "details": [0, 1, 2, 3, 4, 0],
    }
    verification_hash = CounterexampleCertificate.compute_verification_hash(
        conjecture_id, order, edges, witness
    )

    return CounterexampleCertificate(
        conjecture_id=conjecture_id,
        graph_order=order,
        graph_size=size,
        adjacency_matrix=adj_matrix,
        edges=edges,
        invariants=invariants,
        refutation_witness=witness,
        verification_hash=verification_hash,
    )
