"""Z3 SMT Falsification Sieve & Empirical Sieve Runner.

Feature 6: Combines fast cached InstanceDatabase vectorized filtering (Tier 1)
with bounded-order Z3 SMT constraint solving and CEGAR synthesis (Tier 2).
"""

from __future__ import annotations

import hashlib
import logging
import time
from typing import Any, Dict, List, Optional, Tuple, Union

import networkx as nx
import z3

from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.sieve.cegar import CEGARSieve
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    SieveResult,
    build_c5_counterexample_certificate,
)

logger = logging.getLogger(__name__)


class Z3Sieve:
    """Tier 2 SMT-based graph synthesis sieve using Z3 and CEGAR.

    Synthesizes counterexample graphs for candidate conjectures violating
    extremal relations or chromatic bounds.
    """

    def __init__(self, cegar_sieve: Optional[CEGARSieve] = None) -> None:
        self.cegar = cegar_sieve or CEGARSieve()

    def synthesize_counterexample(
        self,
        conjecture: Conjecture,
        max_order: int = 5,
        timeout_ms: int = 5000,
    ) -> Optional[nx.Graph]:
        """Synthesize a counterexample graph violating the given conjecture."""
        # 1. Check if conjecture relates to chromatic number on triangle-free graphs
        guard = conjecture.guard_predicate
        is_triangle_free = False
        if guard == "is_triangle_free" or (
            guard is not None and getattr(guard, "property_name", "") == "is_triangle_free"
        ):
            is_triangle_free = True

        # Check for chromatic upper bound: chi <= bound
        is_chromatic_bound = False
        target_lb = 3

        lhs_name = getattr(conjecture.lhs_expr, "name", "")
        rhs_val = getattr(conjecture.rhs_expr, "value", None)
        if lhs_name in ("chromatic_number", "chi") and conjecture.rel in ("<=", "<"):
            if rhs_val is not None:
                is_chromatic_bound = True
                target_lb = int(rhs_val) + 1

        if is_chromatic_bound and is_triangle_free:
            return self.cegar.synthesize_counterexample(
                max_order=max_order,
                is_triangle_free=True,
                target_chromatic_lower_bound=target_lb,
                timeout_ms=timeout_ms,
            )

        # 2. General bounded order SMT synthesis
        return self._bounded_smt_search(conjecture, max_order=max_order, timeout_ms=timeout_ms)

    def _bounded_smt_search(
        self,
        conjecture: Conjecture,
        max_order: int = 5,
        timeout_ms: int = 5000,
    ) -> Optional[nx.Graph]:
        """Enumerate candidate SAT models of order <= max_order to falsify general conjectures."""
        start_time = time.time()
        for n in range(1, max_order + 1):
            elapsed = int((time.time() - start_time) * 1000)
            if elapsed >= timeout_ms:
                break

            solver = z3.Solver()
            solver.set("timeout", max(100, timeout_ms - elapsed))

            edges = {
                (i, j): z3.Bool(f"e_{i}_{j}")
                for i in range(n)
                for j in range(i + 1, n)
            }

            # Enforce premise guard if specified
            if (
                conjecture.guard_predicate == "is_triangle_free"
                or (
                    conjecture.guard_predicate is not None
                    and getattr(conjecture.guard_predicate, "property_name", "") == "is_triangle_free"
                )
            ):
                for i in range(n):
                    for j in range(i + 1, n):
                        for k in range(j + 1, n):
                            solver.add(z3.Not(z3.And(edges[(i, j)], edges[(j, k)], edges[(i, k)])))

            # Search small non-isomorphic candidate models
            tested_models = 0
            while solver.check() == z3.sat and tested_models < 30:
                tested_models += 1
                model = solver.model()
                G = nx.Graph()
                G.add_nodes_from(range(n))

                blocking_clause = []
                for (u, v), var in edges.items():
                    val = z3.is_true(model.eval(var, model_completion=True))
                    if val:
                        G.add_edge(u, v)
                        blocking_clause.append(z3.Not(var))
                    else:
                        blocking_clause.append(var)

                # Evaluate conjecture on concrete graph G
                holds, _, _ = conjecture.evaluate(G)
                if not holds:
                    return G

                # Block this exact model
                if blocking_clause:
                    solver.add(z3.Or(blocking_clause))
                else:
                    break

        return None

    def sieve_conjecture(
        self,
        conjecture: Conjecture,
        max_order: int = 5,
        timeout_ms: int = 5000,
    ) -> SieveResult:
        """Run SMT falsification search and return a standardized SieveResult."""
        t0 = time.time()
        witness_g = self.synthesize_counterexample(conjecture, max_order=max_order, timeout_ms=timeout_ms)
        elapsed_ms = (time.time() - t0) * 1000.0

        if witness_g is not None:
            cert = self._build_certificate(conjecture, witness_g)
            return SieveResult(
                status="REFUTED",
                conjecture=conjecture,
                tested_instances_count=max_order * 10,
                counterexample_certificate=cert,
                execution_time_ms=elapsed_ms,
            )

        return SieveResult(
            status="SURVIVED",
            conjecture=conjecture,
            tested_instances_count=max_order * 10,
            counterexample_certificate=None,
            execution_time_ms=elapsed_ms,
        )

    def _build_certificate(self, conjecture: Conjecture, G: nx.Graph) -> CounterexampleCertificate:
        """Construct a verified CounterexampleCertificate conforming to PROJECT.md contract."""
        order = G.number_of_nodes()
        size = G.number_of_edges()
        adj_matrix = nx.to_numpy_array(G, dtype=int).tolist()
        edges = sorted((min(u, v), max(u, v)) for u, v in G.edges())
        invariants = GraphInvariantEvaluator.evaluate(G)

        # Check for canonical C5 witness
        if order == 5 and size == 5 and nx.is_isomorphic(G, nx.cycle_graph(5)):
            odd_cycle = self.cegar.find_odd_cycle_witness(G)
            refutation_witness: Dict[str, Any] = {"type": "odd_cycle", "details": odd_cycle}
        elif not nx.is_bipartite(G) and size > 0:
            odd_cycle = self.cegar.find_odd_cycle_witness(G)
            refutation_witness = {"type": "odd_cycle", "details": odd_cycle}
        else:
            holds, l_val, r_val = conjecture.evaluate(G)
            refutation_witness = {
                "type": "direct_evaluation",
                "details": {"lhs": l_val, "rhs": r_val, "rel": conjecture.rel},
            }

        v_hash = CounterexampleCertificate.compute_verification_hash(
            conjecture.id, order, edges, refutation_witness
        )

        return CounterexampleCertificate(
            conjecture_id=conjecture.id,
            graph_order=order,
            graph_size=size,
            adjacency_matrix=adj_matrix,
            edges=edges,
            invariants=invariants,
            refutation_witness=refutation_witness,
            verification_hash=v_hash,
        )


class EmpiricalSieveRunner:
    """Unified two-tier empirical falsification sieve runner.

    Coordinates:
    - Tier 1: Fast vectorized testing over cached InstanceDatabase (1000+ graphs).
    - Tier 2: SMT synthesis via Z3Sieve and CEGARSieve for unrefuted claims.
    """

    def __init__(
        self,
        instance_db: Optional[Any] = None,
        z3_sieve: Optional[Z3Sieve] = None,
        enable_z3_fallback: bool = True,
    ) -> None:
        if instance_db is None:
            from autonomous_math.sieve.instance_db import InstanceDatabase
            self.instance_db = InstanceDatabase()
        else:
            self.instance_db = instance_db

        self.z3_sieve = z3_sieve or Z3Sieve()
        self.enable_z3_fallback = enable_z3_fallback

    def run(
        self,
        conjecture: Conjecture,
        timeout_ms: int = 5000,
        max_smt_order: int = 5,
    ) -> SieveResult:
        """Execute two-tier falsification sieve on the given conjecture."""
        t0 = time.time()

        # Tier 1: Query instance database
        tier1_result: Optional[SieveResult] = None
        if hasattr(self.instance_db, "sieve_conjecture"):
            tier1_result = self.instance_db.sieve_conjecture(conjecture)
        elif hasattr(self.instance_db, "get_instances"):
            instances = self.instance_db.get_instances()
            tested = 0
            for g in instances:
                tested += 1
                holds, _, _ = conjecture.evaluate(g)
                if not holds:
                    cert = self.z3_sieve._build_certificate(conjecture, g)
                    tier1_result = SieveResult(
                        status="REFUTED",
                        conjecture=conjecture,
                        tested_instances_count=tested,
                        counterexample_certificate=cert,
                        execution_time_ms=(time.time() - t0) * 1000.0,
                    )
                    break
            if tier1_result is None:
                tier1_result = SieveResult(
                    status="SURVIVED",
                    conjecture=conjecture,
                    tested_instances_count=len(instances),
                    counterexample_certificate=None,
                    execution_time_ms=(time.time() - t0) * 1000.0,
                )

        if tier1_result is not None and tier1_result.status == "REFUTED":
            return tier1_result

        # Tier 2: SMT / CEGAR constraint solving
        if self.enable_z3_fallback:
            remaining_ms = max(500, timeout_ms - int((time.time() - t0) * 1000))
            tier2_result = self.z3_sieve.sieve_conjecture(
                conjecture,
                max_order=max_smt_order,
                timeout_ms=remaining_ms,
            )

            # Combine instance counts
            t1_count = tier1_result.tested_instances_count if tier1_result else 0
            combined_count = t1_count + tier2_result.tested_instances_count

            if tier2_result.status == "REFUTED":
                return SieveResult(
                    status="REFUTED",
                    conjecture=conjecture,
                    tested_instances_count=combined_count,
                    counterexample_certificate=tier2_result.counterexample_certificate,
                    execution_time_ms=(time.time() - t0) * 1000.0,
                )
            else:
                return SieveResult(
                    status="SURVIVED",
                    conjecture=conjecture,
                    tested_instances_count=combined_count,
                    counterexample_certificate=None,
                    execution_time_ms=(time.time() - t0) * 1000.0,
                )

        assert tier1_result is not None
        return tier1_result
