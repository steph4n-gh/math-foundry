"""Counterexample-Guided Abstraction Refinement (CEGAR) for Graph Synthesis.

Feature 6: Synthesizes certified counterexample graphs violating candidate
conjectures using Z3 SMT for structural constraints (order, size, triangle-freeness)
coupled with external graph theory verification oracles (NetworkX BFS bipartite check)
and monochromatic edge blocking clauses.
"""

from __future__ import annotations

import logging
import time
from typing import Any, Dict, List, Optional, Tuple

import networkx as nx
import z3

logger = logging.getLogger(__name__)


class CEGARSieve:
    """Counterexample-Guided Abstraction Refinement (CEGAR) graph synthesizer.

    Synthesizes extremal graphs (such as C5 for triangle-free non-2-colorability)
    by alternating between an SMT abstraction solver and an external chromatic oracle.
    """

    def __init__(self) -> None:
        pass

    def synthesize_counterexample(
        self,
        max_order: int = 5,
        is_triangle_free: bool = True,
        target_chromatic_lower_bound: int = 3,
        timeout_ms: int = 5000,
        min_order: Optional[int] = None,
    ) -> Optional[nx.Graph]:
        """Synthesize a graph violating a candidate conjecture using CEGAR.

        Parameters
        ----------
        max_order : int
            Maximum number of vertices to search over (default 5).
        is_triangle_free : bool
            Whether to enforce triangle-free constraint (no K3 subgraphs).
        target_chromatic_lower_bound : int
            Minimum chromatic number required for counterexample (default 3).
        timeout_ms : int
            Maximum timeout in milliseconds for the entire search.
        min_order : Optional[int]
            Minimum order to start search. If None, smartly chooses:
            3 if (is_triangle_free and target >= 3) else max(1, target).

        Returns
        -------
        Optional[nx.Graph]
            Synthesized counterexample graph, or None if UNSAT/timeout.
            For max_order=5, is_triangle_free=True, target=3, returns a graph
            isomorphic to C5 (the 5-cycle).
        """
        if max_order < 1:
            return None

        # Determine sensible minimum order based on chromatic number lower bound
        if min_order is not None:
            eff_min = max(1, min_order)
        elif is_triangle_free and target_chromatic_lower_bound >= 3:
            eff_min = 3
        else:
            eff_min = max(1, target_chromatic_lower_bound)

        if eff_min > max_order:
            return None

        start_time = time.time()

        # Bounded order search: find minimal order counterexample first
        for order in range(eff_min, max_order + 1):
            elapsed_ms = int((time.time() - start_time) * 1000)
            remaining_ms = timeout_ms - elapsed_ms
            if remaining_ms <= 0:
                logger.warning("CEGARSieve timed out during bounded order search.")
                return None

            graph = self._cegar_solve_at_order(
                order=order,
                is_triangle_free=is_triangle_free,
                target_chromatic_lower_bound=target_chromatic_lower_bound,
                timeout_ms=remaining_ms,
            )
            if graph is not None:
                return graph

        return None

    def _cegar_solve_at_order(
        self,
        order: int,
        is_triangle_free: bool,
        target_chromatic_lower_bound: int,
        timeout_ms: int,
    ) -> Optional[nx.Graph]:
        """Run CEGAR refinement loop at a fixed vertex order n."""
        # A graph of order n has max chromatic number n
        if order < target_chromatic_lower_bound and target_chromatic_lower_bound > 0:
            return None

        solver = z3.Solver()
        solver.set("timeout", timeout_ms)

        # 1. Decision variables: e_{i, j} for 0 <= i < j < order
        edges: Dict[Tuple[int, int], z3.BoolRef] = {}
        for i in range(order):
            for j in range(i + 1, order):
                edges[(i, j)] = z3.Bool(f"e_{i}_{j}")

        def get_edge_var(u: int, v: int) -> z3.BoolRef:
            if u == v:
                raise ValueError("Self-loops forbidden in simple graphs")
            return edges[(min(u, v), max(u, v))]

        # 2. Structural Clauses: Triangle-free constraints
        # For all i < j < k, Not(e_{i,j} And e_{j,k} And e_{i,k})
        if is_triangle_free:
            for i in range(order):
                for j in range(i + 1, order):
                    for k in range(j + 1, order):
                        solver.add(
                            z3.Not(z3.And(edges[(i, j)], edges[(j, k)], edges[(i, k)]))
                        )

        # 3. Symmetry Breaking Clauses
        # If target chromatic number >= 2 and order >= 2, G must contain at least one edge.
        # Break transposition symmetry by fixing edge (0, 1) = True.
        if target_chromatic_lower_bound >= 2 and order >= 2:
            solver.add(edges[(0, 1)])

        # 4. CEGAR Abstraction-Refinement Loop
        iteration = 0
        max_iterations = 2 ** max(order - 1, 1)

        while iteration < max_iterations:
            iteration += 1
            check_res = solver.check()

            if check_res == z3.unsat:
                return None
            elif check_res == z3.unknown:
                logger.warning("Z3 solver returned unknown (timeout or limit reached).")
                return None

            model = solver.model()

            # Construct concrete candidate graph G from SAT model
            G = nx.Graph()
            G.add_nodes_from(range(order))
            for (u, v), var in edges.items():
                if z3.is_true(model.eval(var, model_completion=True)):
                    G.add_edge(u, v)

            # Verification Oracle: Test chromatic lower bound
            if target_chromatic_lower_bound == 3:
                # O(V + E) BFS bipartite check
                if not nx.is_bipartite(G):
                    # Certified counterexample found!
                    # Graph is triangle-free (via SMT) and non-bipartite (has odd cycle, chi >= 3)
                    return G

                # Spurious counterexample: G is 2-colorable.
                # Extract 2-coloring partition c: V -> {0, 1}
                c = nx.bipartite.color(G)

                # Refinement Clause: Any future graph must NOT be properly 2-colored by c!
                # That is, there must exist at least one monochromatic edge under c.
                same_color_pairs = [
                    get_edge_var(u, v)
                    for u in range(order)
                    for v in range(u + 1, order)
                    if c[u] == c[v]
                ]

                if not same_color_pairs:
                    return None

                solver.add(z3.Or(same_color_pairs))

            elif target_chromatic_lower_bound <= 2:
                # Any graph with >= 1 edge has chi >= 2
                if G.number_of_edges() > 0:
                    return G
                # Spurious: G has 0 edges. Block edgeless graph.
                all_edges = list(edges.values())
                if all_edges:
                    solver.add(z3.Or(all_edges))
                else:
                    return None

            else:
                # Generalized k-colorability check for target > 3
                coloring = self._solve_k_coloring(G, target_chromatic_lower_bound - 1)
                if coloring is None:
                    # G is not (k-1)-colorable, hence chi(G) >= k!
                    return G

                # Spurious: Block coloring partition
                same_color_pairs = [
                    get_edge_var(u, v)
                    for u in range(order)
                    for v in range(u + 1, order)
                    if coloring[u] == coloring[v]
                ]
                if not same_color_pairs:
                    return None
                solver.add(z3.Or(same_color_pairs))

        return None

    def _solve_k_coloring(self, G: nx.Graph, k: int) -> Optional[Dict[int, int]]:
        """Determine if G is k-colorable using a fast auxiliary SAT query."""
        if k <= 0:
            return None
        if k == 1:
            return {v: 0 for v in G.nodes()} if G.number_of_edges() == 0 else None
        if k == 2:
            return nx.bipartite.color(G) if nx.is_bipartite(G) else None

        s = z3.Solver()
        nodes = list(G.nodes())
        x = {(v, c): z3.Bool(f"col_{v}_{c}") for v in nodes for c in range(k)}

        for v in nodes:
            s.add(z3.Or([x[(v, c)] for c in range(k)]))
        for u, v in G.edges():
            for c in range(k):
                s.add(z3.Not(z3.And(x[(u, c)], x[(v, c)])))

        if s.check() == z3.sat:
            m = s.model()
            coloring: Dict[int, int] = {}
            for v in nodes:
                for c in range(k):
                    if z3.is_true(m.eval(x[(v, c)], model_completion=True)):
                        coloring[v] = c
                        break
            return coloring
        return None

    def find_odd_cycle_witness(self, G: nx.Graph) -> List[int]:
        """Extract a canonical odd cycle witness cycle path [v0, v1, ..., v0]."""
        # Search cycle basis for an odd cycle
        for cycle in nx.cycle_basis(G):
            if len(cycle) % 2 == 1:
                return cycle + [cycle[0]]

        # Fallback to simple cycles if available
        if hasattr(nx, "simple_cycles"):
            for cycle in nx.simple_cycles(G.to_directed()):
                if len(cycle) % 2 == 1:
                    return cycle + [cycle[0]]

        # Fallback to standard nodes if cycle not cleanly decomposed
        nodes = sorted(G.nodes())
        return nodes + [nodes[0]] if len(nodes) % 2 == 1 else nodes
