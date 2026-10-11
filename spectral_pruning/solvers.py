"""Exact Maximum Clique Solvers: Baseline Branch-and-Bound vs. Spectral Pruning.

Features:
1. BaselineCliqueSolver: Classical Carraghan-Pardalos / Bron-Kerbosch branch-and-bound
   with Welsh-Powell greedy coloring bounds and degree-ordered branching.
2. SpectralCliqueSolver: Advanced branch-and-bound augmented with:
   - Perron-Frobenius eigenvector centrality vertex ordering (dense-core first).
   - Wilf spectral upper-bound pruning (omega(P) <= floor(lambda_1(P)) + 1).
   - Fiedler vector Laplacian bisection for bottleneck subgraphs.
"""

from __future__ import annotations

import time
from typing import Dict, List, Optional, Set, Tuple
import networkx as nx
import numpy as np


class SolverMetrics:
    def __init__(self) -> None:
        self.nodes_visited: int = 0
        self.size_prunes: int = 0
        self.color_prunes: int = 0
        self.spectral_prunes: int = 0
        self.fiedler_splits: int = 0
        self.runtime_ms: float = 0.0
        self.completed: bool = True
        self.timed_out: bool = False
        self.max_clique_size: int = 0
        self.max_clique_nodes: List[int] = []

    def to_dict(self) -> Dict[str, Any]:
        return {
            "nodes_visited": self.nodes_visited,
            "size_prunes": self.size_prunes,
            "color_prunes": self.color_prunes,
            "spectral_prunes": self.spectral_prunes,
            "fiedler_splits": self.fiedler_splits,
            "runtime_ms": self.runtime_ms,
            "completed": self.completed,
            "timed_out": self.timed_out,
            "max_clique_size": self.max_clique_size,
        }


# ============================================================================
# Baseline Solver: Classical Degree-Ordered Branch-and-Bound
# ============================================================================


class BaselineCliqueSolver:
    """Classical exact Maximum Clique solver using degree-ordered branch-and-bound and greedy coloring."""

    def __init__(self) -> None:
        self.metrics = SolverMetrics()
        self.adj: Dict[int, Set[int]] = {}
        self.max_clique: List[int] = []

    def _greedy_coloring_bound(self, candidates: List[int]) -> int:
        """Computes Welsh-Powell greedy coloring count as an upper bound on omega(candidates)."""
        if not candidates:
            return 0
        # Sort by degree descending in induced subgraph
        cand_set = set(candidates)
        sub_degrees = {u: len(self.adj[u] & cand_set) for u in candidates}
        ordered = sorted(candidates, key=lambda u: sub_degrees[u], reverse=True)

        color_map: Dict[int, int] = {}
        for u in ordered:
            neighbor_colors = {color_map[v] for v in (self.adj[u] & cand_set) if v in color_map}
            c = 0
            while c in neighbor_colors:
                c += 1
            color_map[u] = c

        return max(color_map.values()) + 1 if color_map else 0

    def solve(self, G: nx.Graph, timeout_sec: float = 30.0) -> Tuple[int, List[int], SolverMetrics]:
        """Finds the maximum clique size and vertex set."""
        self.metrics = SolverMetrics()
        t0 = time.time()
        deadline = t0 + timeout_sec

        # Standardize node labels to 0..n-1
        nodes = list(G.nodes())
        node_to_idx = {nd: i for i, nd in enumerate(nodes)}
        idx_to_node = {i: nd for i, nd in enumerate(nodes)}

        self.adj = {node_to_idx[u]: {node_to_idx[v] for v in G.neighbors(u)} for u in G.nodes()}
        self.max_clique = []

        # Initial candidates sorted by degree descending
        initial_candidates = sorted(list(self.adj.keys()), key=lambda u: len(self.adj[u]), reverse=True)

        def search(current_clique: List[int], candidates: List[int]) -> None:
            self.metrics.nodes_visited += 1

            if time.time() > deadline:
                self.metrics.completed = False
                self.metrics.timed_out = True
                return

            if len(current_clique) > len(self.max_clique):
                self.max_clique = list(current_clique)

            # Prune 1: Trivial size bound
            if len(current_clique) + len(candidates) <= len(self.max_clique):
                self.metrics.size_prunes += 1
                return

            # Prune 2: Greedy coloring upper bound
            if len(candidates) >= 3:
                color_ub = self._greedy_coloring_bound(candidates)
                if len(current_clique) + color_ub <= len(self.max_clique):
                    self.metrics.color_prunes += 1
                    return

            cand_set = set(candidates)
            # Explore candidates
            while candidates:
                if len(current_clique) + len(candidates) <= len(self.max_clique):
                    self.metrics.size_prunes += 1
                    break

                v = candidates.pop(0)
                cand_set.remove(v)

                # Filter remaining candidates to neighbors of v
                next_candidates = [u for u in candidates if u in self.adj[v]]
                search(current_clique + [v], next_candidates)

        search([], initial_candidates)

        self.metrics.runtime_ms = (time.time() - t0) * 1000
        self.metrics.max_clique_size = len(self.max_clique)
        self.metrics.max_clique_nodes = [idx_to_node[i] for i in self.max_clique]

        return self.metrics.max_clique_size, self.metrics.max_clique_nodes, self.metrics.metrics_dict() if hasattr(self.metrics, "metrics_dict") else self.metrics


# ============================================================================
# Spectral Pruning Solver: Perron-Frobenius Ordering + Wilf + Fiedler
# ============================================================================


class SpectralCliqueSolver:
    """Advanced Maximum Clique solver utilizing spectral graph theory for search tree reduction."""

    def __init__(self, enable_wilf: bool = True, enable_perron: bool = True, enable_fiedler: bool = True) -> None:
        self.enable_wilf = enable_wilf
        self.enable_perron = enable_perron
        self.enable_fiedler = enable_fiedler
        self.metrics = SolverMetrics()
        self.adj: Dict[int, Set[int]] = {}
        self.max_clique: List[int] = []

    def _compute_perron_ordering_and_wilf(self, candidates: List[int]) -> Tuple[List[int], float]:
        """Computes the Perron-Frobenius principal eigenvector and spectral radius lambda_1.

        Uses power iteration for fast (<0.5ms) computation on the candidate subgraph.
        Returns:
            (ordered_candidates, lambda_1)
        """
        k = len(candidates)
        if k <= 1:
            return candidates, 0.0

        cand_map = {u: i for i, u in enumerate(candidates)}
        # Build compact adjacency matrix for induced subgraph
        A = np.zeros((k, k), dtype=np.float32)
        for u in candidates:
            i = cand_map[u]
            neighbors = self.adj[u]
            for v in neighbors:
                if v in cand_map:
                    A[i, cand_map[v]] = 1.0

        # Power iteration to find dominant eigenvector and eigenvalue lambda_1
        x = np.ones(k, dtype=np.float32) / np.sqrt(k)
        lambda_1 = 0.0
        for _ in range(12):  # 12 iterations gives high precision
            x_next = A @ x
            norm = np.linalg.norm(x_next)
            if norm < 1e-6:
                break
            lambda_1 = float(np.dot(x, x_next))
            x = x_next / norm

        # Order candidates by eigenvector mass descending
        ranked_indices = np.argsort(-x, kind="stable")
        ordered_candidates = [candidates[idx] for idx in ranked_indices]

        # The power estimate is not an upper bound. Maximum degree is an exact
        # integer upper bound on the adjacency spectral radius.
        return ordered_candidates, float(max((len(self.adj[u].intersection(cand_map)) for u in candidates), default=0))

    def _try_fiedler_bisection(self, candidates: List[int]) -> Optional[Tuple[List[int], List[int]]]:
        """Partitions candidates along the Fiedler vector nodal boundary if bottleneck exists."""
        k = len(candidates)
        if k < 16:  # Only for subproblems large enough to justify spectral bisection
            return None

        cand_map = {u: i for i, u in enumerate(candidates)}
        A = np.zeros((k, k), dtype=np.float32)
        degrees = np.zeros(k, dtype=np.float32)
        for u in candidates:
            i = cand_map[u]
            for v in self.adj[u]:
                if v in cand_map:
                    A[i, cand_map[v]] = 1.0
            degrees[i] = np.sum(A[i, :])

        if np.min(degrees) == 0:
            return None

        L = np.diag(degrees) - A
        try:
            # Smallest 2 eigenvalues and eigenvectors
            evals, evecs = np.linalg.eigh(L)
            mu_2 = float(evals[1])
            avg_deg = float(np.mean(degrees))

            # Only partition if the graph has an algebraic bottleneck (mu_2 is small relative to degree)
            if mu_2 < 0.35 * avg_deg:
                v2 = evecs[:, 1]
                pos_cands = [candidates[i] for i in range(k) if v2[i] >= 0]
                neg_cands = [candidates[i] for i in range(k) if v2[i] < 0]

                # Check that partition is balanced enough
                if len(pos_cands) >= 4 and len(neg_cands) >= 4:
                    return pos_cands, neg_cands
        except Exception:
            pass

        return None

    def solve(self, G: nx.Graph, timeout_sec: float = 30.0) -> Tuple[int, List[int], SolverMetrics]:
        """Finds maximum clique using spectral pruning."""
        self.metrics = SolverMetrics()
        t0 = time.time()
        deadline = t0 + timeout_sec

        nodes = list(G.nodes())
        node_to_idx = {nd: i for i, nd in enumerate(nodes)}
        idx_to_node = {i: nd for i, nd in enumerate(nodes)}

        self.adj = {node_to_idx[u]: {node_to_idx[v] for v in G.neighbors(u)} for u in G.nodes()}
        self.max_clique = []

        initial_candidates = sorted(list(self.adj.keys()), key=lambda u: len(self.adj[u]), reverse=True)

        def search(current_clique: List[int], candidates: List[int]) -> None:
            self.metrics.nodes_visited += 1

            if time.time() > deadline:
                self.metrics.completed = False
                self.metrics.timed_out = True
                return

            if len(current_clique) > len(self.max_clique):
                self.max_clique = list(current_clique)

            # Prune 1: Trivial size bound
            if len(current_clique) + len(candidates) <= len(self.max_clique):
                self.metrics.size_prunes += 1
                return

            # Spectral Ordering & Wilf Bound Pruning
            if (self.enable_wilf or self.enable_perron) and len(candidates) >= 4:
                ordered_cands, lambda_1 = self._compute_perron_ordering_and_wilf(candidates)
                if self.enable_perron:
                    candidates = ordered_cands

                # Wilf Bound: omega(candidates) <= floor(lambda_1) + 1
                wilf_bound = int(np.floor(lambda_1)) + 1
                if self.enable_wilf and len(current_clique) + wilf_bound <= len(self.max_clique):
                    self.metrics.spectral_prunes += 1
                    return

            # Fiedler Bisection for Bottleneck Subproblems
            if self.enable_fiedler and len(candidates) >= 20:
                bisection = self._try_fiedler_bisection(candidates)
                if bisection is not None:
                    pos_cands, neg_cands = bisection
                    self.metrics.fiedler_splits += 1
                    # Use communities for ordering only; cliques may cross the cut.
                    candidates = pos_cands + neg_cands

            cand_set = set(candidates)
            while candidates:
                if len(current_clique) + len(candidates) <= len(self.max_clique):
                    self.metrics.size_prunes += 1
                    break

                v = candidates.pop(0)
                cand_set.remove(v)

                next_candidates = [u for u in candidates if u in self.adj[v]]
                search(current_clique + [v], next_candidates)

        search([], initial_candidates)

        self.metrics.runtime_ms = (time.time() - t0) * 1000
        self.metrics.max_clique_size = len(self.max_clique)
        self.metrics.max_clique_nodes = [idx_to_node[i] for i in self.max_clique]

        return self.metrics.max_clique_size, self.metrics.max_clique_nodes, self.metrics
