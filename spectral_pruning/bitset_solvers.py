"""Exact bitset maximum-clique search with optional finite-graph clique bounds.

Degree and Perron ordering share the same branch-and-bound implementation.
The optional degree and edge-count bounds are applied to the induced candidate
subgraph; neither a numerical eigenvalue estimate nor a vertex partition prunes
vertices. Timed-out results are incumbents, never certified optima.
"""
from __future__ import annotations

import math
import time
from typing import Any, Dict, List, Tuple

import networkx as nx
import numpy as np


class BitsetSolverMetrics:
    def __init__(self) -> None:
        self.nodes_visited = 0
        self.size_prunes = 0
        self.color_prunes = 0
        self.degree_prunes = 0
        self.edge_prunes = 0
        self.clique_bound_checks = 0
        self.global_bound_stops = 0
        self.clique_bounds_enabled = False
        self.root_degree_bound = None
        self.root_edge_bound = None
        self.runtime_ms = 0.0
        self.completed = True
        self.timed_out = False
        self.max_clique_size = 0
        self.max_clique: List[Any] = []

    def to_dict(self) -> Dict[str, Any]:
        return {key: value for key, value in vars(self).items() if key != "max_clique"}


def edge_count_clique_bound(edge_count: int) -> int:
    """Largest integer k satisfying k(k-1) <= 2m, without float rounding.

    For m=0 this bound is 1; a graph-order bound separately handles the empty
    graph. Integer square root stays exact even for large edge counts.
    """
    if not isinstance(edge_count, int) or edge_count < 0:
        raise ValueError("The edge count must be a nonnegative integer")
    return (1 + math.isqrt(1 + 8 * edge_count)) // 2


def _parse_dimacs_clq(file_path: str) -> nx.Graph:
    """Parse DIMACS .clq vertices and edges; provenance is checked by the runner."""
    graph = nx.Graph()
    with open(file_path, encoding="utf-8") as handle:
        for line in handle:
            parts = line.strip().split()
            if not parts or parts[0] == "c":
                continue
            if parts[0] == "p":
                graph.add_nodes_from(range(int(parts[2])))
            elif parts[0] == "e":
                graph.add_edge(int(parts[1]) - 1, int(parts[2]) - 1)
    graph.name = file_path.split("/")[-1].replace(".clq", "")
    return graph


class BitsetBaselineSolver:
    """Degree-ordered exact search; optional additional bounds default off.

    Keeping the switch off preserves the classical coloring baseline. Comparing
    True and False uses this same search and ordering, including preprocessing.
    """

    def __init__(self, enable_clique_bounds: bool = False) -> None:
        self.enable_clique_bounds = enable_clique_bounds
        self.metrics = BitsetSolverMetrics()
        self.adj_mask: List[int] = []
        self.n = 0
        self.max_clique: List[int] = []

    def _greedy_coloring_bound(self, p_mask: int) -> int:
        colors = 0
        uncolored = p_mask
        while uncolored:
            colors += 1
            v = (uncolored & -uncolored).bit_length() - 1
            uncolored &= ~(1 << v)
            non_neighbors = uncolored & ~self.adj_mask[v]
            while non_neighbors:
                w = (non_neighbors & -non_neighbors).bit_length() - 1
                non_neighbors &= ~(1 << w)
                uncolored &= ~(1 << w)
                non_neighbors &= ~self.adj_mask[w]
        return colors

    def _root_ordering(self, graph: nx.Graph, node_to_idx: Dict[Any, int]) -> List[int]:
        return sorted(range(self.n), key=lambda v: self.adj_mask[v].bit_count(), reverse=True)

    def _degree_edge_bounds(self, p_mask: int) -> Tuple[int, int]:
        """Clique ceilings for the induced candidate graph, not the whole graph."""
        count = p_mask.bit_count()
        if not count:
            return 0, 0
        max_degree = 0
        twice_edges = 0
        remaining = p_mask
        while remaining:
            bit = remaining & -remaining
            vertex = bit.bit_length() - 1
            remaining ^= bit
            degree = (self.adj_mask[vertex] & p_mask).bit_count()
            max_degree = max(max_degree, degree)
            twice_edges += degree
        return min(count, max_degree + 1), min(count, edge_count_clique_bound(twice_edges // 2))

    def _clique_bound_prunes(self, p_mask: int, budget: int) -> bool:
        """Can a clique in these candidates exceed the remaining incumbent budget?

        If both bounds already permit improvement, stop scanning: additional
        degrees cannot lower the maximum degree or the edge sum. This shortcut
        only declines to prune and therefore cannot discard a possible clique.
        """
        if budget < 1:
            return False
        self.metrics.clique_bound_checks += 1
        max_degree = 0
        twice_edges = 0
        required_edge_sum = budget * (budget + 1)
        remaining = p_mask
        while remaining:
            bit = remaining & -remaining
            vertex = bit.bit_length() - 1
            remaining ^= bit
            degree = (self.adj_mask[vertex] & p_mask).bit_count()
            max_degree = max(max_degree, degree)
            twice_edges += degree
            if max_degree >= budget and twice_edges >= required_edge_sum:
                return False
        if max_degree < budget:
            self.metrics.degree_prunes += 1
            return True
        if twice_edges < required_edge_sum:
            self.metrics.edge_prunes += 1
            return True
        return False

    def solve(self, graph: nx.Graph, timeout_sec: float = 30.0) -> Tuple[int, List[Any], BitsetSolverMetrics]:
        if graph.is_directed() or graph.is_multigraph() or nx.number_of_selfloops(graph):
            raise ValueError("Maximum-clique proofs and search require a finite simple undirected graph")
        if not math.isfinite(timeout_sec) or timeout_sec < 0:
            raise ValueError("The search timeout must be finite and nonnegative")
        self.metrics = BitsetSolverMetrics()
        self.metrics.clique_bounds_enabled = self.enable_clique_bounds
        started = time.monotonic()
        deadline = started + timeout_sec
        nodes = list(graph.nodes())
        node_to_idx = {node: i for i, node in enumerate(nodes)}
        self.n = len(nodes)
        self.adj_mask = [0] * self.n
        for u, v in graph.edges():
            iu, iv = node_to_idx[u], node_to_idx[v]
            self.adj_mask[iu] |= 1 << iv
            self.adj_mask[iv] |= 1 << iu
        initial_p = (1 << self.n) - 1
        global_bound = self.n
        if self.enable_clique_bounds:
            degree_bound, edge_bound = self._degree_edge_bounds(initial_p)
            self.metrics.root_degree_bound = degree_bound
            self.metrics.root_edge_bound = edge_bound
            global_bound = min(degree_bound, edge_bound)
        ordered_vertices = self._root_ordering(graph, node_to_idx)
        self.max_clique = []
        best_size = 0

        def expired() -> bool:
            if time.monotonic() > deadline:
                self.metrics.completed = False
                self.metrics.timed_out = True
                return True
            return False

        def search(current_clique: List[int], p_mask: int) -> None:
            nonlocal best_size
            self.metrics.nodes_visited += 1
            if expired():
                return
            if len(current_clique) > best_size:
                best_size = len(current_clique)
                self.max_clique = list(current_clique)
            if self.enable_clique_bounds and best_size >= global_bound:
                self.metrics.global_bound_stops = 1
                return
            count = p_mask.bit_count()
            if len(current_clique) + count <= best_size:
                self.metrics.size_prunes += 1
                return
            if self.enable_clique_bounds and count >= 2 and self._clique_bound_prunes(p_mask, best_size - len(current_clique)):
                return
            if count >= 3 and len(current_clique) + self._greedy_coloring_bound(p_mask) <= best_size:
                self.metrics.color_prunes += 1
                return
            remaining = p_mask
            while remaining:
                if len(current_clique) + remaining.bit_count() <= best_size:
                    self.metrics.size_prunes += 1
                    break
                bit = remaining & -remaining
                vertex = bit.bit_length() - 1
                remaining ^= bit
                search(current_clique + [vertex], remaining & self.adj_mask[vertex])
                if self.metrics.timed_out or (self.enable_clique_bounds and best_size >= global_bound):
                    return

        remaining = initial_p
        for vertex in ordered_vertices:
            if best_size >= global_bound:
                if self.enable_clique_bounds:
                    self.metrics.global_bound_stops = 1
                break
            if expired():
                break
            remaining &= ~(1 << vertex)
            search([vertex], remaining & self.adj_mask[vertex])
            if self.metrics.timed_out:
                break
        self.metrics.runtime_ms = (time.monotonic() - started) * 1000
        self.metrics.max_clique_size = best_size
        self.metrics.max_clique = [nodes[i] for i in self.max_clique]
        return best_size, self.metrics.max_clique, self.metrics


class BitsetSpectralSolver(BitsetBaselineSolver):
    """The same exact search with Perron centrality used only for root ordering."""

    def _root_ordering(self, graph: nx.Graph, node_to_idx: Dict[Any, int]) -> List[int]:
        return self._compute_perron_ordering(graph, node_to_idx)

    def _compute_perron_ordering(self, graph: nx.Graph, node_to_idx: Dict[Any, int]) -> List[int]:
        n = len(node_to_idx)
        if len({degree for _, degree in graph.degree()}) <= 1:
            return list(range(n))
        adjacency = np.zeros((n, n), dtype=np.float32)
        for u, v in graph.edges():
            iu, iv = node_to_idx[u], node_to_idx[v]
            adjacency[iu, iv] = adjacency[iv, iu] = 1.0
        vector = np.ones(n, dtype=np.float32) / np.sqrt(n)
        for _ in range(15):
            updated = adjacency @ vector + vector
            norm = np.linalg.norm(updated)
            if norm < 1e-6:
                break
            vector = updated / norm
        return [int(i) for i in np.argsort(-vector, kind="stable")]
