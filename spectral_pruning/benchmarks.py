"""Benchmark Graph Generators for the NP-Hard Maximum Clique Problem.

Provides challenging benchmark instances:
1. Brockington-Culberson style (random graphs with hidden planted cliques).
2. Clustered Bottleneck graphs (two dense cliques joined by sparse edges, ideal for Fiedler spectral bisection).
3. Hamming / Hypercube graphs (hard geometric intersection topologies).
4. Erdős-Rényi critical graphs G(n, 0.5).
5. Mycielski graphs (triangle-free, chromatic number growing, clique number strictly 2).
6. Strongly Regular graphs (Petersen, Clebsch, Paley).
7. Johnson graphs (coding theory / Johnson schemes).
8. Fault-tolerant cluster graphs (c-fat).
9. Sanchis graphs (dense random with hidden cliques).
"""

from __future__ import annotations

import itertools
import random
from typing import Dict, List, Optional, Tuple
import networkx as nx
import numpy as np


def generate_planted_clique_graph(n: int = 60, p: float = 0.45, k_planted: int = 8, seed: int = 42) -> nx.Graph:
    """Generates an Erdős-Rényi graph G(n, p) with a planted clique of size k_planted."""
    random.seed(seed)
    np.random.seed(seed)
    G = nx.erdos_renyi_graph(n, p, seed=seed)
    planted_nodes = list(range(k_planted))
    for i in range(k_planted):
        for j in range(i + 1, k_planted):
            G.add_edge(planted_nodes[i], planted_nodes[j])
    G.name = f"PlantedClique_n{n}_k{k_planted}"
    return G


def generate_clustered_bottleneck_graph(n_cluster: int = 30, p_internal: float = 0.7, p_cross: float = 0.05, seed: int = 42) -> nx.Graph:
    """Generates two dense clusters weakly linked by sparse bottleneck edges.

    Tests the Fiedler vector bisection pruning capability: maximum cliques
    are localized within clusters, and cross-cluster branches can be pruned early.
    """
    random.seed(seed)
    np.random.seed(seed)
    G1 = nx.erdos_renyi_graph(n_cluster, p_internal, seed=seed)
    G2 = nx.erdos_renyi_graph(n_cluster, p_internal, seed=seed + 1)
    
    # Relabel G2 nodes
    G2_relabeled = nx.relabel_nodes(G2, {i: i + n_cluster for i in G2.nodes()})
    
    G = nx.union(G1, G2_relabeled)
    # Add sparse cross edges
    for u in G1.nodes():
        for v in G2_relabeled.nodes():
            if random.random() < p_cross:
                G.add_edge(u, v)
    G.name = f"ClusteredBottleneck_n{2*n_cluster}"
    return G


def generate_hamming_graph(dim: int = 4, alphabet: int = 3) -> nx.Graph:
    """Hamming graph H(dim, alphabet) whose cliques represent error-correcting codes."""
    nodes = []
    # Generate all words of length dim over alphabet
    def get_words(d: int) -> List[Tuple[int, ...]]:
        if d == 0:
            return [()]
        sub = get_words(d - 1)
        return [(a,) + s for a in range(alphabet) for s in sub]

    all_words = get_words(dim)
    G = nx.Graph()
    G.add_nodes_from(range(len(all_words)))
    
    for i in range(len(all_words)):
        for j in range(i + 1, len(all_words)):
            w1, w2 = all_words[i], all_words[j]
            # Edge if Hamming distance == 1
            if sum(1 for a, b in zip(w1, w2) if a != b) == 1:
                G.add_edge(i, j)
    G.name = f"Hamming_{dim}_{alphabet}_n{len(all_words)}"
    return G


def generate_erdos_renyi_critical(n: int = 50, p: float = 0.5, seed: int = 42) -> nx.Graph:
    """Erdős-Rényi graph at density p=0.5 where clique size scales as 2*log_2(n)."""
    G = nx.erdos_renyi_graph(n, p, seed=seed)
    G.name = f"ErdosRenyi_n{n}_p05"
    return G


def get_standard_benchmark_suite() -> List[nx.Graph]:
    """Compiles the standard benchmark suite spanning diverse graph topologies."""
    suite = [
        # 1. Clustered Bottlenecks (Fiedler testbed)
        generate_clustered_bottleneck_graph(n_cluster=20, p_internal=0.75, p_cross=0.03, seed=101),
        generate_clustered_bottleneck_graph(n_cluster=25, p_internal=0.70, p_cross=0.04, seed=102),
        generate_clustered_bottleneck_graph(n_cluster=30, p_internal=0.65, p_cross=0.03, seed=103),
        
        # 2. Planted Cliques (Hidden clique testbed)
        generate_planted_clique_graph(n=45, p=0.40, k_planted=7, seed=201),
        generate_planted_clique_graph(n=50, p=0.45, k_planted=8, seed=202),
        generate_planted_clique_graph(n=55, p=0.45, k_planted=9, seed=203),
        generate_planted_clique_graph(n=60, p=0.50, k_planted=10, seed=204),
        
        # 3. Critical Dense Graphs
        generate_erdos_renyi_critical(n=40, p=0.5, seed=301),
        generate_erdos_renyi_critical(n=45, p=0.5, seed=302),
        generate_erdos_renyi_critical(n=50, p=0.5, seed=303),
        
        # 4. Geometric / Hamming
        generate_hamming_graph(dim=3, alphabet=4),  # n=64
        
        # 5. Extremal Classical Graphs
        nx.petersen_graph(),
        nx.mycielski_graph(4),  # Grötzsch graph (n=11, omega=2)
        nx.mycielski_graph(5),  # Mycielski 5 (n=23, omega=2)
    ]
    # Ensure names
    for g in suite:
        if not hasattr(g, "name") or not g.name:
            g.name = f"Graph_n{g.number_of_nodes()}_m{g.number_of_edges()}"
    return suite


def generate_johnson_graph(n: int = 8, v: int = 2, d: int = 4) -> nx.Graph:
    """Johnson graph J(n, v, d): subsets of size v from {1..n} with Hamming distance >= d."""
    subsets = list(itertools.combinations(range(n), v))
    G = nx.Graph()
    G.add_nodes_from(range(len(subsets)))
    for i in range(len(subsets)):
        s1 = set(subsets[i])
        for j in range(i + 1, len(subsets)):
            s2 = set(subsets[j])
            dist = 2 * (v - len(s1 & s2))
            if dist >= d:
                G.add_edge(i, j)
    G.name = f"johnson{n}-{v}-{d}"
    return G


def generate_cfat_graph(n: int = 200, clique_size: int = 12, seed: int = 42) -> nx.Graph:
    """Fault-tolerant graph c-fat with dense cliques and sparse inter-cluster noise."""
    random.seed(seed)
    np.random.seed(seed)
    G = nx.Graph()
    G.add_nodes_from(range(n))

    # Construct primary target clique
    target_clique = list(range(clique_size))
    for i in range(clique_size):
        for j in range(i + 1, clique_size):
            G.add_edge(target_clique[i], target_clique[j])

    # Construct secondary clusters of size ~clique_size - 1
    offset = clique_size
    while offset < n:
        c_len = min(clique_size - 1, n - offset)
        cluster = list(range(offset, offset + c_len))
        for i in range(len(cluster)):
            for j in range(i + 1, len(cluster)):
                if random.random() < 0.90:
                    G.add_edge(cluster[i], cluster[j])
        offset += c_len

    # Add sparse cross-cluster fault-tolerant edges
    for u in range(n):
        for v in range(u + 1, n):
            if not G.has_edge(u, v) and random.random() < 0.04:
                G.add_edge(u, v)

    G.name = f"c-fat{n}-{clique_size // 12}"
    return G


def generate_brock_graph(n: int = 200, k_planted: int = 14, p: float = 0.45, seed: int = 101) -> nx.Graph:
    """Brockington-Culberson style graph with planted clique masked by degree-equalizing edges."""
    random.seed(seed)
    np.random.seed(seed)
    G = nx.erdos_renyi_graph(n, p, seed=seed)

    planted = list(range(k_planted))
    for i in range(k_planted):
        for j in range(i + 1, k_planted):
            G.add_edge(planted[i], planted[j])

    # Degree compensation: slightly prune external edges of planted vertices to obscure clique
    for u in planted:
        neighbors = [v for v in G.neighbors(u) if v not in planted]
        for v in neighbors:
            if random.random() < 0.15:
                G.remove_edge(u, v)

    G.name = f"brock{n}_1"
    return G


def generate_san_graph(n: int = 200, p: float = 0.70, k_planted: int = 15, seed: int = 202) -> nx.Graph:
    """Sanchis dense random graph with planted clique."""
    random.seed(seed)
    np.random.seed(seed)
    G = nx.erdos_renyi_graph(n, p, seed=seed)

    planted = list(range(k_planted))
    for i in range(k_planted):
        for j in range(i + 1, k_planted):
            G.add_edge(planted[i], planted[j])

    G.name = f"san{n}_{p}_1"
    return G


def get_extended_benchmark_suite() -> List[nx.Graph]:
    """Compiles the extended benchmark suite including Johnson, c-fat, brock, and san topologies."""
    suite = list(get_standard_benchmark_suite())
    suite.extend([
        generate_johnson_graph(n=8, v=2, d=4),
        generate_johnson_graph(n=8, v=4, d=4),
        generate_cfat_graph(n=200, clique_size=12, seed=42),
        generate_cfat_graph(n=200, clique_size=24, seed=43),
        generate_brock_graph(n=200, k_planted=14, p=0.45, seed=101),
        generate_san_graph(n=200, p=0.70, k_planted=15, seed=201),
    ])
    for g in suite:
        if not hasattr(g, "name") or not g.name:
            g.name = f"Graph_n{g.number_of_nodes()}_m{g.number_of_edges()}"
    return suite

