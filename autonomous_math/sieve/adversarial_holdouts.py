"""Deterministic graph families that challenge finite-data conjecture fits.

Mixed structures matter: a dense component joined to a sparse one can violate
a bound that survives separate cliques, stars, and paths. The first graphs are
concrete witnesses found during the spectral-candidate audit. Most graphs have
at most 32 vertices; two larger disconnected bipartite witnesses use existing
polynomial exact shortcuts for coloring, clique and independence numbers.
"""

from __future__ import annotations

import networkx as nx

HOLDOUT_REVISION = "mixed-structures-v2-disconnected"


def _bridge_cliques(left: int, right: int) -> nx.Graph:
    graph = nx.disjoint_union(nx.complete_graph(left), nx.complete_graph(right))
    graph.add_edge(0, left)
    graph.name = f"holdout_bridge_cliques_{left}_{right}"
    return graph


def _leaf_star_clique(leaves: int, clique_order: int) -> nx.Graph:
    graph = nx.disjoint_union(nx.star_graph(leaves), nx.complete_graph(clique_order))
    graph.add_edge(1, leaves + 1)
    graph.name = f"holdout_leaf_star_{leaves}_clique_{clique_order}"
    return graph


def holdout_graphs() -> list[nx.Graph]:
    """Return fresh, labeled graphs in a reproducible adversarial-check order.

    Labels explain the construction; all numerical checks use graph topology.
    This is a falsification suite, not a proof or an exhaustive graph search.
    """
    graphs = [
        _bridge_cliques(5, 5),
        _leaf_star_clique(10, 6),
        nx.lollipop_graph(8, 8),
        nx.wheel_graph(24),
        nx.complete_graph(25),
        nx.star_graph(15),
        nx.star_graph(26),
    ]
    for graph, name in zip(graphs[2:], (
        "holdout_lollipop_8_8", "holdout_wheel_24", "holdout_clique_25",
        "holdout_star_15", "holdout_star_26",
    )):
        graph.name = name

    matching = nx.disjoint_union_all([nx.path_graph(2) for _ in range(22)])
    matching.name = "holdout_matching_22"
    cycles = nx.disjoint_union_all([nx.cycle_graph(4) for _ in range(16)])
    cycles.name = "holdout_cycles_4_16"
    graphs.extend((matching, cycles))

    for order in (8, 14, 24, 32):
        clique_order = order // 2
        # Large clique cores joined to tails make naive exact coloring spend
        # time disproving many smaller color counts. Eight-vertex dense cores
        # still expose the mixed-structure failures without that solver cost.
        mixed_clique_order = min(clique_order, 8)
        families = [
            ("path", nx.path_graph(order)),
            ("cycle", nx.cycle_graph(order)),
            ("clique", nx.complete_graph(order)),
            ("empty", nx.empty_graph(order)),
            ("star", nx.star_graph(order - 1)),
            ("balanced_bipartite", nx.complete_bipartite_graph(clique_order, order - clique_order)),
            ("wheel", nx.wheel_graph(order)),
            ("lollipop", nx.lollipop_graph(mixed_clique_order, order - mixed_clique_order)),
        ]
        for family, graph in families:
            graph.name = f"holdout_{family}_{order}"
            graphs.append(graph)
        graphs.append(_bridge_cliques(mixed_clique_order, mixed_clique_order))
        graphs.append(_leaf_star_clique(order - mixed_clique_order - 1, mixed_clique_order))

    disconnected = [
        nx.disjoint_union(nx.complete_graph(3), nx.path_graph(8)),
        nx.disjoint_union(nx.path_graph(2), nx.empty_graph(1)),
    ]
    for index, graph in enumerate(disconnected):
        graph.name = f"holdout_disconnected_{index}"
        graphs.append(graph)

    # Avoid counting a repeated fixed witness as additional evidence. Every
    # constructor above uses consecutive integer labels, so no isomorphism
    # search or canonicalization dependency is needed here.
    unique = []
    seen = set()
    for graph in graphs:
        key = (len(graph), tuple(sorted((min(u, v), max(u, v)) for u, v in graph.edges())))
        if key not in seen:
            seen.add(key)
            unique.append(graph)
    return unique
