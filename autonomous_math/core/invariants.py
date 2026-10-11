"""Comprehensive Graph Invariant Computation Engine.

Provides exact polynomial invariants, pure NumPy spectral routines,
exact Z3 SMT/SAT solvers for NP-hard invariants (chromatic, clique, independence),
structural predicates, and unified GraphInvariantEvaluator matching pipeline contracts.
"""

from __future__ import annotations

import math
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

import networkx as nx
import numpy as np
import z3

from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.expander_codes import (
    compute_parity_code_distance, compute_parity_code_dimension, compute_unique_neighbor_radius,
)

GraphLike = Union[nx.Graph, GraphInstance]


def _to_graph_instance(G: GraphLike) -> GraphInstance:
    if isinstance(G, GraphInstance):
        return G
    return GraphInstance.from_networkx(G)


# ============================================================================
# 1. Elementary Order, Size, Degrees & Density
# ============================================================================


def compute_order(G: GraphLike) -> int:
    """Number of vertices n = |V|."""
    inst = _to_graph_instance(G)
    return inst.order


def compute_size(G: GraphLike) -> int:
    """Number of edges m = |E|."""
    inst = _to_graph_instance(G)
    return inst.size


def compute_max_degree(G: GraphLike) -> int:
    """Maximum degree Delta(G)."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0
    degrees = [0] * inst.order
    for u, v in inst.edges:
        degrees[u] += 1
        degrees[v] += 1
    return max(degrees) if degrees else 0


def compute_min_degree(G: GraphLike) -> int:
    """Minimum degree delta(G)."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0
    degrees = [0] * inst.order
    for u, v in inst.edges:
        degrees[u] += 1
        degrees[v] += 1
    return min(degrees) if degrees else 0


def compute_average_degree(G: GraphLike) -> float:
    """Average degree d_avg = 2m / n."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0.0
    return float(2.0 * inst.size / inst.order)


def compute_density(G: GraphLike) -> float:
    """Graph density rho = 2m / (n * (n - 1)). Returns 0.0 for n < 2."""
    inst = _to_graph_instance(G)
    if inst.order < 2:
        return 0.0
    return float(2.0 * inst.size / (inst.order * (inst.order - 1)))


# ============================================================================
# 2. Metric & Topological Invariants (Triangles, Girth, Diameter, Radius)
# ============================================================================


def compute_triangle_count(G: GraphLike) -> int:
    """Triangle count T(G) = (1/6) * Tr(A^3) = (1/6) * sum(A * (A @ A))."""
    inst = _to_graph_instance(G)
    if inst.order < 3 or inst.size < 3:
        return 0
    A = inst.to_adjacency_matrix()
    A2 = A @ A
    tr_A3 = int(np.sum(A * A2))
    return tr_A3 // 6


def compute_girth(G: GraphLike) -> Union[int, float]:
    """Shortest cycle length g(G). Returns float('inf') if acyclic."""
    inst = _to_graph_instance(G)
    if inst.order < 3 or inst.size < 3:
        return float("inf")

    nx_g = inst.to_networkx()
    min_cycle = float("inf")
    nodes = list(nx_g.nodes())

    for s in nodes:
        dist: Dict[int, int] = {s: 0}
        parent: Dict[int, Optional[int]] = {s: None}
        queue = [s]

        while queue:
            u = queue.pop(0)
            if dist[u] * 2 >= min_cycle:
                break
            for v in nx_g.neighbors(u):
                if v not in dist:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    queue.append(v)
                elif parent[u] != v:
                    cycle_len = dist[u] + dist[v] + 1
                    if cycle_len < min_cycle:
                        min_cycle = cycle_len
                        if min_cycle == 3:
                            return 3
    return min_cycle


def compute_diameter(G: GraphLike) -> Union[int, float]:
    """Diameter D(G). Returns float('inf') if disconnected, 0 if n <= 1."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0
    nx_g = inst.to_networkx()
    if not nx.is_connected(nx_g):
        return float("inf")
    ecc = nx.eccentricity(nx_g)
    return max(ecc.values())


def compute_radius(G: GraphLike) -> Union[int, float]:
    """Radius R(G). Returns float('inf') if disconnected, 0 if n <= 1."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0
    nx_g = inst.to_networkx()
    if not nx.is_connected(nx_g):
        return float("inf")
    ecc = nx.eccentricity(nx_g)
    return min(ecc.values())


# ============================================================================
# 3. Spectral Invariants (Adjacency & Laplacian spectra via pure NumPy)
# ============================================================================


def compute_adjacency_spectrum(G: GraphLike) -> List[float]:
    """Adjacency eigenvalues sorted descending: lambda_1 >= ... >= lambda_n."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return []
    A = inst.to_adjacency_matrix().astype(float)
    evals = np.linalg.eigvalsh(A)
    return [float(x) for x in np.sort(evals)[::-1]]


def compute_spectral_radius(G: GraphLike) -> float:
    """Largest adjacency eigenvalue lambda_1 = lambda_max."""
    spectrum = compute_adjacency_spectrum(G)
    return float(spectrum[0]) if spectrum else 0.0


def compute_smallest_adjacency_eigenvalue(G: GraphLike) -> float:
    """Smallest adjacency eigenvalue lambda_n = lambda_min."""
    spectrum = compute_adjacency_spectrum(G)
    return float(spectrum[-1]) if spectrum else 0.0


compute_min_adjacency_eigenvalue = compute_smallest_adjacency_eigenvalue


def compute_laplacian_spectrum(G: GraphLike) -> List[float]:
    """Combinatorial Laplacian eigenvalues sorted ascending: mu_1 <= ... <= mu_n."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return []
    A = inst.to_adjacency_matrix().astype(float)
    degrees = np.sum(A, axis=1)
    L = np.diag(degrees) - A
    evals = np.linalg.eigvalsh(L)
    evals = np.maximum(evals, 0.0)
    return [float(x) for x in np.sort(evals)]


def compute_algebraic_connectivity(G: GraphLike) -> float:
    """Second smallest Laplacian eigenvalue mu_2 (Fiedler value)."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0.0
    nx_g = inst.to_networkx()
    if not nx.is_connected(nx_g):
        return 0.0
    spectrum = compute_laplacian_spectrum(inst)
    if len(spectrum) < 2:
        return 0.0
    return float(spectrum[1])


def compute_laplacian_spectral_radius(G: GraphLike) -> float:
    """Largest Laplacian eigenvalue mu_n."""
    spectrum = compute_laplacian_spectrum(G)
    return float(spectrum[-1]) if spectrum else 0.0


def compute_hoffman_bound(G: GraphLike) -> float:
    """Hoffman spectral lower bound on chromatic number: 1 - (lambda_1 / lambda_n)."""
    inst = _to_graph_instance(G)
    if inst.size == 0:
        return 1.0 if inst.order > 0 else 0.0
    l_max = compute_spectral_radius(inst)
    l_min = compute_smallest_adjacency_eigenvalue(inst)
    if abs(l_min) < 1e-12:
        return 1.0
    return float(1.0 - (l_max / l_min))


def compute_wilf_bound(G: GraphLike) -> float:
    """Wilf spectral upper bound on chromatic number: 1 + lambda_1."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0.0
    l_max = compute_spectral_radius(inst)
    return float(1.0 + l_max)


def compute_signless_laplacian_spectrum(G: GraphLike) -> List[float]:
    """Signless Laplacian Q = D + A eigenvalues sorted descending: q_1 >= ... >= q_n >= 0."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return []
    A = inst.to_adjacency_matrix().astype(float)
    degrees = np.sum(A, axis=1)
    Q = np.diag(degrees) + A
    evals = np.linalg.eigvalsh(Q)
    evals = np.maximum(evals, 0.0)
    return [float(x) for x in np.sort(evals)[::-1]]


def compute_signless_laplacian_spectral_radius(G: GraphLike) -> float:
    """Largest signless Laplacian eigenvalue q_1 = lambda_max(Q)."""
    spectrum = compute_signless_laplacian_spectrum(G)
    return float(spectrum[0]) if spectrum else 0.0


def compute_normalized_laplacian_spectrum(G: GraphLike) -> List[float]:
    """Normalized Laplacian L_norm = D^{-1/2} L D^{-1/2} eigenvalues sorted ascending: 0 <= lambda_1 <= ... <= lambda_n <= 2."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return []
    A = inst.to_adjacency_matrix().astype(float)
    degs = np.sum(A, axis=1)
    pos_mask = degs > 0
    inv_sqrt_d = np.zeros(inst.order, dtype=float)
    inv_sqrt_d[pos_mask] = 1.0 / np.sqrt(degs[pos_mask])
    D_inv_sqrt = np.diag(inv_sqrt_d)
    L_norm = np.diag(pos_mask.astype(float)) - D_inv_sqrt @ A @ D_inv_sqrt
    evals = np.linalg.eigvalsh(L_norm)
    evals = np.clip(evals, 0.0, 2.0)
    return [float(x) for x in np.sort(evals)]


def compute_normalized_laplacian_spectral_gap(G: GraphLike) -> float:
    """Second smallest normalized Laplacian eigenvalue lambda_2^L (normalized spectral gap / algebraic connectivity)."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0.0
    nx_g = inst.to_networkx()
    if not nx.is_connected(nx_g):
        return 0.0
    spectrum = compute_normalized_laplacian_spectrum(inst)
    if len(spectrum) < 2:
        return 0.0
    return float(spectrum[1])


def compute_normalized_laplacian_spectral_radius(G: GraphLike) -> float:
    """Largest normalized Laplacian eigenvalue lambda_n^L."""
    spectrum = compute_normalized_laplacian_spectrum(G)
    return float(spectrum[-1]) if spectrum else 0.0


def compute_estrada_index(G: GraphLike) -> float:
    """Estrada index EE(G) = sum_{i=1}^n exp(lambda_i(A)) = Tr(exp(A))."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0.0
    spectrum = compute_adjacency_spectrum(inst)
    return float(np.sum(np.exp(np.array(spectrum))))


def compute_graph_energy(G: GraphLike) -> float:
    """Graph energy E(G) = sum_{i=1}^n |lambda_i(A)|."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0.0
    spectrum = compute_adjacency_spectrum(inst)
    return float(np.sum(np.abs(np.array(spectrum))))


def compute_complement_spectral_radius(G: GraphLike) -> float:
    """Spectral radius of the complement graph lambda_1(G_bar)."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0.0
    n = inst.order
    A = inst.to_adjacency_matrix().astype(float)
    A_bar = (np.ones((n, n), dtype=float) - np.eye(n, dtype=float)) - A
    evals = np.linalg.eigvalsh(A_bar)
    return float(np.max(evals)) if len(evals) > 0 else 0.0


def compute_nordhaus_gaddum_spectral_sum(G: GraphLike) -> float:
    """Nordhaus-Gaddum spectral sum: lambda_1(G) + lambda_1(G_bar)."""
    return float(compute_spectral_radius(G) + compute_complement_spectral_radius(G))


def compute_nordhaus_gaddum_spectral_product(G: GraphLike) -> float:
    """Nordhaus-Gaddum spectral product: lambda_1(G) * lambda_1(G_bar)."""
    return float(compute_spectral_radius(G) * compute_complement_spectral_radius(G))


def compute_spectral_spread(G: GraphLike) -> float:
    """Spectral spread s(G) = lambda_1(G) - lambda_n(G) = lambda_max - lambda_min."""
    inst = _to_graph_instance(G)
    if inst.order <= 1:
        return 0.0
    l_max = compute_spectral_radius(inst)
    l_min = compute_smallest_adjacency_eigenvalue(inst)
    return float(l_max - l_min)


compute_spread = compute_spectral_spread
spectral_spread = compute_spectral_spread


# Functional aliases matching invariant keys
signless_laplacian_spectral_radius = compute_signless_laplacian_spectral_radius
normalized_laplacian_spectral_gap = compute_normalized_laplacian_spectral_gap
normalized_laplacian_spectral_radius = compute_normalized_laplacian_spectral_radius
estrada_index = compute_estrada_index
graph_energy = compute_graph_energy
complement_spectral_radius = compute_complement_spectral_radius
nordhaus_gaddum_spectral_sum = compute_nordhaus_gaddum_spectral_sum
nordhaus_gaddum_spectral_product = compute_nordhaus_gaddum_spectral_product


# ============================================================================
# 4. NP-Hard Invariants (Chromatic, Clique, Independence via Z3 SMT)
# ============================================================================


def compute_chromatic_number(G: GraphLike, timeout_ms: int = 5000) -> int:
    """Exact chromatic number chi(G) computed via Z3 Boolean SAT with symmetry breaking."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0
    if inst.size == 0:
        return 1

    if inst.size == inst.order * (inst.order - 1) // 2:
        return inst.order

    nx_g = inst.to_networkx()
    if nx.is_bipartite(nx_g):
        return 2

    delta = compute_max_degree(inst)
    max_k = delta + 1

    nodes = list(range(inst.order))
    edges = inst.edges

    # Fast lower bound: triangle count > 0 -> omega >= 3 -> chi >= 3
    omega_lb = 3

    context = z3.Context()
    for k in range(omega_lb, max_k + 1):
        s = z3.Solver(ctx=context)
        s.set("timeout", timeout_ms)

        # x[v, c] is True iff vertex v is colored with color c
        x = {(v, c): z3.Bool(f"x_{v}_{c}", ctx=context) for v in nodes for c in range(k)}

        # 1. At least one color per vertex
        for v in nodes:
            s.add(z3.Or([x[(v, c)] for c in range(k)]))

        # 2. Adjacent vertices cannot share a color
        for u, v in edges:
            for c in range(k):
                s.add(z3.Not(z3.And(x[(u, c)], x[(v, c)])))

        # 3. Symmetry breaking: node 0 has color 0
        s.add(x[(nodes[0], 0)])
        if inst.order > 1 and len(edges) > 0:
            first_neighbor = edges[0][1] if edges[0][0] == 0 else edges[0][0]
            s.add(x[(first_neighbor, 1)])

        res = s.check()
        if res == z3.sat:
            return k
        elif res == z3.unknown:
            raise TimeoutError(f"Z3 timed out solving chromatic number for k={k}")

    return max_k


def compute_clique_number(G: GraphLike, timeout_ms: int = 5000) -> int:
    """Exact clique number omega(G) computed via Z3 Optimize."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0
    if inst.size == 0:
        return 1
    if inst.size == inst.order * (inst.order - 1) // 2:
        return inst.order

    # Triangle-free check shortcut
    if compute_triangle_count(inst) == 0:
        return 2 if inst.size > 0 else 1

    context = z3.Context()
    opt = z3.Optimize(ctx=context)
    opt.set("timeout", timeout_ms)

    nodes = list(range(inst.order))
    x = {v: z3.Bool(f"clique_{v}", ctx=context) for v in nodes}
    edge_set = set(inst.edges)

    for i in range(inst.order):
        for j in range(i + 1, inst.order):
            if (i, j) not in edge_set:
                opt.add(z3.Not(z3.And(x[i], x[j])))

    total = z3.Sum([z3.If(x[v], 1, 0) for v in nodes])
    h = opt.maximize(total)

    res = opt.check()
    if res == z3.sat:
        if not opt.lower(h).eq(opt.upper(h)):
            raise TimeoutError("Clique optimum has not been established")
        return opt.lower(h).as_long()
    elif res == z3.unknown:
        raise TimeoutError("Z3 timed out solving clique number")
    return 1


def compute_independence_number(G: GraphLike, timeout_ms: int = 5000) -> int:
    """Exact independence number alpha(G) computed via Z3 Optimize / Konig theorem."""
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return 0
    if inst.size == 0:
        return inst.order
    if inst.size == inst.order * (inst.order - 1) // 2:
        return 1

    nx_g = inst.to_networkx()
    # Polynomial time shortcut for bipartite graphs via Konig's Theorem.
    # On disconnected bipartite graphs, maximum matching decomposes over connected components.
    if nx.is_bipartite(nx_g):
        try:
            total_matching_size = 0
            for comp in nx.connected_components(nx_g):
                sub = nx_g.subgraph(comp)
                matching = nx.bipartite.maximum_matching(sub)
                total_matching_size += len(matching) // 2
            return inst.order - total_matching_size
        except Exception:
            # Fall back to general component decomposition / Z3 optimization
            pass

    # Disconnected graph decomposition: alpha(G) = sum(alpha(C_i)) across connected components
    comps = list(nx.connected_components(nx_g))
    if len(comps) > 1:
        return sum(
            compute_independence_number(nx_g.subgraph(comp), timeout_ms=timeout_ms)
            for comp in comps
        )

    context = z3.Context()
    opt = z3.Optimize(ctx=context)
    opt.set("timeout", timeout_ms)

    nodes = list(range(inst.order))
    x = {v: z3.Bool(f"indep_{v}", ctx=context) for v in nodes}

    for u, v in inst.edges:
        opt.add(z3.Not(z3.And(x[u], x[v])))

    total = z3.Sum([z3.If(x[v], 1, 0) for v in nodes])
    h = opt.maximize(total)

    res = opt.check()
    if res == z3.sat:
        if not opt.lower(h).eq(opt.upper(h)):
            raise TimeoutError("Independence optimum has not been established")
        return opt.lower(h).as_long()
    elif res == z3.unknown:
        raise TimeoutError("Z3 timed out solving independence number")
    return 1


# ============================================================================
# 5. Structural Predicates
# ============================================================================


def is_bipartite(G: GraphLike) -> bool:
    nx_g = _to_graph_instance(G).to_networkx()
    return bool(nx.is_bipartite(nx_g))


def is_triangle_free(G: GraphLike) -> bool:
    return compute_triangle_count(G) == 0


def is_regular(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return True
    return compute_max_degree(inst) == compute_min_degree(inst)


def is_connected(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return False
    return bool(nx.is_connected(inst.to_networkx()))


def is_tree(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    return is_connected(inst) and (inst.size == inst.order - 1)


def is_forest(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return True
    nx_g = inst.to_networkx()
    num_components = nx.number_connected_components(nx_g)
    return inst.size == inst.order - num_components


def is_planar(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return True
    nx_g = inst.to_networkx()
    return bool(nx.check_planarity(nx_g)[0])


def is_empty(G: GraphLike) -> bool:
    return _to_graph_instance(G).size == 0


def is_complete(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return False
    return inst.size == (inst.order * (inst.order - 1) // 2)


def is_chordal(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return True
    nx_g = inst.to_networkx()
    return bool(nx.is_chordal(nx_g))


def is_eulerian(G: GraphLike) -> bool:
    inst = _to_graph_instance(G)
    if inst.order == 0:
        return False
    nx_g = inst.to_networkx()
    return bool(nx.is_eulerian(nx_g))


# ============================================================================
# 6. Alias Mapping & Unified GraphInvariantEvaluator
# ============================================================================

INVARIANT_ALIASES: Dict[str, str] = {
    # Order & Size
    "n": "order",
    "order": "order",
    "vertices": "order",
    "num_vertices": "order",
    "m": "size",
    "size": "size",
    "edges": "size",
    "num_edges": "size",
    # Degrees & Density
    "delta_max": "max_degree",
    "Delta": "max_degree",
    "max_degree": "max_degree",
    "delta_min": "min_degree",
    "delta": "min_degree",
    "min_degree": "min_degree",
    "d_avg": "average_degree",
    "avg_degree": "average_degree",
    "average_degree": "average_degree",
    "rho": "density",
    "density": "density",
    # Topological & Metric
    "triangles": "triangle_count",
    "triangle_count": "triangle_count",
    "T": "triangle_count",
    "g": "girth",
    "girth": "girth",
    "diam": "diameter",
    "diameter": "diameter",
    "D": "diameter",
    "rad": "radius",
    "radius": "radius",
    "R": "radius",
    # Spectral Adjacency
    "lambda_1": "spectral_radius",
    "lambda_max": "spectral_radius",
    "spectral_radius": "spectral_radius",
    "lambda_n": "smallest_adjacency_eigenvalue",
    "lambda_min": "smallest_adjacency_eigenvalue",
    "smallest_adjacency_eigenvalue": "smallest_adjacency_eigenvalue",
    "min_adjacency_eigenvalue": "smallest_adjacency_eigenvalue",
    "adjacency_spectrum": "adjacency_spectrum",
    # Spectral Laplacian
    "mu_2": "algebraic_connectivity",
    "fiedler": "algebraic_connectivity",
    "fiedler_value": "algebraic_connectivity",
    "algebraic_connectivity": "algebraic_connectivity",
    "mu_max": "laplacian_spectral_radius",
    "mu_n": "laplacian_spectral_radius",
    "laplacian_radius": "laplacian_spectral_radius",
    "laplacian_spectral_radius": "laplacian_spectral_radius",
    "laplacian_spectrum": "laplacian_spectrum",
    # Spectral Bounds
    "hoffman": "hoffman_bound",
    "hoffman_bound": "hoffman_bound",
    "wilf": "wilf_bound",
    "wilf_bound": "wilf_bound",
    # Signless Laplacian
    "q_1": "signless_laplacian_spectral_radius",
    "q_max": "signless_laplacian_spectral_radius",
    "q_spectral_radius": "signless_laplacian_spectral_radius",
    "signless_laplacian_radius": "signless_laplacian_spectral_radius",
    "signless_laplacian_spectral_radius": "signless_laplacian_spectral_radius",
    "signless_laplacian_spectrum": "signless_laplacian_spectrum",
    "q_spectrum": "signless_laplacian_spectrum",
    # Normalized Laplacian
    "lambda_2_norm": "normalized_laplacian_spectral_gap",
    "normalized_spectral_gap": "normalized_laplacian_spectral_gap",
    "normalized_algebraic_connectivity": "normalized_laplacian_spectral_gap",
    "normalized_laplacian_spectral_gap": "normalized_laplacian_spectral_gap",
    "normalized_laplacian_gap": "normalized_laplacian_spectral_gap",
    "normalized_laplacian_spectral_radius": "normalized_laplacian_spectral_radius",
    "normalized_laplacian_radius": "normalized_laplacian_spectral_radius",
    "lambda_max_norm": "normalized_laplacian_spectral_radius",
    "normalized_laplacian_spectrum": "normalized_laplacian_spectrum",
    # Estrada Index
    "estrada": "estrada_index",
    "estrada_index": "estrada_index",
    "EE": "estrada_index",
    # Graph Energy
    "energy": "graph_energy",
    "graph_energy": "graph_energy",
    "E_G": "graph_energy",
    # Spectral Spread
    "spectral_spread": "spectral_spread",
    "spread": "spectral_spread",
    "s": "spectral_spread",
    # Complement & Nordhaus-Gaddum
    "comp_spectral_radius": "complement_spectral_radius",
    "complement_spectral_radius": "complement_spectral_radius",
    "lambda_1_comp": "complement_spectral_radius",
    "nordhaus_gaddum_spectral_sum": "nordhaus_gaddum_spectral_sum",
    "ng_spectral_sum": "nordhaus_gaddum_spectral_sum",
    "nordhaus_gaddum_spectral_product": "nordhaus_gaddum_spectral_product",
    "ng_spectral_product": "nordhaus_gaddum_spectral_product",
    # Exact SMT Invariants
    "chi": "chromatic_number",
    "chromatic_number": "chromatic_number",
    "omega": "clique_number",
    "clique_number": "clique_number",
    "alpha": "independence_number",
    "independence_number": "independence_number",
    "parity_code_distance": "parity_code_distance",
    "parity_code_dimension": "parity_code_dimension",
    "unique_neighbor_radius": "unique_neighbor_radius",
    # Predicates
    "is_bipartite": "is_bipartite",
    "is_triangle_free": "is_triangle_free",
    "is_regular": "is_regular",
    "is_connected": "is_connected",
    "is_tree": "is_tree",
    "is_forest": "is_forest",
    "is_planar": "is_planar",
    "is_empty": "is_empty",
    "is_complete": "is_complete",
    "is_chordal": "is_chordal",
    "is_eulerian": "is_eulerian",
}

INVARIANT_CALLABLES: Dict[str, Callable[..., Any]] = {
    "parity_code_distance": compute_parity_code_distance,
    "parity_code_dimension": compute_parity_code_dimension,
    "unique_neighbor_radius": compute_unique_neighbor_radius,
    "order": compute_order,
    "size": compute_size,
    "max_degree": compute_max_degree,
    "min_degree": compute_min_degree,
    "average_degree": compute_average_degree,
    "density": compute_density,
    "triangle_count": compute_triangle_count,
    "girth": compute_girth,
    "diameter": compute_diameter,
    "radius": compute_radius,
    "spectral_radius": compute_spectral_radius,
    "smallest_adjacency_eigenvalue": compute_smallest_adjacency_eigenvalue,
    "adjacency_spectrum": compute_adjacency_spectrum,
    "algebraic_connectivity": compute_algebraic_connectivity,
    "laplacian_spectral_radius": compute_laplacian_spectral_radius,
    "laplacian_spectrum": compute_laplacian_spectrum,
    "hoffman_bound": compute_hoffman_bound,
    "wilf_bound": compute_wilf_bound,
    "signless_laplacian_spectral_radius": compute_signless_laplacian_spectral_radius,
    "signless_laplacian_spectrum": compute_signless_laplacian_spectrum,
    "normalized_laplacian_spectral_gap": compute_normalized_laplacian_spectral_gap,
    "normalized_laplacian_spectral_radius": compute_normalized_laplacian_spectral_radius,
    "normalized_laplacian_spectrum": compute_normalized_laplacian_spectrum,
    "estrada_index": compute_estrada_index,
    "graph_energy": compute_graph_energy,
    "spectral_spread": compute_spectral_spread,
    "complement_spectral_radius": compute_complement_spectral_radius,
    "nordhaus_gaddum_spectral_sum": compute_nordhaus_gaddum_spectral_sum,
    "nordhaus_gaddum_spectral_product": compute_nordhaus_gaddum_spectral_product,
    "chromatic_number": compute_chromatic_number,
    "clique_number": compute_clique_number,
    "independence_number": compute_independence_number,
    "is_bipartite": is_bipartite,
    "is_triangle_free": is_triangle_free,
    "is_regular": is_regular,
    "is_connected": is_connected,
    "is_tree": is_tree,
    "is_forest": is_forest,
    "is_planar": is_planar,
    "is_empty": is_empty,
    "is_complete": is_complete,
    "is_chordal": is_chordal,
    "is_eulerian": is_eulerian,
}

STANDARD_SCALAR_INVARIANTS = [
    "order",
    "size",
    "max_degree",
    "min_degree",
    "average_degree",
    "density",
    "triangle_count",
    "girth",
    "diameter",
    "radius",
    "spectral_radius",
    "smallest_adjacency_eigenvalue",
    "spectral_spread",
    "algebraic_connectivity",
    "laplacian_spectral_radius",
    "hoffman_bound",
    "wilf_bound",
    "chromatic_number",
    "clique_number",
    "independence_number",
    "signless_laplacian_spectral_radius",
    "normalized_laplacian_spectral_gap",
    "estrada_index",
    "graph_energy",
    "complement_spectral_radius",
    "nordhaus_gaddum_spectral_sum",
]


class GraphInvariantEvaluator:
    """Unified invariant evaluator and cache manager conforming to pipeline contracts."""

    @classmethod
    def normalize_name(cls, name: str) -> str:
        """Resolve invariant aliases to canonical names."""
        canonical = INVARIANT_ALIASES.get(name)
        if canonical is None:
            raise KeyError(f"Unknown invariant or predicate: '{name}'")
        return canonical

    @classmethod
    def evaluate_single(
        cls,
        G: GraphLike,
        name: str,
        timeout_ms: int = 5000,
    ) -> Any:
        """Evaluate a single invariant or predicate with caching."""
        inst = _to_graph_instance(G)
        canon_name = cls.normalize_name(name)

        if inst.has_invariant(canon_name):
            return inst.get_invariant(canon_name)

        fn = INVARIANT_CALLABLES[canon_name]
        if canon_name in ("chromatic_number", "clique_number", "independence_number"):
            val = fn(inst, timeout_ms=timeout_ms)
        else:
            val = fn(inst)

        inst.set_invariant(canon_name, val)
        return val

    @classmethod
    def evaluate(
        cls,
        G: GraphLike,
        invariants: Optional[List[str]] = None,
        timeout_ms: int = 5000,
    ) -> Dict[str, Union[int, float, bool]]:
        """Batch evaluate invariants on G.

        Populates results under both requested and canonical names.
        If invariants is None, computes standard scalars.
        """
        inst = _to_graph_instance(G)
        inv_list = invariants if invariants is not None else STANDARD_SCALAR_INVARIANTS

        results: Dict[str, Union[int, float, bool]] = {}
        for raw_name in inv_list:
            canon_name = cls.normalize_name(raw_name)
            val = cls.evaluate_single(inst, canon_name, timeout_ms=timeout_ms)
            results[raw_name] = val
            results[canon_name] = val
        return results
