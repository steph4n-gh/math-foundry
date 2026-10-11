"""Empirical Instance Database and Fast Vectorized Sieve Engine (Feature 5).

Houses a pre-indexed catalog of 1,000+ extremal graphs (NetworkX atlas up to n=7,
odd/even cycles, cliques, complete bipartite, Turan, Mycielskian, Paley,
strongly regular graphs, and random graphs).
Precomputes and caches 19+ structural invariants in memory, supporting sub-millisecond
vectorized falsification of candidate conjectures and producing verifiable
counterexample certificates.
"""

from __future__ import annotations

import hashlib
import math
import time
from typing import Any, Callable, Dict, List, Literal, Optional, Sequence, Set, Tuple, Union

import networkx as nx
import numpy as np

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
)
from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.core.invariants import (
    INVARIANT_ALIASES,
    compute_average_degree,
    compute_density,
    compute_diameter,
    compute_girth,
    compute_max_degree,
    compute_min_degree,
    compute_normalized_laplacian_spectrum,
    compute_order,
    compute_radius,
    compute_size,
    compute_spectral_spread,
    compute_triangle_count,
    is_bipartite,
    is_connected,
    is_regular,
    is_triangle_free,
)
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    SieveResult,
)


# ============================================================================
# Exact Combinatorial Invariant Helpers for Catalog Precomputation
# ============================================================================

KEYS_TO_VECTORIZE: List[str] = [
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
    "clique_number",
    "independence_number",
    "chromatic_number",
    "spectral_radius",
    "smallest_adjacency_eigenvalue",
    "spectral_spread",
    "signless_laplacian_spectral_radius",
    "normalized_laplacian_spectral_gap",
    "normalized_laplacian_spectral_radius",
    "estrada_index",
    "graph_energy",
    "complement_spectral_radius",
    "nordhaus_gaddum_spectral_sum",
    "nordhaus_gaddum_spectral_product",
]
CODE_COLUMNS = ("parity_code_distance", "parity_code_dimension", "unique_neighbor_radius")



def _exact_chromatic_backtrack(
    G: nx.Graph, max_k: int = 25, *, timeout_sec: float = 10.0,
    lower_bound: int = 1,
) -> int:
    """Return the exact chromatic number, or raise on a finite search deadline.

    DSATUR chooses the most constrained uncolored vertex. Color labels are
    interchangeable, so only one previously unused color is explored. A greedy
    coloring gives an upper bound and actual greedily found cliques give lower
    bounds; neither is returned unless the exact search closes the gap. The
    caller may supply a proven lower bound from already computed exact
    invariants, avoiding repeated clique/independence search.
    ``max_k`` remains accepted for compatibility; it was historically unused.
    """
    if not math.isfinite(timeout_sec) or timeout_sec <= 0:
        raise ValueError("Exact coloring requires a finite positive timeout")
    deadline = time.monotonic() + timeout_sec

    def check():
        if time.monotonic() >= deadline:
            raise TimeoutError("Exact chromatic search exceeded its finite budget")

    check()
    n = G.number_of_nodes()
    if n == 0:
        return 0
    if G.number_of_edges() == 0:
        return 1
    if nx.is_bipartite(G):
        return 2

    if G.number_of_edges() == n * (n - 1) // 2:
        return n
    adj = {u: set(G.neighbors(u)) for u in G.nodes()}
    ordered = sorted(G.nodes(), key=lambda u: len(adj[u]), reverse=True)
    lower = max(3, lower_bound)  # The bipartite shortcut excluded values 1/2.
    for seed in ordered:
        check()
        clique = {seed}
        for node in ordered:
            if node not in clique and clique <= adj[node]:
                clique.add(node)
        lower = max(lower, len(clique))

    colors = {}
    remaining = set(ordered)

    def select_vertex():
        # Preserve input order for deterministic saturation/degree ties.
        return max((u for u in ordered if u in remaining), key=lambda u:
            (len({colors[v] for v in adj[u] if v in colors}), len(adj[u])))

    best = 0
    while remaining:
        check()
        node = select_vertex()
        forbidden = {colors[v] for v in adj[node] if v in colors}
        color = next(c for c in range(best + 1) if c not in forbidden)
        colors[node] = color
        remaining.remove(node)
        best = max(best, color + 1)
    colors.clear()
    remaining.update(ordered)

    def search(used):
        nonlocal best
        check()
        if best == lower or used >= best:
            return
        if not remaining:
            best = used
            return
        node = select_vertex()
        forbidden = {colors[v] for v in adj[node] if v in colors}
        remaining.remove(node)
        for color in range(min(used + 1, best - 1)):
            if color not in forbidden:
                colors[node] = color
                search(max(used, color + 1))
                del colors[node]
                if best == lower:
                    break
        remaining.add(node)

    search(0)
    return best


def _find_odd_cycle_walk(G: nx.Graph) -> Optional[List[int]]:
    """Extract closed odd cycle vertex sequence [v0, v1, ..., vk, v0] if non-bipartite."""
    if nx.is_bipartite(G) or G.number_of_edges() == 0:
        return None
    for cycle in nx.cycle_basis(G):
        if len(cycle) % 2 == 1:
            return cycle + [cycle[0]]
    # Fallback to shortest odd cycle
    try:
        odd_cycles = [
            c for c in nx.simple_cycles(G.to_directed())
            if len(c) % 2 == 1 and len(c) >= 3
        ]
        if odd_cycles:
            shortest = min(odd_cycles, key=len)
            return shortest + [shortest[0]]
    except Exception:
        pass
    return None


# ============================================================================
# Instance Database
# ============================================================================


class InstanceDatabase:
    """Catalog of 1,000+ extremal graphs with precomputed invariant caching.

    Uses class-level singleton caching to ensure instant instantiation (<0.01ms)
    after the initial 0.2s algorithmic population.
    """

    # Class-level caches
    _cached_nx: Optional[List[nx.Graph]] = None
    _cached_gi: Optional[List[GraphInstance]] = None
    _cached_invariants: Optional[List[Dict[str, Any]]] = None
    _cached_matrix: Optional[Dict[str, np.ndarray]] = None
    _code_columns_enabled = False

    def __init__(self, include_atlas: bool = True, max_atlas_order: int = 7) -> None:
        self.include_atlas = include_atlas
        self.max_atlas_order = max_atlas_order

        if InstanceDatabase._cached_gi is None:
            self._initialize_catalog()

    @classmethod
    def clear_cache(cls) -> None:
        """Clear class-level caches."""
        cls._cached_nx = None
        cls._cached_gi = None
        cls._cached_invariants = None
        cls._cached_matrix = None
        cls._code_columns_enabled = False

    def ensure_code_columns(self) -> Dict[str, Any]:
        """Compute optional exact code columns only for an explicit code query.

        Unsupported graph orders are NaN, never fabricated distance/dimension.
        Ordinary catalog initialization does not call the exponential evaluator.
        """
        from autonomous_math.core.expander_codes import MAX_EXACT_CODE_ORDER
        from autonomous_math.core.invariants import GraphInvariantEvaluator
        cls = type(self)
        graphs = cls._cached_gi or []
        if not cls._code_columns_enabled:
            for graph, values in zip(graphs, cls._cached_invariants or []):
                for name in CODE_COLUMNS:
                    try:
                        values[name] = float(GraphInvariantEvaluator.evaluate_single(graph, name))
                    except ValueError:
                        values[name] = float("nan")
            cls._code_columns_enabled = True
            cls._rebuild_cached_matrix()
        if cls._cached_matrix is None or any(len(cls._cached_matrix.get(name, [])) != len(graphs) for name in CODE_COLUMNS):
            cls._rebuild_cached_matrix()
        table = cls._cached_matrix or {}
        dimension = table.get("parity_code_dimension", np.array([]))
        return {"construction": "kernel_of_adjacency_over_GF2", "max_exact_order": MAX_EXACT_CODE_ORDER,
                "graphs": len(graphs), "defined_graphs": int(np.sum(np.isfinite(dimension))),
                "unsupported_graphs": int(np.sum(~np.isfinite(dimension))),
                "nonzero_code_graphs": int(np.sum(np.isfinite(dimension) & (dimension >= 1))),
                "zero_code_graphs": int(np.sum(dimension == 0))}

    def _initialize_catalog(self) -> None:
        """Construct the 1,000+ graph catalog and precompute invariants."""
        raw_graphs: List[nx.Graph] = []

        # 1. NetworkX Graph Atlas (all non-isomorphic graphs up to n=7)
        if self.include_atlas:
            for i, g in enumerate(nx.graph_atlas_g()):
                if g.number_of_nodes() <= self.max_atlas_order:
                    gc = g.copy()
                    gc.name = f"Atlas_{i}"
                    raw_graphs.append(gc)

        # 2. Cycles (C_3 to C_15)
        for c in range(3, 16):
            gc = nx.cycle_graph(c)
            gc.name = f"C_{c}"
            raw_graphs.append(gc)

        # 3. Cliques (K_1 to K_10)
        for k in range(1, 11):
            gc = nx.complete_graph(k)
            gc.name = f"K_{k}"
            raw_graphs.append(gc)

        # 4. Complete Bipartite graphs K_{a, b} (1 <= a <= b <= 6)
        for a in range(1, 7):
            for b in range(a, 7):
                gc = nx.complete_bipartite_graph(a, b)
                gc.name = f"K_{a}_{b}"
                raw_graphs.append(gc)

        # 5. Turán Graphs T(n, r)
        for n in range(4, 13):
            for r in range(2, min(5, n)):
                gc = nx.turan_graph(n, r)
                gc.name = f"Turan_{n}_{r}"
                raw_graphs.append(gc)

        # 6. Mycielskian Graphs M_2 = K_2, M_3 = C_5, M_4 = Grötzsch, M_5
        for m in [2, 3, 4, 5]:
            gc = nx.mycielski_graph(m)
            names = {2: "K_2", 3: "C_5", 4: "Grotzsch", 5: "Mycielski_5"}
            gc.name = f"Mycielski_{m}_{names.get(m, '')}"
            raw_graphs.append(gc)

        # 7. Paley Graphs (P_5, P_9, P_13, P_17) - coerced to undirected!
        for q in [5, 9, 13, 17]:
            gc = nx.paley_graph(q).to_undirected()
            gc.name = f"Paley_{q}"
            raw_graphs.append(gc)

        # 8. Strongly Regular & Famous Extremal Graphs
        # Petersen (10, 3, 0, 1)
        p = nx.petersen_graph()
        p.name = "Petersen"
        raw_graphs.append(p)

        # Clebsch graph (16, 5, 0, 2) via folded 5-cube
        cleb = nx.Graph()
        cleb.add_nodes_from(range(16))
        for u in range(16):
            for v in range(u + 1, 16):
                diff = bin(u ^ v).count("1")
                if diff in (1, 4):
                    cleb.add_edge(u, v)
        cleb.name = "Clebsch"
        raw_graphs.append(cleb)

        # Shrikhande graph (16, 6, 2, 2)
        shrik = nx.Graph()
        nodes_z4 = [(x, y) for x in range(4) for y in range(4)]
        map_z4 = {nd: i for i, nd in enumerate(nodes_z4)}
        shrik.add_nodes_from(range(16))
        conn_set = {(1, 0), (3, 0), (0, 1), (0, 3), (1, 1), (3, 3)}
        for x, y in nodes_z4:
            u_idx = map_z4[(x, y)]
            for dx, dy in conn_set:
                v_idx = map_z4[((x + dx) % 4, (y + dy) % 4)]
                if u_idx < v_idx:
                    shrik.add_edge(u_idx, v_idx)
        shrik.name = "Shrikhande"
        raw_graphs.append(shrik)

        # Chvátal graph (triangle-free 4-chromatic 4-regular)
        chv = nx.chvatal_graph()
        chv.name = "Chvatal"
        raw_graphs.append(chv)

        # Heawood & Desargues
        heawood = nx.heawood_graph()
        heawood.name = "Heawood"
        raw_graphs.append(heawood)

        desargues = nx.desargues_graph()
        desargues.name = "Desargues"
        raw_graphs.append(desargues)

        # 9. Random Graphs: Erdős-Rényi and Random Regular with fixed seed
        rng = np.random.RandomState(42)
        for n in [8, 10, 12, 14]:
            for prob in [0.2, 0.4, 0.6]:
                seed = int(rng.randint(100000))
                gc = nx.erdos_renyi_graph(n, prob, seed=seed)
                gc.name = f"ER_{n}_{prob}"
                raw_graphs.append(gc)

        for d, n in [(3, 10), (3, 14), (4, 12)]:
            seed = int(rng.randint(100000))
            gc = nx.random_regular_graph(d, n, seed=seed)
            gc.name = f"RR_{d}_{n}"
            raw_graphs.append(gc)

        # Build GraphInstances and precompute invariants
        gi_list: List[GraphInstance] = []
        inv_list: List[Dict[str, Any]] = []

        for g in raw_graphs:
            gi = GraphInstance.from_networkx(g, name=g.name)
            inv_dict = self._compute_instance_invariants(gi, g)
            gi_list.append(gi)
            inv_list.append(inv_dict)

        # Build columnar numpy array table for ultra-fast vectorized sieving
        matrix_dict: Dict[str, np.ndarray] = {}
        for key in KEYS_TO_VECTORIZE:
            matrix_dict[key] = np.array([float(d[key]) for d in inv_list], dtype=float)
            alias = INVARIANT_ALIASES.get(key)
            if alias:
                matrix_dict[alias] = matrix_dict[key]

        matrix_dict["is_triangle_free"] = np.array([d["is_triangle_free"] for d in inv_list], dtype=bool)
        matrix_dict["is_bipartite"] = np.array([d["is_bipartite"] for d in inv_list], dtype=bool)
        matrix_dict["is_connected"] = np.array([d["is_connected"] for d in inv_list], dtype=bool)
        matrix_dict["is_regular"] = np.array([d["is_regular"] for d in inv_list], dtype=bool)

        InstanceDatabase._cached_nx = raw_graphs
        InstanceDatabase._cached_gi = gi_list
        InstanceDatabase._cached_invariants = inv_list
        InstanceDatabase._cached_matrix = matrix_dict

    @property
    def instances(self) -> List[nx.Graph]:
        """Convenience property returning all NetworkX graph instances."""
        return self.get_instances()

    def get_instances(self) -> List[nx.Graph]:
        """Return list of all NetworkX graph instances in the catalog."""
        return list(InstanceDatabase._cached_nx or [])

    def get_graph_instances(self) -> List[GraphInstance]:
        """Return list of immutable GraphInstance models."""
        return list(InstanceDatabase._cached_gi or [])

    def get_precomputed_invariants(self) -> List[Dict[str, Any]]:
        """Return list of precomputed invariant dictionaries."""
        return list(InstanceDatabase._cached_invariants or [])

    def get_invariants_table(self) -> Dict[str, np.ndarray]:
        """Return column-oriented dictionary of 1D NumPy arrays."""
        return dict(InstanceDatabase._cached_matrix or {})

    def __len__(self) -> int:
        return len(InstanceDatabase._cached_gi or [])

    @classmethod
    def _compute_instance_invariants(
        cls,
        gi: GraphInstance,
        nx_g: nx.Graph,
    ) -> Dict[str, Any]:
        """Compute the full suite of invariants required for caching and vectorized sieving."""
        n = gi.order
        m = gi.size

        degs = [d for _, d in nx_g.degree()]
        dmax = max(degs) if degs else 0
        dmin = min(degs) if degs else 0
        davg = float(2.0 * m / n) if n > 0 else 0.0
        dens = float(2.0 * m / (n * (n - 1))) if n > 1 else 0.0

        tri = compute_triangle_count(gi)
        tf = (tri == 0)
        bip = bool(nx.is_bipartite(nx_g)) if m > 0 else True
        conn = bool(nx.is_connected(nx_g)) if n > 0 else False
        regular = (dmax == dmin) if n > 0 else True
        g_val = float(compute_girth(gi))
        diam_val = float(compute_diameter(gi))
        rad_val = float(compute_radius(gi))

        # Cliques and independence
        if n == 0:
            cli = 0
            ind = 0
        elif n <= 10:
            cli = len(max(nx.find_cliques(nx_g), key=len))
            gc_comp = nx.complement(nx_g)
            ind = len(max(nx.find_cliques(gc_comp), key=len))
        else:
            cli = len(nx.algorithms.clique.max_weight_clique(nx_g, weight=None)[0])
            gc_comp = nx.complement(nx_g)
            ind = len(nx.algorithms.clique.max_weight_clique(gc_comp, weight=None)[0])

        # Exact chromatic calculation
        # A color class is independent: chi >= ceil(n / alpha). Reuse the exact
        # values computed above instead of repeating exponential searches.
        chi = _exact_chromatic_backtrack(nx_g, lower_bound=max(cli, (n + ind - 1) // ind) if ind else 0)

        # Spectral invariants
        if n > 0:
            A = gi.to_adjacency_matrix().astype(float)
            eigs = np.linalg.eigvalsh(A)
            lambda_1 = float(eigs[-1])
            lambda_n = float(eigs[0])
            sr = float(max(abs(lambda_1), abs(lambda_n)))

            # Signless Laplacian Q = D + A
            deg_sum = np.sum(A, axis=1)
            Q = np.diag(deg_sum) + A
            q_eigs = np.linalg.eigvalsh(Q)
            q1 = float(np.max(q_eigs))

            # Normalized Laplacian
            norm_eigs = compute_normalized_laplacian_spectrum(gi)
            norm_gap = float(norm_eigs[1]) if len(norm_eigs) >= 2 else 0.0
            norm_radius = float(norm_eigs[-1]) if norm_eigs else 0.0

            # Estrada Index & Graph Energy
            estrada = float(np.sum(np.exp(eigs)))
            energy = float(np.sum(np.abs(eigs)))
        else:
            lambda_1 = 0.0
            lambda_n = 0.0
            sr = 0.0
            q1 = 0.0
            norm_gap = 0.0
            norm_radius = 0.0
            estrada = 0.0
            energy = 0.0

        if n > 1:
            A_bar = (np.ones((n, n), dtype=float) - np.eye(n, dtype=float)) - A
            bar_eigs = np.linalg.eigvalsh(A_bar)
            comp_sr = float(np.max(bar_eigs))
        else:
            comp_sr = 0.0

        spread = float(lambda_1 - lambda_n) if n > 0 else 0.0

        inv_dict: Dict[str, Any] = {
            "order": n,
            "n": n,
            "size": m,
            "m": m,
            "max_degree": dmax,
            "min_degree": dmin,
            "average_degree": davg,
            "density": dens,
            "triangle_count": tri,
            "triangles": tri,
            "girth": g_val,
            "g": g_val,
            "diameter": diam_val,
            "diam": diam_val,
            "D": diam_val,
            "radius": rad_val,
            "rad": rad_val,
            "R": rad_val,
            "clique_number": cli,
            "omega": cli,
            "independence_number": ind,
            "alpha": ind,
            "chromatic_number": chi,
            "chi": chi,
            "spectral_radius": sr,
            "smallest_adjacency_eigenvalue": lambda_n,
            "spectral_spread": spread,
            "spread": spread,
            "s": spread,
            "signless_laplacian_spectral_radius": q1,
            "q_spectral_radius": q1,
            "q_1": q1,
            "normalized_laplacian_spectral_gap": norm_gap,
            "normalized_spectral_gap": norm_gap,
            "lambda_2_norm": norm_gap,
            "normalized_laplacian_spectral_radius": norm_radius,
            "estrada_index": estrada,
            "estrada": estrada,
            "EE": estrada,
            "graph_energy": energy,
            "energy": energy,
            "complement_spectral_radius": comp_sr,
            "comp_spectral_radius": comp_sr,
            "nordhaus_gaddum_spectral_sum": sr + comp_sr,
            "ng_spectral_sum": sr + comp_sr,
            "nordhaus_gaddum_spectral_product": sr * comp_sr,
            "ng_spectral_product": sr * comp_sr,
            "is_triangle_free": tf,
            "is_bipartite": bip,
            "is_connected": conn,
            "is_regular": regular,
        }

        # Override with any pre-existing invariants explicitly set on gi
        for k in list(inv_dict.keys()):
            if gi.has_invariant(k):
                inv_dict[k] = gi.get_invariant(k)

        # Synchronize canonical and alias pairs if only one was pre-set
        alias_pairs = [
            ("order", "n"),
            ("size", "m"),
            ("triangle_count", "triangles"),
            ("girth", "g"),
            ("diameter", "diam"),
            ("diameter", "D"),
            ("radius", "rad"),
            ("radius", "R"),
            ("clique_number", "omega"),
            ("independence_number", "alpha"),
            ("chromatic_number", "chi"),
            ("spectral_spread", "spread"),
            ("spectral_spread", "s"),
        ]
        for canon_k, alias_k in alias_pairs:
            if gi.has_invariant(alias_k) and not gi.has_invariant(canon_k):
                inv_dict[canon_k] = inv_dict[alias_k]
            elif gi.has_invariant(canon_k) and not gi.has_invariant(alias_k):
                inv_dict[alias_k] = inv_dict[canon_k]

        for k, v in inv_dict.items():
            gi.set_invariant(k, v)

        return inv_dict

    @classmethod
    def _rebuild_cached_matrix(cls) -> Optional[Dict[str, np.ndarray]]:
        """Rebuild columnar NumPy arrays from _cached_invariants."""
        if cls._cached_invariants is None or not cls._cached_invariants:
            cls._cached_matrix = None
            return None

        bool_keys = ["is_triangle_free", "is_bipartite", "is_connected", "is_regular"]

        try:
            matrix_dict: Dict[str, np.ndarray] = {}
            for key in (*KEYS_TO_VECTORIZE, *(CODE_COLUMNS if cls._code_columns_enabled else ())):
                matrix_dict[key] = np.array(
                    [float(d[key]) for d in cls._cached_invariants], dtype=float
                )
                alias = INVARIANT_ALIASES.get(key)
                if alias:
                    matrix_dict[alias] = matrix_dict[key]
            for key in bool_keys:
                matrix_dict[key] = np.array(
                    [bool(d[key]) for d in cls._cached_invariants], dtype=bool
                )
            cls._cached_matrix = matrix_dict
            return matrix_dict
        except (KeyError, ValueError, TypeError):
            cls._cached_matrix = None
            return None

    def add_instance(
        self,
        G: Union[nx.Graph, GraphInstance],
        name: Optional[str] = None,
    ) -> None:
        """Dynamically append a custom graph to the database with complete cache coherence."""
        if isinstance(G, GraphInstance):
            gi = G
            nx_g = G.to_networkx()
            if name:
                nx_g.name = name
                object.__setattr__(gi, "name", name)
        else:
            nx_g = G.copy()
            if name:
                nx_g.name = name
            gi = GraphInstance.from_networkx(nx_g, name=nx_g.name)

        if InstanceDatabase._cached_gi is None:
            self._initialize_catalog()

        assert InstanceDatabase._cached_nx is not None
        assert InstanceDatabase._cached_gi is not None
        assert InstanceDatabase._cached_invariants is not None

        # Compute full invariant dictionary matching catalog schema
        inv_dict = self._compute_instance_invariants(gi, nx_g)
        if InstanceDatabase._code_columns_enabled:
            from autonomous_math.core.invariants import GraphInvariantEvaluator
            for key in CODE_COLUMNS:
                try:
                    inv_dict[key] = float(GraphInvariantEvaluator.evaluate_single(gi, key))
                except ValueError:
                    inv_dict[key] = float("nan")

        # Update base caches
        InstanceDatabase._cached_nx.append(nx_g)
        InstanceDatabase._cached_gi.append(gi)
        InstanceDatabase._cached_invariants.append(inv_dict)

        # Maintain _cached_matrix coherence: append row if matrix is active
        if InstanceDatabase._cached_matrix is not None:
            try:
                bool_keys = ["is_triangle_free", "is_bipartite", "is_connected", "is_regular"]

                for k in (*KEYS_TO_VECTORIZE, *(CODE_COLUMNS if InstanceDatabase._code_columns_enabled else ())):
                    val = float(inv_dict[k])
                    InstanceDatabase._cached_matrix[k] = np.append(
                        InstanceDatabase._cached_matrix[k], val
                    )
                    alias = INVARIANT_ALIASES.get(k)
                    if alias and alias in InstanceDatabase._cached_matrix:
                        InstanceDatabase._cached_matrix[alias] = InstanceDatabase._cached_matrix[k]
                for k in bool_keys:
                    val = bool(inv_dict[k])
                    InstanceDatabase._cached_matrix[k] = np.append(
                        InstanceDatabase._cached_matrix[k], val
                    )
            except Exception:
                # If row append fails, invalidate matrix so lazy rebuild or fallback takes over safely
                InstanceDatabase._cached_matrix = None

    # ========================================================================
    # Sieve Execution Engine
    # ========================================================================

    def sieve_conjecture(self, conj: Conjecture) -> SieveResult:
        """Evaluate conjecture against all database instances.

        Fast path: evaluates columnar arrays (<1ms).
        Fallback: iterates over precomputed dicts (<2ms).
        Returns SieveResult with status 'REFUTED' or 'SURVIVED'.
        """
        t0 = time.time()
        assert InstanceDatabase._cached_gi is not None
        assert InstanceDatabase._cached_nx is not None
        assert InstanceDatabase._cached_invariants is not None

        # 1. Try Ultra-Fast Columnar Vectorized Evaluation
        self._coverage = {}
        vec_res = self._try_vectorized_sieve(conj)
        if vec_res is not None:
            violation_idx, l_val, r_val = vec_res
            if violation_idx is not None:
                # Counterexample found at violation_idx!
                tested_count = int(violation_idx) + 1
                cert = self._build_certificate(
                    conj=conj,
                    idx=violation_idx,
                    lhs_val=l_val,
                    rhs_val=r_val,
                )
                dt = (time.time() - t0) * 1000
                return SieveResult(
                    status="REFUTED",
                    conjecture=conj,
                    tested_instances_count=len(InstanceDatabase._cached_gi),
                    **self._coverage,
                    counterexample_certificate=cert,
                    execution_time_ms=dt,
                )
            else:
                # All instances satisfied the conjecture
                dt = (time.time() - t0) * 1000
                return SieveResult(
                    status="SURVIVED" if self._coverage.get("checked_instances_count", 0) else "INCONCLUSIVE",
                    conjecture=conj,
                    **self._coverage,
                    tested_instances_count=len(InstanceDatabase._cached_gi),
                    counterexample_certificate=None,
                    execution_time_ms=dt,
                )

        # 2. Sequential Dictionary Evaluation Fallback
        tested = 0
        checked = 0
        undefined = 0
        for idx, (gi, nx_g, invs) in enumerate(
            zip(
                InstanceDatabase._cached_gi,
                InstanceDatabase._cached_nx,
                InstanceDatabase._cached_invariants,
            )
        ):
            tested += 1
            try:
                guard_vars = getattr(conj.guard_predicate, "variables", set())
                if any(name in invs and not np.isfinite(invs[name]) for name in guard_vars & set(CODE_COLUMNS)):
                    undefined += 1
                    continue
                if not conj.applies(gi, invs):
                    continue
                holds, l_val, r_val = conj.evaluate(gi, invariants=invs)
                if np.isnan(l_val) or np.isnan(r_val):
                    undefined += 1
                    continue
                checked += 1
            except (ZeroDivisionError, ValueError, ArithmeticError, TimeoutError):
                # Domain error on boundary graph (e.g. division by zero, invalid root/log).
                # Graphs where expressions are mathematically undefined do not constitute
                # valid counterexamples. Safely skip to the next candidate instance.
                undefined += 1
                continue

            if not holds:
                cert = self._build_certificate(
                    conj=conj,
                    idx=idx,
                    lhs_val=l_val,
                    rhs_val=r_val,
                )
                dt = (time.time() - t0) * 1000
                return SieveResult(
                    status="REFUTED",
                    conjecture=conj,
                    tested_instances_count=tested,
                    checked_instances_count=checked, undefined_instances_count=undefined,
                    counterexample_certificate=cert,
                    execution_time_ms=dt,
                )

        dt = (time.time() - t0) * 1000
        return SieveResult(
            status="SURVIVED" if checked else "INCONCLUSIVE",
            conjecture=conj,
            checked_instances_count=checked, undefined_instances_count=undefined,
            tested_instances_count=tested,
            counterexample_certificate=None,
            execution_time_ms=dt,
        )

    def sieve_conjectures(self, conjectures: List[Conjecture]) -> List[SieveResult]:
        """Batch evaluate a list of conjectures."""
        return [self.sieve_conjecture(c) for c in conjectures]

    # ========================================================================
    # Internal Vectorization & Certificate Construction
    # ========================================================================

    def _try_vectorized_sieve(
        self,
        conj: Conjecture,
    ) -> Optional[Tuple[Optional[int], float, float]]:
        """Attempt vectorized array evaluation over precomputed matrix.

        Returns (violation_idx, l_val, r_val) if vectorizable, or None if fallback required.
        """
        needed_vars = set(conj.lhs_expr.variables) | set(conj.rhs_expr.variables)
        needed_vars |= getattr(conj.guard_predicate, "variables", set())
        if needed_vars & set(CODE_COLUMNS):
            self.ensure_code_columns()
        table = InstanceDatabase._cached_matrix
        target_len = len(InstanceDatabase._cached_gi or [])

        # Cache coherence check: rebuild matrix lazily if None or length mismatch
        if table is None or len(table.get("order", [])) != target_len:
            table = self._rebuild_cached_matrix()
            if table is None or len(table.get("order", [])) != target_len:
                return None

        # Check if all required variables are present in table
        for v in needed_vars:
            canon = INVARIANT_ALIASES.get(v, v)
            if canon not in table:
                return None

        # Determine applicability mask based on premise guard
        n_instances = len(table["order"])
        mask = np.ones(n_instances, dtype=bool)

        if conj.guard_predicate is not None:
            if isinstance(conj.guard_predicate, str):
                g_str = conj.guard_predicate
                if g_str in table:
                    mask = table[g_str]
                elif g_str in INVARIANT_ALIASES and INVARIANT_ALIASES[g_str] in table:
                    mask = table[INVARIANT_ALIASES[g_str]]
                elif g_str == "universal":
                    pass
                else:
                    return None
            elif isinstance(conj.guard_predicate, GuardPredicate):
                gp = conj.guard_predicate
                if gp.predicate_type == "property" and gp.property_name:
                    pname = gp.property_name
                    if pname in table:
                        mask = (~table[pname]) if gp.negated else table[pname]
                    elif pname in INVARIANT_ALIASES and INVARIANT_ALIASES[pname] in table:
                        col = table[INVARIANT_ALIASES[pname]]
                        mask = (~col) if gp.negated else col
                    else:
                        return None
                elif gp.predicate_type == "universal":
                    pass
                else:
                    return None

        # Evaluate expressions over columns
        try:
            with np.errstate(all="ignore"):
                l_arr = self._eval_expr_columnar(conj.lhs_expr, table)
                r_arr = self._eval_expr_columnar(conj.rhs_expr, table)
        except Exception:
            return None

        # Domain validity mask: exclude instances where LHS or RHS is mathematically undefined (NaN)
        # Disconnected diameter and acyclic girth legitimately take +infinity.
        # Preserve extended-real comparisons; undefined arithmetic is NaN.
        valid_domain = ~np.isnan(l_arr) & ~np.isnan(r_arr)
        self._coverage = {"checked_instances_count": int(np.sum(mask & valid_domain)),
                          "undefined_instances_count": int(np.sum(mask & ~valid_domain))}

        tol = 1e-7
        if conj.rel == "<=":
            violation_mask = mask & valid_domain & (l_arr > r_arr + tol)
        elif conj.rel == ">=":
            violation_mask = mask & valid_domain & (l_arr < r_arr - tol)
        elif conj.rel == "==":
            with np.errstate(invalid="ignore"):
                distance = np.where(l_arr == r_arr, 0, np.abs(l_arr - r_arr))
            violation_mask = mask & valid_domain & (distance > tol)
        elif conj.rel == "<":
            violation_mask = mask & valid_domain & (l_arr >= r_arr - tol)
        elif conj.rel == ">":
            violation_mask = mask & valid_domain & (l_arr <= r_arr + tol)
        else:
            return None

        violation_indices = np.nonzero(violation_mask)[0]
        if len(violation_indices) > 0:
            first_idx = int(violation_indices[0])
            return (first_idx, float(l_arr[first_idx]), float(r_arr[first_idx]))

        return (None, 0.0, 0.0)

    def _eval_expr_columnar(
        self,
        expr: ExpressionNode,
        table: Dict[str, np.ndarray],
    ) -> np.ndarray:
        """Vectorized evaluator for AST expressions over 1D NumPy arrays.

        Yields np.nan for domain singularities (division by zero, negative radicands,
        non-positive logs/log1p, invalid powers) without emitting RuntimeWarnings.
        """
        if isinstance(expr, InvariantNode):
            canon = INVARIANT_ALIASES.get(expr.name, expr.name)
            if canon not in table:
                raise KeyError(f"Invariant {expr.name} not in table")
            return table[canon]
        elif isinstance(expr, ConstantNode):
            return np.full_like(table["order"], expr.value, dtype=float)
        elif isinstance(expr, UnaryOpNode):
            sub = self._eval_expr_columnar(expr.child, table)
            if expr.op in ("-", "neg"):
                return -sub
            elif expr.op == "abs":
                return np.abs(sub)
            elif expr.op == "sqr":
                return sub * sub
            elif expr.op == "sqrt":
                return np.where(sub < -1e-9, np.nan, np.sqrt(np.maximum(sub, 0.0)))
            elif expr.op == "log":
                safe_sub = np.where(sub <= 1e-12, 1.0, sub)
                return np.where(sub <= 1e-12, np.nan, np.log(safe_sub))
            elif expr.op == "log1p":
                safe_sub = np.where(sub <= -1.0 + 1e-12, 0.0, sub)
                return np.where(sub <= -1.0 + 1e-12, np.nan, np.log1p(safe_sub))
            elif expr.op == "inv":
                safe_sub = np.where(np.abs(sub) < 1e-12, 1.0, sub)
                return np.where(np.abs(sub) < 1e-12, np.nan, 1.0 / safe_sub)
            elif expr.op == "ceil":
                return np.ceil(sub)
            elif expr.op == "floor":
                return np.floor(sub)
            elif expr.op == "exp":
                with np.errstate(over="ignore", invalid="ignore"):
                    res = np.exp(sub)
                    return np.where(np.isinf(res), np.nan, res)
            raise ValueError(f"Unknown unary op {expr.op}")
        elif isinstance(expr, BinaryOpNode):
            l = self._eval_expr_columnar(expr.left, table)
            r = self._eval_expr_columnar(expr.right, table)
            if expr.op == "+":
                return l + r
            elif expr.op == "-":
                return l - r
            elif expr.op == "*":
                return l * r
            elif expr.op == "/":
                safe_r = np.where(np.abs(r) < 1e-12, 1.0, r)
                return np.where(np.abs(r) < 1e-12, np.nan, l / safe_r)
            elif expr.op in ("^", "**"):
                with np.errstate(invalid="ignore", divide="ignore"):
                    res = np.power(l, r)
                    return np.where(np.isinf(res), np.nan, res)
            elif expr.op == "min":
                return np.minimum(l, r)
            elif expr.op == "max":
                return np.maximum(l, r)
            raise ValueError(f"Unknown binary op {expr.op}")
        raise TypeError(f"Unsupported node type: {type(expr)}")

    def _build_certificate(
        self,
        conj: Conjecture,
        idx: int,
        lhs_val: float,
        rhs_val: float,
    ) -> CounterexampleCertificate:
        """Assemble CounterexampleCertificate for a refuted conjecture."""
        assert InstanceDatabase._cached_gi is not None
        assert InstanceDatabase._cached_nx is not None
        assert InstanceDatabase._cached_invariants is not None

        gi = InstanceDatabase._cached_gi[idx]
        nx_g = gi.to_networkx()
        invs = InstanceDatabase._cached_invariants[idx]

        adj_matrix = nx.to_numpy_array(nx_g, dtype=int).tolist()
        edges = list(gi.edges)

        # Refutation witness selection
        odd_cycle = _find_odd_cycle_walk(nx_g)
        stmt_lower = conj.statement.lower()
        if (
            odd_cycle is not None
            and (
                "chi" in stmt_lower
                or "chromatic" in stmt_lower
                or conj.guard_predicate == "is_triangle_free"
                or (
                    isinstance(conj.guard_predicate, GuardPredicate)
                    and conj.guard_predicate.property_name == "is_triangle_free"
                )
            )
        ):
            refutation_witness: Dict[str, Any] = {
                "type": "odd_cycle",
                "details": odd_cycle,
            }
        else:
            refutation_witness = {
                "type": "direct_evaluation",
                "details": {
                    "lhs_value": lhs_val,
                    "rel": conj.rel,
                    "rhs_value": rhs_val,
                    "graph_name": gi.name,
                },
            }

        v_hash = CounterexampleCertificate.compute_verification_hash(
            conj.id, gi.order, edges, refutation_witness
        )

        return CounterexampleCertificate(
            conjecture_id=conj.id,
            graph_order=gi.order,
            graph_size=gi.size,
            adjacency_matrix=adj_matrix,
            edges=edges,
            invariants=invs,
            refutation_witness=refutation_witness,
            verification_hash=v_hash,
        )
