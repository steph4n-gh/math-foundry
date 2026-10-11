"""Graph representation models, canonical forms, and conversion utilities.

Provides GraphInstance (and GraphWrapper) for immutable, hashable graph representations,
conversions between NetworkX, adjacency matrices, and edge lists,
plus invariant memoization and canonical factory constructors.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Sequence, Set, Tuple, Union

import networkx as nx
import numpy as np


@dataclass
class GraphInstance:
    """Canonical representation of a simple, undirected graph.

    Vertices are strictly 0-indexed integers {0, 1, ..., order - 1}.
    Edges are canonicalized pairs (u, v) with u < v, sorted in ascending order.
    """

    order: int
    edges: Tuple[Tuple[int, int], ...]
    name: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)

    # Internal caches
    _nx_cache: Optional[nx.Graph] = field(default=None, repr=False, compare=False)
    _adj_cache: Optional[np.ndarray] = field(default=None, repr=False, compare=False)
    _invariant_cache: Dict[str, Any] = field(default_factory=dict, repr=False, compare=False)

    def __post_init__(self) -> None:
        if self.order < 0:
            raise ValueError(f"Graph order cannot be negative, got {self.order}")

        canon_edges: Set[Tuple[int, int]] = set()
        for u, v in self.edges:
            if u == v:
                raise ValueError(f"Self-loops are forbidden in simple graphs: ({u}, {v})")
            if not (0 <= u < self.order and 0 <= v < self.order):
                raise ValueError(
                    f"Edge ({u}, {v}) is out of vertex bounds [0, {self.order - 1}]"
                )
            canon_edges.add((min(u, v), max(u, v)))

        object.__setattr__(self, "edges", tuple(sorted(canon_edges)))
        if not self.name:
            object.__setattr__(self, "name", f"G_{self.order}_{len(self.edges)}")

    @property
    def size(self) -> int:
        """Number of edges."""
        return len(self.edges)

    @classmethod
    def from_networkx(
        cls,
        G: nx.Graph,
        name: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> GraphInstance:
        """Create GraphInstance from a NetworkX Graph, remapping nodes to 0..n-1."""
        if G.is_directed():
            raise ValueError("Only undirected graphs are supported")

        nodes_sorted = sorted(G.nodes())
        mapping = {node: i for i, node in enumerate(nodes_sorted)}
        edges = [(mapping[u], mapping[v]) for u, v in G.edges() if u != v]

        inst_name = name or getattr(G, "name", "") or f"nx_{len(nodes_sorted)}"
        inst = cls(
            order=len(nodes_sorted),
            edges=tuple(edges),
            name=inst_name,
            metadata=metadata or {},
        )
        return inst

    @classmethod
    def from_adjacency_matrix(
        cls,
        adj: Union[np.ndarray, Sequence[Sequence[int]]],
        name: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> GraphInstance:
        """Create GraphInstance from a symmetric 2D adjacency matrix."""
        A = np.asarray(adj, dtype=int)
        if A.ndim != 2 or A.shape[0] != A.shape[1]:
            raise ValueError(f"Adjacency matrix must be square 2D, got shape {A.shape}")
        if not np.array_equal(A, A.T):
            raise ValueError("Adjacency matrix must be symmetric for undirected graphs")
        if np.any(np.diag(A) != 0):
            raise ValueError("Adjacency matrix diagonal must be 0 (no self-loops)")

        n = A.shape[0]
        edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] != 0]
        inst = cls(
            order=n,
            edges=tuple(edges),
            name=name or f"adj_{n}",
            metadata=metadata or {},
        )
        inst._adj_cache = A.copy()
        return inst

    @classmethod
    def from_edge_list(
        cls,
        edges: Iterable[Tuple[int, int]],
        order: Optional[int] = None,
        name: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ) -> GraphInstance:
        """Create GraphInstance from an edge list. If order is None, inferred from max vertex."""
        edge_list = list(edges)
        if order is None:
            if not edge_list:
                order = 0
            else:
                order = max(max(u, v) for u, v in edge_list) + 1
        return cls(
            order=order,
            edges=tuple(edge_list),
            name=name or f"edges_{order}",
            metadata=metadata or {},
        )

    def to_networkx(self) -> nx.Graph:
        """Convert to NetworkX Graph (cached)."""
        if self._nx_cache is None:
            G = nx.Graph()
            G.add_nodes_from(range(self.order))
            G.add_edges_from(self.edges)
            G.name = self.name
            self._nx_cache = G
        return self._nx_cache

    def to_adjacency_matrix(self) -> np.ndarray:
        """Convert to 2D numpy adjacency matrix (cached)."""
        if self._adj_cache is None:
            A = np.zeros((self.order, self.order), dtype=np.int64)
            for u, v in self.edges:
                A[u, v] = 1
                A[v, u] = 1
            self._adj_cache = A
        return self._adj_cache

    def to_edge_list(self) -> List[Tuple[int, int]]:
        """Return list of canonical edges."""
        return list(self.edges)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to JSON-serializable dictionary."""
        return {
            "order": self.order,
            "size": self.size,
            "edges": [list(e) for e in self.edges],
            "name": self.name,
            "metadata": self.metadata,
            "hash": self.canonical_hash,
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> GraphInstance:
        """Reconstruct from dictionary."""
        edges = tuple((int(u), int(v)) for u, v in data["edges"])
        return cls(
            order=int(data["order"]),
            edges=edges,
            name=data.get("name", ""),
            metadata=data.get("metadata", {}),
        )

    @property
    def canonical_hash(self) -> str:
        """Deterministic SHA256 digest of canonical order and edges."""
        edge_str = ",".join(f"{u}-{v}" for u, v in self.edges)
        raw = f"{self.order};{edge_str}"
        return hashlib.sha256(raw.encode("utf-8")).hexdigest()

    def to_graph6(self) -> str:
        """Convert to graph6 string format."""
        G = self.to_networkx()
        return nx.to_graph6_bytes(G, header=False).decode("ascii").strip()

    @classmethod
    def from_graph6(cls, g6_str: str, name: Optional[str] = None) -> GraphInstance:
        """Construct from graph6 string."""
        G = nx.from_graph6_bytes(g6_str.encode("ascii"))
        return cls.from_networkx(G, name=name or f"g6_{len(G)}")

    # Invariant Cache API
    def get_invariant(self, key: str) -> Optional[Any]:
        return self._invariant_cache.get(key)

    def set_invariant(self, key: str, value: Any) -> None:
        self._invariant_cache[key] = value

    def has_invariant(self, key: str) -> bool:
        return key in self._invariant_cache

    def clear_cache(self) -> None:
        self._invariant_cache.clear()
        self._nx_cache = None
        self._adj_cache = None

    # Canonical Graph Factories
    @classmethod
    def empty(cls, n: int) -> GraphInstance:
        return cls(order=n, edges=(), name=f"Empty_{n}")

    @classmethod
    def complete(cls, n: int) -> GraphInstance:
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        return cls(order=n, edges=tuple(edges), name=f"K_{n}")

    @classmethod
    def cycle(cls, n: int) -> GraphInstance:
        if n < 3:
            raise ValueError(f"Cycle graph requires n >= 3, got {n}")
        edges = [(i, (i + 1) % n) for i in range(n)]
        return cls(order=n, edges=tuple(edges), name=f"C_{n}")

    @classmethod
    def path(cls, n: int) -> GraphInstance:
        if n < 1:
            raise ValueError(f"Path graph requires n >= 1, got {n}")
        edges = [(i, i + 1) for i in range(n - 1)]
        return cls(order=n, edges=tuple(edges), name=f"P_{n}")

    @classmethod
    def complete_bipartite(cls, n1: int, n2: int) -> GraphInstance:
        edges = [(i, n1 + j) for i in range(n1) for j in range(n2)]
        return cls(order=n1 + n2, edges=tuple(edges), name=f"K_{n1}_{n2}")

    @classmethod
    def star(cls, n: int) -> GraphInstance:
        """Star graph with central vertex 0 and n-1 leaves."""
        if n < 1:
            raise ValueError(f"Star graph requires n >= 1, got {n}")
        edges = [(0, i) for i in range(1, n)]
        return cls(order=n, edges=tuple(edges), name=f"Star_{n}")

    @classmethod
    def wheel(cls, n: int) -> GraphInstance:
        """Wheel graph W_n with 1 center (vertex 0) and n-1 cycle vertices."""
        if n < 4:
            raise ValueError(f"Wheel graph requires n >= 4, got {n}")
        edges = [(0, i) for i in range(1, n)]  # spokes
        for i in range(1, n):
            nxt = 1 if i == n - 1 else i + 1
            edges.append((i, nxt))
        return cls(order=n, edges=tuple(edges), name=f"W_{n}")

    @classmethod
    def petersen(cls) -> GraphInstance:
        G = nx.petersen_graph()
        return cls.from_networkx(G, name="Petersen")

    @classmethod
    def mycielski(cls, k: int) -> GraphInstance:
        """Generate Mycielskian M_k. M_2 = K_2, M_3 = C_5, M_4 = Grötzsch."""
        G = nx.mycielski_graph(k)
        return cls.from_networkx(G, name=f"Mycielski_{k}")


# Alias GraphWrapper to GraphInstance for interchangeable usage
GraphWrapper = GraphInstance
