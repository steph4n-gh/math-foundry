"""Shared pytest fixtures, reference mathematical oracles, and environment configuration

for the Autonomous Mathematical Discovery Pipeline E2E test suite.
"""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

import networkx as nx
import numpy as np
import pytest
import z3

# Ensure autonomous_math package root is on sys.path
AUTONOMOUS_MATH_ROOT = Path(__file__).resolve().parents[2]
if str(AUTONOMOUS_MATH_ROOT) not in sys.path:
    sys.path.insert(0, str(AUTONOMOUS_MATH_ROOT))


# ============================================================================
# AUTHORITATIVE REFERENCE MATHEMATICAL ORACLES
# Every test derives expected mathematical outputs from these pure reference oracles.
# ============================================================================

class ReferenceGraphOracle:
    """Independent ground-truth reference implementation for graph invariants and properties.

    Used as the authoritative comparison baseline for GraphInvariantEvaluator.
    """

    @staticmethod
    def order(G: nx.Graph) -> int:
        return G.number_of_nodes()

    @staticmethod
    def size(G: nx.Graph) -> int:
        return G.number_of_edges()

    @staticmethod
    def max_degree(G: nx.Graph) -> int:
        if G.number_of_nodes() == 0:
            return 0
        return max(dict(G.degree()).values())

    @staticmethod
    def min_degree(G: nx.Graph) -> int:
        if G.number_of_nodes() == 0:
            return 0
        return min(dict(G.degree()).values())

    @staticmethod
    def density(G: nx.Graph) -> float:
        n = G.number_of_nodes()
        if n <= 1:
            return 0.0
        return float(2.0 * G.number_of_edges() / (n * (n - 1)))

    @staticmethod
    def triangle_count(G: nx.Graph) -> int:
        if G.number_of_nodes() < 3:
            return 0
        return sum(nx.triangles(G).values()) // 3

    @staticmethod
    def is_triangle_free(G: nx.Graph) -> bool:
        return ReferenceGraphOracle.triangle_count(G) == 0

    @staticmethod
    def girth(G: nx.Graph) -> float:
        if G.number_of_nodes() < 3:
            return float("inf")
        cycles = nx.cycle_basis(G)
        if not cycles:
            return float("inf")
        return float(min(len(c) for c in cycles))

    @staticmethod
    def clique_number(G: nx.Graph) -> int:
        if G.number_of_nodes() == 0:
            return 0
        return max((len(c) for c in nx.find_cliques(G)), default=0)

    @staticmethod
    def independence_number(G: nx.Graph) -> int:
        if G.number_of_nodes() == 0:
            return 0
        complement = nx.complement(G)
        return max((len(c) for c in nx.find_cliques(complement)), default=0)

    @staticmethod
    def chromatic_number_exact(G: nx.Graph) -> int:
        """Exact chromatic number computed via Z3 SAT."""
        n = G.number_of_nodes()
        if n == 0:
            return 0
        if G.number_of_edges() == 0:
            return 1
        if nx.is_bipartite(G):
            return 2

        # Check k from 3 to n
        nodes = list(G.nodes())
        node_idx = {node: i for i, node in enumerate(nodes)}

        for k in range(3, n + 1):
            s = z3.Solver()
            # color variables: c_i in [0, k-1]
            c = [z3.Int(f"c_{i}") for i in range(n)]
            for i in range(n):
                s.add(c[i] >= 0, c[i] < k)
            for u, v in G.edges():
                s.add(c[node_idx[u]] != c[node_idx[v]])

            if s.check() == z3.sat:
                return k
        return n

    @staticmethod
    def adjacency_spectrum(G: nx.Graph) -> np.ndarray:
        if G.number_of_nodes() == 0:
            return np.array([], dtype=float)
        adj = nx.to_numpy_array(G, dtype=float)
        eigenvalues = np.linalg.eigvalsh(adj)
        return np.sort(eigenvalues)[::-1]  # descending: lambda_1 >= lambda_2 >= ...

    @staticmethod
    def laplacian_spectrum(G: nx.Graph) -> np.ndarray:
        if G.number_of_nodes() == 0:
            return np.array([], dtype=float)
        adj = nx.to_numpy_array(G, dtype=float)
        degrees = np.sum(adj, axis=1)
        L = np.diag(degrees) - adj
        eigenvalues = np.linalg.eigvalsh(L)
        return np.sort(eigenvalues)  # ascending: 0 = mu_1 <= mu_2 <= ...

    @staticmethod
    def spectral_radius(G: nx.Graph) -> float:
        spec = ReferenceGraphOracle.adjacency_spectrum(G)
        if len(spec) == 0:
            return 0.0
        return float(np.max(np.abs(spec)))

    @staticmethod
    def algebraic_connectivity(G: nx.Graph) -> float:
        spec = ReferenceGraphOracle.laplacian_spectrum(G)
        if len(spec) < 2:
            return 0.0
        return float(spec[1])

    @staticmethod
    def diameter(G: nx.Graph) -> float:
        if G.number_of_nodes() <= 1:
            return 0.0
        if not nx.is_connected(G):
            return float("inf")
        return float(nx.diameter(G))

    @staticmethod
    def radius(G: nx.Graph) -> float:
        if G.number_of_nodes() <= 1:
            return 0.0
        if not nx.is_connected(G):
            return float("inf")
        return float(nx.radius(G))

    @classmethod
    def evaluate_all(cls, G: nx.Graph) -> Dict[str, Any]:
        """Compute full invariant profile using reference logic."""
        adj_spec = cls.adjacency_spectrum(G)
        lap_spec = cls.laplacian_spectrum(G)
        return {
            "order": cls.order(G),
            "size": cls.size(G),
            "max_degree": cls.max_degree(G),
            "min_degree": cls.min_degree(G),
            "density": cls.density(G),
            "triangle_count": cls.triangle_count(G),
            "is_triangle_free": cls.is_triangle_free(G),
            "is_bipartite": nx.is_bipartite(G) if cls.order(G) > 0 else True,
            "is_connected": nx.is_connected(G) if cls.order(G) > 0 else False,
            "girth": cls.girth(G),
            "clique_number": cls.clique_number(G),
            "independence_number": cls.independence_number(G),
            "chromatic_number": cls.chromatic_number_exact(G),
            "spectral_radius": cls.spectral_radius(G),
            "min_adjacency_eigenvalue": float(adj_spec[-1]) if len(adj_spec) > 0 else 0.0,
            "algebraic_connectivity": cls.algebraic_connectivity(G),
            "laplacian_spectral_radius": float(lap_spec[-1]) if len(lap_spec) > 0 else 0.0,
            "diameter": cls.diameter(G),
            "radius": cls.radius(G),
        }


# ============================================================================
# CANONICAL GRAPH FIXTURES
# ============================================================================

@pytest.fixture
def oracle():
    """Provides access to the reference mathematical graph oracle."""
    return ReferenceGraphOracle


@pytest.fixture
def graph_c5() -> nx.Graph:
    """The canonical 5-cycle C5: triangle-free, chromatic number 3, 5 vertices, 5 edges."""
    return nx.cycle_graph(5)


@pytest.fixture
def graph_c6() -> nx.Graph:
    """Even 6-cycle C6: triangle-free, bipartite, chromatic number 2, 6 vertices, 6 edges."""
    return nx.cycle_graph(6)


@pytest.fixture
def graph_petersen() -> nx.Graph:
    """Petersen graph: 10 vertices, 15 edges, triangle-free, girth 5, chi=3, omega=2, alpha=4."""
    return nx.petersen_graph()


@pytest.fixture
def graph_grotzsch() -> nx.Graph:
    """Grötzsch graph (Mycielskian of C5, 4th Mycielski graph): 11 vertices, 20 edges, triangle-free, chi=4, omega=2."""
    return nx.mycielski_graph(4)


@pytest.fixture
def graph_k1() -> nx.Graph:
    """Single vertex graph K1."""
    return nx.complete_graph(1)


@pytest.fixture
def graph_k4() -> nx.Graph:
    """Complete graph K4."""
    return nx.complete_graph(4)


@pytest.fixture
def graph_k5() -> nx.Graph:
    """Complete graph K5."""
    return nx.complete_graph(5)


@pytest.fixture
def graph_empty_5() -> nx.Graph:
    """Edgeless graph with 5 vertices."""
    return nx.empty_graph(5)


@pytest.fixture
def graph_star_6() -> nx.Graph:
    """Star graph S6 (K1,5): 6 vertices, 5 edges, delta=5, chi=2, alpha=5, omega=2."""
    return nx.star_graph(5)


@pytest.fixture
def graph_disconnected_k3_k3() -> nx.Graph:
    """Disconnected graph consisting of two disjoint triangles K3 + K3."""
    return nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))


@pytest.fixture
def graph_null() -> nx.Graph:
    """Empty null graph with 0 vertices."""
    return nx.Graph()


# ============================================================================
# REFERENCE OUTPUT VALIDATORS
# ============================================================================

class ReferenceArtifactValidator:
    """Reference validator for Lean 4 and LaTeX outputs."""

    @staticmethod
    def validate_lean_comparator_json(json_content: str) -> Tuple[bool, List[str]]:
        errors = []
        try:
            data = json.loads(json_content)
        except json.JSONDecodeError as e:
            return False, [f"Invalid JSON: {e}"]

        required_keys = {
            "challenge_module",
            "solution_module",
            "theorem_names",
            "definition_names",
            "permitted_axioms",
            "enable_nanoda",
        }
        missing = required_keys - set(data.keys())
        if missing:
            errors.append(f"Missing required keys: {missing}")

        if not isinstance(data.get("theorem_names"), list):
            errors.append("'theorem_names' must be a list")
        if not isinstance(data.get("permitted_axioms"), list):
            errors.append("'permitted_axioms' must be a list")
        if not isinstance(data.get("enable_nanoda"), bool):
            errors.append("'enable_nanoda' must be a boolean")

        return len(errors) == 0, errors

    @staticmethod
    def validate_lean_source(lean_code: str) -> Tuple[bool, List[str]]:
        errors = []
        if "import Mathlib" not in lean_code:
            errors.append("Missing 'import Mathlib'")
        if "namespace OAI" not in lean_code:
            errors.append("Missing 'namespace OAI'")
        if "theorem" not in lean_code and "def" not in lean_code:
            errors.append("No theorem or def declared in Lean source")
        if lean_code.count("namespace") != lean_code.count("end"):
            errors.append("Mismatched namespace open/close count")
        return len(errors) == 0, errors

    @staticmethod
    def validate_latex_source(tex_content: str) -> Tuple[bool, List[str]]:
        errors = []
        # Check balanced environments
        begins = re.findall(r"\\begin\{([a-zA-Z0-9*]+)\}", tex_content)
        ends = re.findall(r"\\end\{([a-zA-Z0-9*]+)\}", tex_content)
        if begins != ends:
            # Check counts per environment
            from collections import Counter
            cb = Counter(begins)
            ce = Counter(ends)
            for env in set(cb.keys()) | set(ce.keys()):
                if cb[env] != ce[env]:
                    errors.append(f"Unbalanced LaTeX environment '\\begin{{{env}}}' ({cb[env]}) vs '\\end{{{env}}}' ({ce[env]})")
        return len(errors) == 0, errors


@pytest.fixture
def artifact_validator():
    return ReferenceArtifactValidator
