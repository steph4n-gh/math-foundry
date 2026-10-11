"""Root pytest configuration and shared test fixtures for autonomous_math."""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Dict, List, Union

import networkx as nx
import pytest

# Ensure autonomous_math root is on sys.path
AUTONOMOUS_MATH_ROOT = Path(__file__).resolve().parent.parent
if str(AUTONOMOUS_MATH_ROOT) not in sys.path:
    sys.path.insert(0, str(AUTONOMOUS_MATH_ROOT))


@pytest.fixture
def graph_null() -> nx.Graph:
    """Empty graph with 0 vertices."""
    return nx.empty_graph(0)


@pytest.fixture
def graph_k1() -> nx.Graph:
    """Single-vertex graph K1."""
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
def graph_c4() -> nx.Graph:
    """Cycle graph C4."""
    return nx.cycle_graph(4)


@pytest.fixture
def graph_c5() -> nx.Graph:
    """Cycle graph C5 (benchmark counterexample)."""
    return nx.cycle_graph(5)


@pytest.fixture
def graph_petersen() -> nx.Graph:
    """Petersen graph (10 vertices, 15 edges, 3-regular, girth 5, chi 3)."""
    return nx.petersen_graph()


@pytest.fixture
def graph_empty_5() -> nx.Graph:
    """Edgeless graph with 5 vertices."""
    return nx.empty_graph(5)


@pytest.fixture
def graph_star_6() -> nx.Graph:
    """Star graph with 6 vertices (1 center, 5 leaves)."""
    return nx.star_graph(5)


@pytest.fixture
def graph_k2_3() -> nx.Graph:
    """Complete bipartite graph K_{2,3}."""
    return nx.complete_bipartite_graph(2, 3)


@pytest.fixture
def graph_disconnected_k3_k3() -> nx.Graph:
    """Disconnected graph consisting of two disjoint triangles."""
    return nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
