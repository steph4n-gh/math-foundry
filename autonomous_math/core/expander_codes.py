"""Exact small binary adjacency codes and known-erasure parity peeling.

Variables and checks are separate copies of the graph's vertex set. A codeword
has even selected-neighbor count at every check. Graph size is capped before
the exponential minimum-weight and stopping-set searches; unsupported is an
exception, never a guessed scalar. No spectral surrogate or error decoder is used.
"""

from dataclasses import dataclass
from functools import lru_cache

import networkx as nx

from autonomous_math.core.graph_types import GraphInstance

MAX_EXACT_CODE_ORDER = 16


def _rows(graph) -> tuple[int, ...]:
    if isinstance(graph, nx.Graph):
        if graph.is_directed() or graph.is_multigraph() or nx.number_of_selfloops(graph):
            raise ValueError("Binary adjacency codes require a simple undirected graph")
        if len(graph) > MAX_EXACT_CODE_ORDER:
            raise ValueError("Exact adjacency-code evaluation supports at most 16 vertices")
        graph = GraphInstance.from_networkx(graph)
    if not isinstance(graph, GraphInstance):
        raise TypeError("Expected GraphInstance or a simple NetworkX graph")
    if graph.order > MAX_EXACT_CODE_ORDER:
        raise ValueError("Exact adjacency-code evaluation supports at most 16 vertices")
    rows = [0] * graph.order
    for u, v in graph.edges:
        rows[u] |= 1 << v
        rows[v] |= 1 << u
    return tuple(rows)


@lru_cache(maxsize=128)
def _kernel_basis(rows: tuple[int, ...]) -> tuple[int, ...]:
    """GF(2) row reduction; basis vectors are variable-support bit masks."""
    reduced, pivots = list(rows), []
    for column in range(len(rows)):
        pivot = next((r for r in range(len(pivots), len(rows)) if reduced[r] & (1 << column)), None)
        if pivot is None:
            continue
        position = len(pivots)
        reduced[position], reduced[pivot] = reduced[pivot], reduced[position]
        for r in range(len(rows)):
            if r != position and reduced[r] & (1 << column):
                reduced[r] ^= reduced[position]
        pivots.append(column)
    basis = []
    for free in range(len(rows)):
        if free in pivots:
            continue
        word = 1 << free
        for row, pivot in zip(reduced, pivots):
            if row & (1 << free):
                word |= 1 << pivot
        basis.append(word)
    return tuple(basis)


@lru_cache(maxsize=128)
def _distance(rows: tuple[int, ...]) -> int:
    basis = _kernel_basis(rows)
    distance, word = len(rows) + 1, 0
    # Gray-code traversal changes one basis vector per nonzero codeword.
    for index in range(1, 1 << len(basis)):
        word ^= basis[(index & -index).bit_length() - 1]
        distance = min(distance, word.bit_count())
        if distance == 1:
            break
    return distance


@lru_cache(maxsize=128)
def _unique_radius(rows: tuple[int, ...]) -> int:
    # A stopping set has no check with exactly one selected neighbor. Enumerate
    # in increasing weight and return its first size minus one; no set means n.
    for weight in range(1, len(rows) + 1):
        mask = (1 << weight) - 1
        while mask < 1 << len(rows):
            if all((row & mask).bit_count() != 1 for row in rows):
                return weight - 1
            low = mask & -mask
            following = mask + low
            mask = following | (((following ^ mask) >> 2) // low)
    return len(rows)


def compute_parity_code_distance(graph) -> int:
    """Minimum nonzero binary kernel weight, with n+1 for the zero code."""
    return _distance(_rows(graph))


def compute_parity_code_dimension(graph) -> int:
    """Binary nullity n-rank_GF2(A), exposing zero-code vacuity explicitly."""
    return len(_kernel_basis(_rows(graph)))


def compute_unique_neighbor_radius(graph) -> int:
    """Largest k<=n where every nonempty |S|<=k has a unique-neighbor check."""
    return _unique_radius(_rows(graph))


@dataclass(frozen=True)
class ErasureDecodeResult:
    status: str
    word: tuple[int | None, ...]
    # Each step is (check index, recovered variable index, recovered bit).
    steps: tuple[tuple[int, int, int], ...]
    unresolved_positions: tuple[int, ...]
    violated_checks: tuple[int, ...]


def peel_erasures(graph, received) -> ErasureDecodeResult:
    """Recover known erasures using single-unknown parity checks, at most n steps.

    received uses canonical sorted vertex order, 0/1 for known bits and None
    for erasures. Correctness requires the known bits to be uncorrupted.
    Blocked/inconsistent inputs retain their partial word and full step trace.
    """
    rows = _rows(graph)
    if not isinstance(received, (list, tuple)) or len(received) != len(rows) or any(
            bit is not None and (type(bit) is not int or bit not in (0, 1)) for bit in received):
        raise ValueError("Received word must have one binary integer or None per vertex")
    word, steps = list(received), []
    while True:
        unknown = sum(1 << i for i, bit in enumerate(word) if bit is None)
        ones = sum(1 << i for i, bit in enumerate(word) if bit == 1)
        violations = tuple(i for i, row in enumerate(rows)
                           if not row & unknown and (row & ones).bit_count() % 2)
        if violations or not unknown:
            status = "INCONSISTENT" if violations else "DECODED"
            break
        for check, row in enumerate(rows):
            missing = row & unknown
            if missing and missing & (missing - 1) == 0:
                variable = missing.bit_length() - 1
                bit = (row & ones).bit_count() % 2
                word[variable] = bit
                steps.append((check, variable, bit))
                break
        else:
            status = "BLOCKED"
            break
    return ErasureDecodeResult(status, tuple(word), tuple(steps),
        tuple(i for i, bit in enumerate(word) if bit is None), violations)
