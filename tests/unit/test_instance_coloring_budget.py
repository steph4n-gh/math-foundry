"""Independent exact-coloring checks and fail-closed replay budget controls."""
from functools import lru_cache
from types import SimpleNamespace

import networkx as nx
import pytest

from autonomous_math.core.graph_types import GraphInstance
from autonomous_math.sieve import instance_db


def partition_oracle(graph):
    """Exhaustively partition vertices into independent sets (not DSATUR)."""
    nodes = list(graph)
    adjacency = [sum(1 << j for j, v in enumerate(nodes) if graph.has_edge(u, v)) for u in nodes]
    independent = [True] * (1 << len(nodes))
    for mask in range(1, len(independent)):
        pivot = mask & -mask
        remainder = mask ^ pivot
        independent[mask] = independent[remainder] and not (adjacency[pivot.bit_length() - 1] & remainder)

    @lru_cache(None)
    def colors(mask):
        if not mask:
            return 0
        pivot = mask & -mask
        subset = mask
        best = len(nodes)
        while subset:
            if subset & pivot and independent[subset]:
                best = min(best, 1 + colors(mask ^ subset))
            subset = (subset - 1) & mask
        return best

    return colors((1 << len(nodes)) - 1)


def stalled_boundary():
    # The retained 33-vertex,264-edge counterexample is the eighth power of C33.
    graph = nx.Graph()
    graph.add_nodes_from(range(33))
    graph.add_edges_from((u, (u + offset) % 33) for u in range(33) for offset in range(1, 9))
    return graph


def test_exact_coloring_matches_independent_partition_oracle_for_entire_atlas():
    graphs = nx.graph_atlas_g()
    assert len(graphs) == 1253
    for graph in graphs:
        assert instance_db._exact_chromatic_backtrack(graph) == partition_oracle(graph)


def test_relabeling_disconnected_and_more_than_legacy_max_k():
    graph = nx.disjoint_union(nx.mycielski_graph(4), nx.cycle_graph(9))
    assert instance_db._exact_chromatic_backtrack(graph) == 4
    relabeled = nx.relabel_nodes(graph, {u: ("vertex", u) for u in graph})
    assert instance_db._exact_chromatic_backtrack(relabeled) == 4
    assert instance_db._exact_chromatic_backtrack(nx.complete_graph(30), max_k=1) == 30


@pytest.mark.parametrize("budget", [0, -1, float("inf"), float("nan")])
def test_exact_search_requires_finite_positive_budget(budget):
    with pytest.raises(ValueError, match="finite positive"):
        instance_db._exact_chromatic_backtrack(nx.cycle_graph(5), timeout_sec=budget)


def test_deadline_during_search_does_not_return_greedy_upper_bound(monkeypatch):
    graph = nx.mycielski_graph(4)
    calls = 0

    def clock():
        nonlocal calls
        calls += 1
        # Deadline creation,initial check,one per clique seed and greedy vertex
        # all finish; the first exact search call crosses the budget.
        return 0 if calls <= 2 + 2 * len(graph) else 1

    monkeypatch.setattr(instance_db, "time", SimpleNamespace(monotonic=clock))
    with pytest.raises(TimeoutError, match="Exact chromatic search"):
        instance_db._exact_chromatic_backtrack(graph, timeout_sec=0.5)


def test_retained_dense_boundary_has_exact_coloring_witness_and_finite_timeout():
    graph = stalled_boundary()
    assert graph.number_of_nodes() == 33 and graph.number_of_edges() == 264
    # A 3-vertex independent-set upper bound gives chi>=11; i mod11 proves<=11.
    assert all(u % 11 != v % 11 for u, v in graph.edges())
    assert max(map(len, nx.find_cliques(nx.complement(graph)))) == 3
    with pytest.raises(TimeoutError, match="Exact chromatic search"):
        instance_db._exact_chromatic_backtrack(graph, timeout_sec=0.005, lower_bound=11)


def test_timed_out_addition_does_not_admit_partial_invariants(monkeypatch):
    graph = stalled_boundary()
    names = ("_cached_nx", "_cached_gi", "_cached_invariants")
    for name in names:
        monkeypatch.setattr(instance_db.InstanceDatabase, name, [])
    monkeypatch.setattr(instance_db.InstanceDatabase, "_cached_matrix", {})
    monkeypatch.setattr(instance_db.InstanceDatabase, "_code_columns_enabled", False)
    original = instance_db._exact_chromatic_backtrack
    monkeypatch.setattr(instance_db, "_exact_chromatic_backtrack",
                        lambda *args, **kwargs: original(*args, **dict(kwargs, timeout_sec=0.005)))
    database = instance_db.InstanceDatabase()
    with pytest.raises(TimeoutError):
        database.add_instance(GraphInstance.from_networkx(graph))
    assert all(getattr(instance_db.InstanceDatabase, name) == [] for name in names)
    assert instance_db.InstanceDatabase._cached_matrix == {}
