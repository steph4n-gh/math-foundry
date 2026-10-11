"""Adverse controls for timeout claims and concurrent exact invariants."""
from concurrent.futures import ThreadPoolExecutor
from types import SimpleNamespace

import networkx as nx
import pytest

from autonomous_math.core.invariants import compute_chromatic_number, compute_clique_number, compute_independence_number
from spectral_pruning import benchmark_runner


def test_parallel_exact_invariants_use_independent_solver_contexts():
    graph = nx.wheel_graph(6)
    functions = [compute_chromatic_number, compute_clique_number, compute_independence_number] * 8
    with ThreadPoolExecutor(max_workers=6) as executor:
        results = list(executor.map(lambda function: function(graph), functions))
    assert results == [4, 3, 2] * 8


def configure_searches(monkeypatch, baseline_witness, spectral_witness):
    graph = nx.path_graph(3)
    graph.name = "timeout_control"
    monkeypatch.setattr(benchmark_runner, "get_standard_benchmark_suite", lambda: [graph])

    def solver(witness):
        metrics = SimpleNamespace(completed=False, timed_out=True, nodes_visited=8,
                                  runtime_ms=10, spectral_prunes=0, fiedler_splits=0)
        return SimpleNamespace(solve=lambda _graph, timeout_sec: (len(witness), witness, metrics))

    monkeypatch.setattr(benchmark_runner, "BaselineCliqueSolver", lambda: solver(baseline_witness))
    monkeypatch.setattr(benchmark_runner, "SpectralCliqueSolver", lambda: solver(spectral_witness))


def test_different_valid_timeout_incumbents_do_not_claim_optimum_or_speedup(monkeypatch, tmp_path):
    configure_searches(monkeypatch, [0], [0, 1])
    result = benchmark_runner.run_comparative_benchmark(tmp_path, timeout_sec=0)
    row = result["results"][0]
    assert row["baseline_incumbent"] == 1 and row["spectral_incumbent"] == 2
    assert row["max_clique_omega"] is None and row["speedup"] is None
    assert result["completed_pairs"] == 0 and result["overall_speedup"] is None
    assert result["total_base_nodes"] == result["total_spec_nodes"] == 0


def test_timeout_witness_must_still_be_a_clique(monkeypatch, tmp_path):
    configure_searches(monkeypatch, [0, 2], [0, 1])
    with pytest.raises(ValueError, match="Invalid baseline clique witness"):
        benchmark_runner.run_comparative_benchmark(tmp_path, timeout_sec=0)
