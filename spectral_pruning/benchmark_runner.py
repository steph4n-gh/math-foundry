"""Empirical Benchmark Runner: Spectral Pruning vs. Classical Baseline for Maximum Clique.

Executes a comparative head-to-head empirical evaluation across standard,
planted, clustered bottleneck, and geometric graphs.
Measures search tree node visited reduction, spectral prune count, and execution time.
Outputs LaTeX tables and Markdown summaries.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys
import time
from typing import Any, Dict, List, Optional
from itertools import combinations

import pandas as pd

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from spectral_pruning.benchmarks import get_standard_benchmark_suite
from spectral_pruning.solvers import BaselineCliqueSolver, SpectralCliqueSolver


def run_comparative_benchmark(output_dir: Optional[Path] = None, timeout_sec: float = 30.0) -> Dict[str, Any]:
    out_dir = output_dir or (Path(__file__).resolve().parent / "qualified_benchmark_results")
    out_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 86)
    print("  EMPIRICAL RESEARCH BENCHMARK: SPECTRAL PRUNING FOR THE NP-HARD MAXIMUM CLIQUE")
    print("  Comparing Classical Branch-and-Bound vs. Perron-Frobenius & Fiedler Pruning")
    print("=" * 86)

    suite = get_standard_benchmark_suite()
    print(f"\nLoaded {len(suite)} benchmark instances spanning diverse topological regimes.\n")

    baseline_solver = BaselineCliqueSolver()
    spectral_solver = SpectralCliqueSolver()

    results = []

    print(f"{'Graph Name':<28} {'n':<5} {'m':<6} {'omega':<6} {'Base Nodes':<12} {'Spec Nodes':<12} {'Node Red.':<10} {'Speedup':<8}")
    print("-" * 86)

    total_base_nodes = 0
    total_spec_nodes = 0
    total_base_time = 0.0
    total_spec_time = 0.0
    completed_pairs = 0

    for G in suite:
        name = G.name
        n = G.number_of_nodes()
        m = G.number_of_edges()

        # Run Baseline
        omega_base, nodes_base, m_base = baseline_solver.solve(G, timeout_sec=timeout_sec)
        # Run Spectral
        omega_spec, nodes_spec, m_spec = spectral_solver.solve(G, timeout_sec=timeout_sec)

        for solver_name, omega, witness in (("baseline", omega_base, nodes_base), ("spectral", omega_spec, nodes_spec)):
            if len(witness) != omega or len(set(witness)) != omega or any(v not in G for v in witness) or any(
                    not G.has_edge(u, v) for u, v in combinations(witness, 2)):
                raise ValueError(f"Invalid {solver_name} clique witness on {name}")
        if ((m_base.completed and omega_spec > omega_base) or
                (m_spec.completed and omega_base > omega_spec) or
                (m_base.completed and m_spec.completed and omega_base != omega_spec)):
            raise ValueError(f"Conflicting completed clique searches on {name}: {omega_base} != {omega_spec}")
        comparable = m_base.completed and m_spec.completed
        optimum = omega_base if m_base.completed else omega_spec if m_spec.completed else None

        base_nodes = m_base.nodes_visited
        spec_nodes = m_spec.nodes_visited
        base_time = m_base.runtime_ms
        spec_time = m_spec.runtime_ms

        if comparable:
            completed_pairs += 1
            total_base_nodes += base_nodes
            total_spec_nodes += spec_nodes
            total_base_time += base_time
            total_spec_time += spec_time

        node_reduction = (1.0 - (spec_nodes / max(1, base_nodes))) * 100.0 if comparable else None
        speedup = base_time / max(1e-4, spec_time) if comparable else None

        comparison = f"{node_reduction:>+7.1f}%   {speedup:>6.2f}x" if comparable else "unfinished; comparison excluded"
        print(f"{name:<28} {n:<5} {m:<6} {str(optimum):<6} {base_nodes:<12} {spec_nodes:<12} {comparison}")

        results.append({
            "graph": name,
            "order_n": n,
            "size_m": m,
            "max_clique_omega": optimum,
            "baseline_incumbent": omega_base,
            "spectral_incumbent": omega_spec,
            "baseline_witness": nodes_base,
            "spectral_witness": nodes_spec,
            "baseline_completed": m_base.completed,
            "spectral_completed": m_spec.completed,
            "baseline_timed_out": m_base.timed_out,
            "spectral_timed_out": m_spec.timed_out,
            "baseline_nodes": base_nodes,
            "spectral_nodes": spec_nodes,
            "node_reduction_pct": node_reduction,
            "baseline_time_ms": base_time,
            "spectral_time_ms": spec_time,
            "speedup": speedup,
            "spectral_prunes": m_spec.spectral_prunes,
            "fiedler_splits": m_spec.fiedler_splits,
        })

    print("-" * 86)
    overall_reduction = (1.0 - (total_spec_nodes / max(1, total_base_nodes))) * 100.0 if completed_pairs else None
    overall_speedup = total_base_time / max(1e-4, total_spec_time) if completed_pairs else None
    print(f"Completed comparison pairs: {completed_pairs}/{len(results)}; speedup: {overall_speedup}")
    print("=" * 86)

    # Export to JSON and CSV
    df = pd.DataFrame(results)
    csv_path = out_dir / "benchmark_data.csv"
    json_path = out_dir / "benchmark_data.json"
    df.to_csv(csv_path, index=False)
    json_path.write_text(json.dumps(results, indent=2, allow_nan=False), encoding="utf-8")

    # Generate LaTeX table code
    latex_table = df[["graph", "order_n", "size_m", "max_clique_omega", "baseline_nodes", "spectral_nodes", "node_reduction_pct", "speedup"]].to_latex(
        index=False,
        float_format="%.2f",
        caption="Measured clique searches. Speedup and node reduction include only pairs where both searches completed; missing optima remain unknown.",
        label="tab:spectral_pruning_results",
    )
    (out_dir / "results_table.tex").write_text(latex_table, encoding="utf-8")

    print(f"\nDeliverables saved to {out_dir}:")
    print(f"  * CSV Data   : {csv_path.name}")
    print(f"  * JSON Data  : {json_path.name}")
    print(f"  * LaTeX Table: results_table.tex")

    return {
        "results": results,
        "completed_pairs": completed_pairs,
        "total_base_nodes": total_base_nodes,
        "total_spec_nodes": total_spec_nodes,
        "overall_reduction": overall_reduction,
        "overall_speedup": overall_speedup,
    }


if __name__ == "__main__":
    run_comparative_benchmark()
