"""Qualify optional clique bounds on an independent oracle and published DIMACS.

Example:
    python -m spectral_pruning.certified_bounds_benchmark --receipt DEGREE.json \
        --receipt EDGES.json --timeout 2 --trials 3

All comparisons use one solver and one ordering with only the bounds switch
changed. Every trial's witness and timeout status is retained. Incomplete pairs
are excluded from runtime and search-node summaries; slowdowns remain included.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import platform
import statistics
import sys
import time
from pathlib import Path

import networkx as nx
import numpy as np
import sympy as sp

from autonomous_math.core.ast import Conjecture
from autonomous_math.research_state import atomic_save_json, sha256, validate_receipt
from spectral_pruning.bitset_solvers import (
    BitsetBaselineSolver,
    BitsetSpectralSolver,
    _parse_dimacs_clq,
)

ROOT = Path(__file__).resolve().parent.parent


def validate_witness(graph, size, witness):
    if (size != len(witness) or len(set(witness)) != size or
            any(vertex not in graph for vertex in witness) or
            any(not graph.has_edge(u, v) for u, v in itertools.combinations(witness, 2))):
        raise AssertionError("The solver returned an invalid clique witness")


def exhaustive_clique_masks(graph):
    """Enumerate every vertex subset with NetworkX edge queries, independent of search."""
    nodes = list(graph)
    return [mask for mask in range(1 << len(nodes)) if all(
        graph.has_edge(nodes[i], nodes[j])
        for i, j in itertools.combinations([i for i in range(len(nodes)) if mask & (1 << i)], 2))]


def run_oracle_qualification(output_dir):
    started = time.monotonic()
    rows = []
    induced_graphs = prune_checks = solves = 0
    solver_types = (BitsetBaselineSolver, BitsetSpectralSolver)
    for index, graph in enumerate(nx.graph_atlas_g()):
        clique_masks = exhaustive_clique_masks(graph)
        optimum = max(mask.bit_count() for mask in clique_masks)
        results = {}
        for solver_type in solver_types:
            for enabled in (False, True):
                solver = solver_type(enable_clique_bounds=enabled)
                size, witness, metrics = solver.solve(graph, timeout_sec=5)
                validate_witness(graph, size, witness)
                if not metrics.completed or size != optimum:
                    raise AssertionError(f"Oracle disagreement on graph atlas #{index}")
                results[f'{solver_type.__name__}:{enabled}'] = {
                    'witness': witness, **metrics.to_dict()}
                solves += 1
        # Each candidate subset is also checked, not just the whole graph ceiling.
        verifier = BitsetBaselineSolver(enable_clique_bounds=True)
        verifier.solve(graph)
        for candidates in range(1 << len(graph)):
            actual = max(mask.bit_count() for mask in clique_masks if mask & candidates == mask)
            degree, edges = verifier._degree_edge_bounds(candidates)
            if degree < actual or edges < actual:
                raise AssertionError(f"Unsound candidate bound on atlas #{index}")
            coloring = verifier._greedy_coloring_bound(candidates)
            if coloring > degree or coloring > edges:
                raise AssertionError(f"Greedy coloring dominance failed on atlas #{index}")
            for budget in range(candidates.bit_count() + 1):
                if verifier._clique_bound_prunes(candidates, budget) and actual > budget:
                    raise AssertionError(f"False candidate prune on atlas #{index}")
                prune_checks += 1
            induced_graphs += 1
        rows.append({'atlas_index': index, 'order': len(graph),
                     'size': graph.number_of_edges(), 'graph6': nx.to_graph6_bytes(graph, header=False).decode().strip(),
                     'oracle_optimum': optimum, 'measurements': results})
    report = {'status': 'PASS', 'oracle': 'Every vertex subset checked with graph.has_edge',
              'graphs': len(rows), 'all_graphs_through_order': 7,
              'graph_family': 'One representative of every isomorphism class of finite simple undirected graphs through order seven (NetworkX graph atlas).',
              'induced_candidate_subsets': induced_graphs, 'candidate_prune_budget_checks': prune_checks,
              'coloring_dominance_checks': induced_graphs,
              'coloring_dominance': 'Every candidate greedy-color count is no larger than either additional bound.',
              'solver_comparisons': solves, 'duration_ms': (time.monotonic() - started) * 1000,
              'solver_source_sha256': sha256(ROOT / 'spectral_pruning/bitset_solvers.py'),
              'benchmark_source_sha256': sha256(Path(__file__)),
              'networkx_version': nx.__version__, 'results': rows}
    atomic_save_json(report, Path(output_dir) / 'clique_bounds_soundness.json')
    print(f'Independent oracle passed: {len(rows)} graphs, {induced_graphs} candidate subsets, {prune_checks} budgets, {solves} solves', flush=True)
    return report


def checked_bound_receipts(paths):
    """Require the two exact universal AST inequalities, not a theorem-name match."""
    omega, delta, edges = sp.symbols('clique_number max_degree size', real=True, nonnegative=True)
    expected = {'degree': omega - delta - 1, 'edges': omega * (omega - 1) - 2 * edges}
    found = {}
    for path in paths:
        receipt, error = validate_receipt(path)
        if not receipt:
            raise ValueError(f'Invalid formal bound receipt: {error}')
        conjecture = Conjecture.from_dict(receipt['conjecture'])
        guard = conjecture.guard_predicate
        if guard and guard.predicate_type != 'universal':
            raise ValueError('Solver bounds require unconditional finite simple graph theorems')
        if conjecture.rel not in {'<=', '>='}:
            continue
        difference = conjecture.lhs_expr.to_sympy() - conjecture.rhs_expr.to_sympy()
        if conjecture.rel == '>=':
            difference = -difference
        for name, target in expected.items():
            if sp.expand(difference - target) == 0:
                found[name] = {'receipt_path': str(Path(path).resolve()),
                    'receipt_sha256': sha256(Path(path)),
                    'source_path': receipt['source_path'], 'source_sha256': receipt['source_sha256'],
                    'conjecture': receipt['conjecture'], 'theorem_name': receipt['theorem_name'],
                    'axioms': receipt['axioms'], 'workspace_sha256': receipt['workspace_sha256'],
                    'lean_binary_sha256': receipt['lean_binary_sha256'], 'lean_version': receipt['lean_version']}
    if set(found) != set(expected):
        raise ValueError('Both checked degree and edge-count bound receipts are required')
    return found


def run_paired_dimacs(output_dir, receipt_paths, timeout_sec=2.0, trials=3, instances=None,
                      load_context='Not recorded'):
    if trials < 3 or timeout_sec <= 0:
        raise ValueError('Use at least three repeats and a positive equal search budget')
    proofs = checked_bound_receipts(receipt_paths)
    source = ROOT / 'spectral_pruning/bitset_solvers.py'
    solver_hash = sha256(source)
    benchmark_hash = sha256(Path(__file__))
    data_dir = ROOT / 'spectral_pruning/dimacs_data'
    provenance = json.loads((data_dir / 'provenance.json').read_text())
    if instances and set(instances) - {entry['file'] for entry in provenance}:
        raise ValueError('Requested instance is absent from the authentic input manifest')
    rows = []
    for entry in provenance:
        if instances and entry['file'] not in instances:
            continue
        path = data_dir / entry['file']
        if sha256(path) != entry['sha256']:
            raise ValueError(f'Changed DIMACS input: {path}')
        graph = _parse_dimacs_clq(str(path))
        if (len(graph), graph.number_of_edges()) != (entry['n'], entry['m']):
            raise ValueError(f'Input topology disagrees with provenance: {path}')
        for ordering, solver_type in [('degree', BitsetBaselineSolver), ('perron', BitsetSpectralSolver)]:
            samples = {'disabled': [], 'enabled': []}
            trial_orders = []
            for trial in range(trials):
                order = (False, True) if trial % 2 == 0 else (True, False)
                trial_orders.append(['enabled' if flag else 'disabled' for flag in order])
                for enabled in order:
                    mode = 'enabled' if enabled else 'disabled'
                    size, witness, metrics = solver_type(enable_clique_bounds=enabled).solve(graph, timeout_sec)
                    validate_witness(graph, size, witness)
                    samples[mode].append({'trial': trial, 'incumbent': size, 'witness': witness,
                                          'witness_sha256': hashlib.sha256(json.dumps(witness).encode()).hexdigest(),
                                          **metrics.to_dict()})
            completed_optima = {sample['incumbent'] for ss in samples.values() for sample in ss if sample['completed']}
            if len(completed_optima) > 1:
                raise AssertionError(f'Completed searches disagree on {path.name}')
            optimum = next(iter(completed_optima)) if completed_optima else None
            if optimum is not None and any(s['incumbent'] > optimum for ss in samples.values() for s in ss):
                raise AssertionError(f'An incumbent exceeds a completed optimum on {path.name}')
            complete = all(sample['completed'] for ss in samples.values() for sample in ss)
            base_ms = statistics.median(s['runtime_ms'] for s in samples['disabled'])
            enabled_ms = statistics.median(s['runtime_ms'] for s in samples['enabled'])
            base_nodes = statistics.median(s['nodes_visited'] for s in samples['disabled'])
            enabled_nodes = statistics.median(s['nodes_visited'] for s in samples['enabled'])
            rows.append({'instance': path.name, 'provenance': entry, 'ordering': ordering,
                'trial_orders': trial_orders, 'completed_pair': complete, 'known_optimum_from_completed_search': optimum,
                'baseline_median_ms': base_ms, 'enabled_median_ms': enabled_ms,
                'baseline_median_nodes': base_nodes, 'enabled_median_nodes': enabled_nodes,
                'speedup_disabled_over_enabled': base_ms / enabled_ms if complete else None,
                'node_reduction_percent': 100 * (1 - enabled_nodes / max(1, base_nodes)) if complete else None,
                'exclusion_reason': None if complete else 'One or more searches timed out; no speedup or node-reduction claim',
                'samples': samples})
            print(path.name, ordering, 'completed:', complete,
                  'speedup:', rows[-1]['speedup_disabled_over_enabled'], flush=True)
    completed = [r for r in rows if r['completed_pair']]
    speedups = [r['speedup_disabled_over_enabled'] for r in completed]
    if solver_hash != sha256(source) or benchmark_hash != sha256(Path(__file__)):
        raise ValueError('Source changed during qualification; rerun against one immutable version')
    report = {'scope': 'Additional degree and exact integer edge-count bounds; identical bitset search and root ordering',
        'default_enabled': False, 'timeout_sec_per_solve': timeout_sec, 'trials': trials,
        'load_context': load_context,
        'trial_order': 'Alternating disabled/enabled order; all trials and preprocessing included',
        'solver_source_sha256': solver_hash, 'benchmark_source_sha256': benchmark_hash,
        'input_manifest_sha256': sha256(data_dir / 'provenance.json'),
        'checked_bound_proofs': proofs, 'environment': {'python': sys.version, 'platform': platform.platform(),
            'numpy': np.__version__, 'networkx': nx.__version__,
            'thread_environment': {name: os.environ.get(name) for name in
                ('OPENBLAS_NUM_THREADS', 'VECLIB_MAXIMUM_THREADS', 'OMP_NUM_THREADS')}},
        'summary': {'instance_ordering_pairs': len(rows), 'completed_pairs': len(completed),
            'excluded_timeout_pairs': len(rows) - len(completed),
            'geometric_mean_completed_speedup': statistics.geometric_mean(speedups) if speedups else None,
            'faster_completed_pairs': sum(value > 1 for value in speedups),
            'slower_or_equal_completed_pairs': sum(value <= 1 for value in speedups),
            'summed_median_time_ratio': sum(r['baseline_median_ms'] for r in completed) / sum(r['enabled_median_ms'] for r in completed) if completed else None},
        'results': rows,
        'limitations': ['Python search implementation is qualified by exhaustive small-graph replay, not itself formally verified.',
            'Formal receipts cover graph inequalities; bitmask/candidate translation is checked empirically.',
            'This is a bounded local experiment; timings and submillisecond ratios are environment-dependent.',
            'Incomplete searches are retained and excluded from comparative performance summaries.',
            'Known foundational inequalities and their use do not establish mathematical or algorithmic novelty.']}
    atomic_save_json(report, Path(output_dir) / 'clique_bounds_dimacs.json')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'runs/clique_bounds')
    parser.add_argument('--receipt', action='append', type=Path, default=[])
    parser.add_argument('--timeout', type=float, default=2.0)
    parser.add_argument('--trials', type=int, default=3)
    parser.add_argument('--instance', action='append')
    parser.add_argument('--load-context', default='Not recorded',
                        help='Concurrent workloads or quiet-window conditions for timing provenance')
    parser.add_argument('--oracle-only', action='store_true')
    parser.add_argument('--benchmark-only', action='store_true')
    args = parser.parse_args()
    if args.oracle_only and args.benchmark_only:
        parser.error('Choose one qualification mode or run both')
    if not args.benchmark_only:
        run_oracle_qualification(args.output_dir)
    if not args.oracle_only:
        report = run_paired_dimacs(args.output_dir, args.receipt, args.timeout, args.trials,
                                   args.instance, args.load_context)
        print(json.dumps(report['summary'], indent=2), flush=True)


if __name__ == '__main__':
    main()
