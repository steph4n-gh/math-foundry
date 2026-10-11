"""Maximum-clique comparisons on hashed published inputs, with ordering controls."""
from __future__ import annotations
import hashlib,json,itertools,random,statistics
from pathlib import Path
from spectral_pruning.bitset_solvers import BitsetBaselineSolver,BitsetSpectralSolver,_parse_dimacs_clq
from autonomous_math.research_state import atomic_save_json
ROOT=Path(__file__).resolve().parent.parent

class ControlSolver(BitsetSpectralSolver):
    def __init__(self,seed=None):
        super().__init__();self.seed=seed
    def _compute_perron_ordering(self,g,mapping):
        order=list(range(len(mapping)))
        if self.seed is not None:random.Random(self.seed).shuffle(order)
        return order

def run_dimacs_benchmark(timeout_sec=10.0,trials=3,instances=None,output_dir=None):
    directory=ROOT/'spectral_pruning/dimacs_data'
    provenance=json.loads((directory/'provenance.json').read_text())
    rows=[]
    for entry in provenance:
        if instances is not None and entry['file'] not in instances:continue
        path=directory/entry['file'];payload=path.read_bytes()
        if hashlib.sha256(payload).hexdigest()!=entry['sha256']:raise ValueError(f'Changed benchmark input: {path}')
        graph=_parse_dimacs_clq(str(path))
        if (graph.number_of_nodes(),graph.number_of_edges())!=(entry['n'],entry['m']):raise ValueError(f'Invalid benchmark header: {path}')
        measurements={}
        for name,factory in [('degree',BitsetBaselineSolver),('perron',BitsetSpectralSolver),('stable',ControlSolver)]+[(f'random_{seed}',lambda seed=seed:ControlSolver(seed)) for seed in range(3)]:
            samples=[]
            for _ in range(trials):
                size,witness,metrics=factory().solve(graph,timeout_sec)
                if size!=len(witness) or len(set(witness))!=size or not all(graph.has_edge(u,v) for u,v in itertools.combinations(witness,2)):
                    raise ValueError(f'Invalid clique witness from {name}')
                samples.append({'incumbent':size,'witness':witness,**metrics.to_dict()})
            completed=all(s['completed'] for s in samples)
            measurements[name]={'completed':completed,'optimal_size':samples[0]['incumbent'] if completed else None,
                'median_ms':statistics.median(s['runtime_ms'] for s in samples),'samples':samples}
        optima={r['optimal_size'] for r in measurements.values() if r['completed']}
        if len(optima)>1:raise ValueError(f'Completed solvers disagree on {path}')
        all_complete=all(r['completed'] for r in measurements.values())
        rows.append({'instance':entry['file'],'provenance':entry,'measurements':measurements,
            'all_complete':all_complete,'speedup':measurements['degree']['median_ms']/max(1e-9,measurements['perron']['median_ms']) if all_complete else None,
            'optimal_size':next(iter(optima)) if optima else None})
        print(entry['file'],'all completed:',all_complete,'optimum:',rows[-1]['optimal_size'],flush=True)
    atomic_save_json(rows,Path(output_dir or ROOT/'spectral_pruning/benchmark_results')/'qualified_dimacs.json')
    return rows

if __name__=='__main__':run_dimacs_benchmark()
