# Find, replay and reuse one proof

The [subject index](../results/README.md) is the starting point for the 341-proof snapshot. Each entry has an exact target, complete premises, independently replayable source and a separate originality assessment. You can use known mathematics without claiming it is a new discovery.

## Choose a statement

Start with `archetype_chi_ge_omega`, the familiar clique-versus-coloring inequality:

$$\omega(G) \le \chi(G).$$

It applies to every finite simple graph. The [Lean source](../results/proofs/9c811cc19988fc3c8cfaf48a9f85fa1461ca632847cdac0b138dafbc2e1a79ad.lean) quantifies over a finite vertex type with decidable equality and adjacency. Its chromatic number uses Mathlib's natural-valued conversion; a finite coloring bound in the context ensures that this conversion is appropriate.

The frozen assessment is **known result**, and expert review remains pending. Its value here is an inspectable, reusable formal proof.

For machine-readable searching, Python's standard library is enough; no package installation or model account is needed:

```sh
python3 - <<'PY'
import json
from pathlib import Path
needle = "graph_energy"
for row in json.loads(Path("results/catalog.json").read_text())["records"]:
    if needle in json.dumps(row["conjecture"]):
        print(row["id"], row["statement_latex"], row["source_path"], sep="\n")
        print()
PY
```

Change the search term to an invariant such as `chromatic_number`, `spectral_radius` or `parity_code_distance`. Inspect `guard_predicate` as well as the displayed inequality; connectivity, nonzero dimension and order restrictions matter.

## Replay the exact retained bytes

Complete the [Python and pinned Lean setup](../README.md#start-without-ai), then run from the repository root:

```sh
python scripts/replay_results.py --id archetype_chi_ge_omega \
  --timeout 60 --output runs/clique-replay.json
```

The command first validates the complete catalog's source/challenge hashes and native AST-rendered targets, including every guard. It then compiles the selected source against genuine pinned Mathlib and checks the final target's transitive axioms. `propext`, `Classical.choice` and `Quot.sound` are the permitted set; extra axioms fail the check.

Repeat `--id` to select several theorems. Repeated IDs are replayed once, in catalog order. Unknown IDs and an empty selection fail. If you combine IDs with sharding, the IDs must belong to that original catalog-position shard; `--limit` applies after selection.

Each report records the selected IDs, exact hashes, compiler identity, durations, failures and axiom reports. A successful binding-only `--check-only` report is not a fresh kernel replay. Use a fresh output filename each time; reports are never overwritten. These commands invoke no AI provider.

## Reuse in your own Lean project

Archived sources are standalone compilation units. Each embeds its checked prerequisites, so importing all 341 files together can redeclare shared names. The current `certified_lean` package pins dependencies but does not expose a combined `lean_lib` target.

For one theorem, retain the complete source and add your consumer theorem in a separate namespace. [ReuseCliqueBound.lean](../examples/ReuseCliqueBound.lean) contains the unchanged clique-bound source followed by this small use:

```lean
namespace MathFoundryExamples

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact archetype_chi_ge_omega G

end MathFoundryExamples
```

Compile the example using the prepared workspace:

```sh
cd certified_lean
lake env lean ../examples/ReuseCliqueBound.lean
```

The file ends with `#print axioms MathFoundryExamples.clique_bound`. This example only reuses the existing bound; it adds no mathematical result to the snapshot count.

When combining results in a larger project, reconcile duplicate prerequisites and put declarations in appropriate namespaces. Keep the archived proof bytes and provenance unchanged, then independently compile and inspect the axioms of your adapted module. A compact namespaced library with an external import example is a useful next contribution; the present archive does not promise that packaging yet.

## Contribute a useful improvement

Good small contributions include a clearer theorem explanation, a reproducible counterexample, a namespaced module for a few checked results, or an exact comparison with a readable primary theorem. Provide complete premises and keep failed checks visible. See [CONTRIBUTING.md](../CONTRIBUTING.md).
