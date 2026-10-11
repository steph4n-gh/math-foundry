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

The `certifiedResearch` Lake package in `certified_lean` exports the `MathFoundry` library. It uses Lean **4.34.1** and the same pinned Mathlib revision as the archive. Create a separate project with these three files; no Python installation or model account is needed.

`lean-toolchain`:

```text
leanprover/lean4:v4.34.1
```

`lakefile.lean`:

```lean
import Lake
open Lake DSL

package myResearch

require certifiedResearch from git
  "https://github.com/steph4n-gh/math-foundry.git" @ "main" / "certified_lean"

@[default_target]
lean_lib MyResearch
```

`MyResearch.lean`:

```lean
import MathFoundry.Foundations

namespace MyResearch

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact MathFoundry.archetype_chi_ge_omega G

end MyResearch

#print axioms MyResearch.clique_bound
```

With [Elan](https://github.com/leanprover/elan#installation) installed, run from your new project:

```sh
lake update
lake exe cache get
lake build
lake env lean MyResearch.lean
```

The final command prints the consumer theorem's transitive axioms. The permitted set is `propext`, `Classical.choice` and `Quot.sound`. Dependency setup downloads upstream sources and Mathlib caches. `lake update` records the exact resolved Git revisions in your `lake-manifest.json`; commit that lockfile and replace `"main"` with the resolved Math Foundry commit for a fixed dependency. Keep the pinned Lean version when using this snapshot. Git dependencies with a package subdirectory follow the [official Lake syntax](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).

The eight foundation exports retain their existing theorem names: `MathFoundry.archetype_chi_ge_omega`, `MathFoundry.archetype_brooks_standard`, `MathFoundry.archetype_spectral_wilf`, `MathFoundry.mcclelland_graph_energy_upper`, `MathFoundry.cvetkovic_signless_laplacian_max_deg`, `MathFoundry.chung_normalized_laplacian_gap_upper`, `MathFoundry.parity_code_unique_neighbor_distance` and `MathFoundry.parity_code_dimension_le_order`. Their [explanations and premises](../results/README.md#useful-starting-points) still apply; the historical Brooks identifier denotes the standard greedy bound.

For all 341 targets, change the first line to `import MathFoundry`. Each is available as `MathFoundry.Archive.<theorem_name>.<theorem_name>`, with its checked prerequisites isolated in that same namespace. Raw catalog IDs containing punctuation use the catalog's sanitized `theorem_name`. To import only one artifact, use its module `MathFoundry.Archive.<theorem_name>`.

The [library manifest](../certified_lean/MathFoundry/manifest.json) maps every original ID to its module, qualified theorem, original source/challenge hashes and generated-module hash. It is a packaging record; it does not grant originality or replace fresh kernel verification. Complete statements and guards remain in the [result catalog](../results/catalog.json).

[ImportFoundry.lean](../examples/ImportFoundry.lean) is a separate consumer example used by CI. CI clones the checked commit as an actual Lake dependency, builds the complete library, compiles this consumer and audits all 341 target axioms, all eight exported names and the consumer theorem. This adds no new research result to the snapshot count.

## Maintain the packaging

Archived proof and challenge bytes stay unchanged. Generated modules retain the exact import prefix and complete theorem body, adding only an enclosing namespace and provenance comment. After intentionally updating the archive, regenerate and check the package:

```sh
python scripts/package_lean_library.py
python scripts/package_lean_library.py --check
```

The check validates the whole catalog's exact source/challenge/AST/guard bindings and every generated file. It invokes neither Lean nor AI. Fresh compilation and axiom checks are separate gates. The original [standalone reuse example](../examples/ReuseCliqueBound.lean) remains available for examining one archived proof without the library.

## Contribute a useful improvement

Good small contributions include a clearer theorem explanation, a reproducible counterexample, a useful consumer example, or an exact comparison with a readable primary theorem. Provide complete premises and keep failed checks visible. See [CONTRIBUTING.md](../CONTRIBUTING.md).
