# Math Foundry

Math Foundry proposes graph inequalities, searches for counterexamples, and attempts proofs against genuine pinned Lean and Mathlib. It stores exact statements, guards, proof sources and verification evidence so others can inspect, replay and build on the work.

This public snapshot contains **341 Lean-certified proof artifacts from checkpoint 275**, frozen on 11 October 2026. All had passing saved independent replays at that boundary. The count includes known results, helpers, specializations and routine consequences; **no mathematical originality is established**. Fresh replay on your machine is a separate check. The project remains a research prototype, with no established general discovery-rate advantage or completed 24-hour release qualification.

## Start without AI

Use Python 3.11 or newer on macOS or Linux. Work from the checkout root; the Lean workspace is separate from the Python package.

```sh
git clone https://github.com/steph4n-gh/math-foundry.git
cd math-foundry
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e .
python scripts/replay_results.py --check-only --output runs/catalog-check.json
```

`--check-only` checks the published catalogue and artifact bindings. It does not invoke Lean or establish a fresh kernel replay. These commands make no AI requests and need no Codex account.

For kernel replay, install [Elan](https://github.com/leanprover/elan#installation), then prepare the pinned workspace:

```sh
"$HOME/.elan/bin/elan" toolchain install leanprover/lean4:v4.34.1
cd certified_lean
"$HOME/.elan/bin/lake" exe cache get
cd ..
python scripts/replay_results.py --limit 3 --timeout 60 --output runs/replay-first3.json
```

Lean is pinned to **4.34.1** and Mathlib to **d13f23b723b8a846827a245b89c10fc7d3f11612**. Dependency setup downloads upstream packages and build caches; replay uses the local compiler. Omit `--limit` for the full corpus. `--shard-index 0 --shard-count 4` selects one of four disjoint shards; `--output` saves a report. Use a fresh report path when repeating a command; existing reports are never overwritten. A timeout is an unresolved replay, not a disproof.

Browse [results/catalog.json](results/catalog.json) for each exact structured statement and its source/challenge bindings, and the [investigated originality notes](results/originality-notes.md) for three routine comparisons. The frozen assessments comprise 27 known results, 54 routine consequences and 260 awaiting review; automated labels are preserved as provisional metadata. Sources contain their required checked parents. Companion challenges describe exact targets; compile the proof sources through the replay script rather than treating challenge placeholders as proofs.

## Explore locally

A small deterministic run needs no AI account:

```sh
python -B run_research.py --continuous --max-iterations 1 \
  --proof-backend none --model-candidates 0 --max-lean-targets 0 \
  --limit-per-pair 2 --limit-per-triad 2 --timeout-sec 60 \
  --output-dir runs/offline-demo
python -B dashboard.py --output-dir runs/offline-demo --port 8050
```

Open <http://127.0.0.1:8050/>. Use a fresh output directory for an independent run and the same directory to resume it. Only complete batches become committed checkpoints. The frozen public corpus is separate from a new run's initial library.

## Optional model-assisted research

Install and authenticate the [Codex CLI](https://developers.openai.com/codex/cli/) using your own account before selecting `--proof-backend codex`. Model generation and the background originality reviewer consume that account's allowance. Replay and deterministic exploration do not require them.

For a bounded first experiment:

```sh
python -B run_research.py --continuous --campaign spectral \
  --max-iterations 1 --timeout-sec 300 --workers 1 \
  --proof-backend codex --model-candidates 1 --max-lean-targets 1 \
  --model-rounds 1 --model-request-timeout 120 \
  --output-dir runs/model-demo
```

Model and effort follow your CLI configuration unless explicitly supplied. The request and run deadlines are time ceilings, not token or billing caps. Proof, proposal and review requests have separate accounting. Keep failures and missing usage visible when comparing experiments.

## Mathematical scope

| Campaign | Investigated quantities |
| --- | --- |
| `spectral` | Adjacency and Laplacian spectra, algebraic connectivity, coloring and independence bounds |
| `advanced_spectral` | Signless and normalized Laplacian quantities, energy, Estrada index and nonlinear envelopes |
| `extremal_coloring` | Chromatic number, degrees, cliques and supported graph premises |
| `independence_clique` | Independence, clique number, order and edge count |
| `metric_topological` | Diameter, radius, girth, triangles and density |
| `chemical_energy` | Adjacency energy, Estrada index and spectral spread |
| `expander_codes` | The binary adjacency kernel over GF(2), dimension, distance and unique neighbors |

These are seven graph/coding campaigns. Empirical breadth exceeds the trusted formal grammar: diameter, radius and girth currently have no accepted scalar Lean translation. Binary-code numerical checks are exact only through order 16. Unsupported cases remain unresolved.

A finite survivor is a candidate. Certification requires the exact rendered target, genuine pinned dependencies and permitted transitive axioms (`propext`, `Classical.choice`, `Quot.sound`). It does not certify numerical screening, generated exposition, external paper interpretations or originality. Read the [originality workflow](docs/originality-frontier.md), [spectral comparison rules](docs/spectral-refinements.md), [negative results](docs/negative-results.md) and [publication scope](docs/publication.md).

## Reuse and contributions

Original project code, documentation and newly authored proof scripts are licensed under [Apache-2.0](LICENSE). Upstream components and literature retain their own terms; see [third-party notices](THIRD_PARTY_NOTICES.md). Full papers, private traces, runtime state, DIMACS data bytes, dependency trees and toolchains are excluded. This is a frozen publication snapshot, with no automatic synchronization to private research.

See [CONTRIBUTING.md](CONTRIBUTING.md) for reproducible changes and mathematical-review expectations.
