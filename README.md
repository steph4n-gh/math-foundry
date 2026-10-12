# Math Foundry

[![Verify engine and proof snapshot](https://github.com/steph4n-gh/math-foundry/actions/workflows/verify.yml/badge.svg)](https://github.com/steph4n-gh/math-foundry/actions/workflows/verify.yml)

**Read a theorem. Understand the argument. Reuse its Lean proof.**

Math Foundry publishes **341 checked Lean 4 proof artifacts** about finite simple
graphs and binary adjacency codes. The collection includes known theorems,
helpers, specializations and routine consequences. No original mathematical
result is established. You can read and use the proofs without an AI account.

## Start with a proof

Here are five entry points, with explanations and direct links to the theorem
declarations. For a graph, **n** counts vertices, **m** counts edges, **χ** is the
chromatic number, **ω** the largest clique size, **Δ** the maximum degree and
**ρ** the adjacency spectral radius.

| Result | What it tells you | Read the argument | Read the Lean proof |
| --- | --- | --- | --- |
| **χ ≥ ω** | A clique forces its vertices to have different colors. | [Clique versus coloring](docs/proof-walkthroughs.md#clique-versus-coloring) | [Proof](certified_lean/MathFoundry/Archive/archetype_chi_ge_omega.lean#L18) |
| **χ ≤ Δ + 1** | Maximum degree gives a guaranteed coloring upper bound. | [Greedy coloring](docs/proof-walkthroughs.md#greedy-coloring) | [Proof](certified_lean/MathFoundry/Archive/archetype_brooks_standard.lean#L61) |
| **χ ≤ ρ + 1** | The adjacency spectrum also bounds the number of colors. | [Wilf's spectral bound](docs/proof-walkthroughs.md#wilfs-spectral-coloring-bound) | [Proof](certified_lean/MathFoundry/Archive/archetype_spectral_wilf.lean#L105) |
| **E ≤ √(2mn)** | Edge count and graph order bound adjacency energy E. | [McClelland's energy bound](docs/proof-walkthroughs.md#mcclellands-energy-bound) | [Proof](certified_lean/MathFoundry/Archive/mcclelland_graph_energy_upper.lean#L238) |
| **k ≤ n** | The binary adjacency kernel has dimension at most n. | [Code dimension](docs/proof-walkthroughs.md#binary-adjacency-code-dimension) | [Proof](certified_lean/MathFoundry/Archive/parity_code_dimension_le_order.lean#L46) |

**[Read the five walkthroughs →](docs/proof-walkthroughs.md)**

The walkthroughs explain the notation, assumptions, proof ideas and their
connections to the actual Lean source. The coloring bound above is the standard
greedy bound; its historical source name does not claim the sharper Brooks theorem.

## Browse the whole collection

Every entry in the full index now links to a **plain-English explanation** of
its meaning and actual proof argument, alongside the statement, assessment and
Lean source. Conditional results keep their premises.

| Subject | Open the proofs | Artifacts |
| --- | --- | --- |
| Coloring, cliques and independence | [Browse](results/all-proofs.md#coloring-cliques-and-independence) | 72 |
| Spectral bounds | [Browse](results/all-proofs.md#spectral-bounds) | 91 |
| Energy and Estrada index | [Browse](results/all-proofs.md#energy-and-estrada-index) | 49 |
| Adjacency codes and unique neighbors | [Browse](results/all-proofs.md#adjacency-codes-and-unique-neighbors) | 107 |
| Degree, density and triangles | [Browse](results/all-proofs.md#degree-density-and-triangles) | 22 |

**[All 341 statements, explanations and proofs →](results/all-proofs.md)** ·
[Browse all explanations](docs/proofs/README.md) ·
[Eight foundation results explained](results/README.md#useful-starting-points) ·
[Machine-readable catalog](results/catalog.json)

## Build something with the proofs

The [practical examples](docs/lean-examples.md) show three ways to use the library:

- [Rule out a proposed three-coloring](docs/lean-examples.md#rule-out-a-proposed-coloring) using a certified clique bound.
- [Certify an exact chromatic number](docs/lean-examples.md#certify-an-exact-chromatic-number) when lower and upper bounds meet.
- [Bound a binary adjacency-code dimension](docs/lean-examples.md#bound-a-binary-adjacency-code-dimension) for a graph on 16 vertices.

Their complete, checked source is [ImportFoundry.lean](examples/ImportFoundry.lean).
For a numerical example you can run, the
[four-cycle walkthrough](docs/adjacency-code-example.md) constructs codewords and
tests erasure recovery, while distinguishing those finite checks from universal proofs.

### Import into your Lean project

Use Lean **4.34.1** and add this Lake dependency:

```lean
require certifiedResearch from git
  "https://github.com/steph4n-gh/math-foundry.git" @ "main" / "certified_lean"
```

Then use a checked result directly:

```lean
import MathFoundry.Foundations

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact MathFoundry.archetype_chi_ge_omega G
```

**[Complete project files and setup commands →](docs/using-proofs.md#reuse-in-your-own-lean-project)**

Lean reuse requires no Python or model account. `MathFoundry.Foundations` exports
eight starting results; `import MathFoundry` imports all 341 targets. Individual
archive modules are also available. The
[manifest](certified_lean/MathFoundry/manifest.json) maps catalog IDs to imports and
qualified theorem names. Pin the resolved Math Foundry commit and retain your
Lake lockfile for reproducibility. Mathlib is pinned to
**d13f23b723b8a846827a245b89c10fc7d3f11612**.

## What has been checked

This is a frozen **checkpoint 275** snapshot from **2026-10-11**. All 341 artifacts
had passing saved independent replays at that boundary. The
[successful Linux verification](https://github.com/steph4n-gh/math-foundry/actions/runs/38182698567)
also built the importable library, checked a separate consumer project and audited
the exported targets' axioms. The badge above links to the latest GitHub CI status.

Certification checks the exact statement, declared premises and proof against
genuine pinned dependencies. Permitted transitive axioms are `propext`,
`Classical.choice` and `Quot.sound`; `sorryAx` and additional axioms fail the checks.
It does not establish originality or certify an accompanying numerical experiment
or explanation. The frozen assessments are **27 known results, 54 routine
consequences and 260 awaiting review**, with expert review pending.

To reproduce the checks, follow the
[exact-source replay guide](docs/using-proofs.md#replay-the-exact-retained-bytes).
For the limits of the research claims, see
[investigated routine comparisons](results/originality-notes.md),
[negative results](docs/negative-results.md) and [publication scope](docs/publication.md).
No general discovery-rate advantage or completed 24-hour release qualification
has been established.

## The research engine

The repository also contains the experimental system used to propose graph/coding
inequalities, search for counterexamples and attempt Lean proofs. Its seven
campaigns, deterministic examples and optional model-assisted setup are in the
[engine guide](docs/running-engine.md). Finite survivors remain candidates; each
universal claim needs its own checked proof. There is no automatic synchronization
between this public snapshot and private research.

## Contribute or reuse

Read [CONTRIBUTING.md](CONTRIBUTING.md) for reproducible changes and mathematical
review expectations. Original project code, documentation and newly authored
proof scripts use [Apache-2.0](LICENSE). Upstream components and literature retain
their own terms; see [third-party notices](THIRD_PARTY_NOTICES.md).

Full papers, private traces, runtime state, DIMACS data bytes, dependency trees
and toolchains are excluded from this publication.
