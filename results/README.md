# Browse the proof snapshot

**341 independently replayable Lean artifacts, frozen at checkpoint 275.** The collection includes known theorems, routine consequences and helpers. No original mathematical result is established.

Start with [using one proof](../docs/using-proofs.md) or the [small adjacency-code example](../docs/adjacency-code-example.md). Every archived proof includes its required checked parents. The [importable Lean library](../certified_lean/MathFoundry.lean) puts those contexts in separate namespaces so all 341 targets can coexist.

## Browse by subject

| Subject | Artifacts |
| --- | --- |
| [Adjacency codes and unique neighbors](all-proofs.md#adjacency-codes-and-unique-neighbors) | 107 |
| [Energy and Estrada index](all-proofs.md#energy-and-estrada-index) | 49 |
| [Coloring, cliques and independence](all-proofs.md#coloring-cliques-and-independence) | 72 |
| [Spectral bounds](all-proofs.md#spectral-bounds) | 91 |
| [Degree, density and triangles](all-proofs.md#degree-density-and-triangles) | 22 |

The [full index](all-proofs.md) preserves every complete rendered statement. The [JSON catalog](catalog.json) additionally records structured expressions, guards, source/challenge hashes and historical verification.

## Useful starting points

All eight below have a frozen **known-result** assessment; the collection is valuable as formalization and reproducible evidence.

### Greedy coloring

[archetype_brooks_standard](proofs/8c8654240c0f7fd70f3dc854ad434f91d356998d59c422a1988c80782ad5ccfb.lean)

$\forall G \in \mathcal{G}, \quad \chi(G) \le \Delta(G) + 1$

Every finite simple graph admits the standard maximum-degree-plus-one bound. The historical identifier is not a claim of the sharper Brooks theorem.

### Clique versus coloring

[archetype_chi_ge_omega](proofs/9c811cc19988fc3c8cfaf48a9f85fa1461ca632847cdac0b138dafbc2e1a79ad.lean)

$\forall G \in \mathcal{G}, \quad \chi(G) \ge \omega(G)$

A clique needs distinct colors. This is a small starting point for inspecting and reusing a proof.

### Wilf spectral coloring bound

[archetype_spectral_wilf](proofs/73070a86f8b8be27dba056bd0f1f4147ec63686ae2a191bbc03d0feb6a6d46cf.lean)

$\forall G \in \mathcal{G}, \quad \chi(G) \le \lambda_1(G) + 1$

Relates chromatic number to the adjacency spectral radius.

### McClelland energy bound

[mcclelland_graph_energy_upper](proofs/2715a679aa18d9420bab1ba6ef86b952f310fe3d03220cb80fd858b89667a2fc.lean)

$\forall G \in \mathcal{G}, \quad \mathcal{E}(G) \le \sqrt{2 \cdot m \cdot n}$

Bounds adjacency energy by the graph order and edge count.

### Signless Laplacian degree bound

[cvetkovic_signless_laplacian_max_deg](proofs/e089c248e2db5496e4e3b6d46348ca0e58aa19ffba82189b264f0db59fd24865.lean)

$\forall G \in \mathcal{G}, \quad q_1(G) \le 2 \cdot \Delta(G)$

Bounds the signless Laplacian spectral radius by twice the maximum degree.

### Normalized Laplacian gap bound

[chung_normalized_laplacian_gap_upper](proofs/676e7f2d85277cbf931e43edab01cb52de57e6003d5a2065d487b8d98b2f063d.lean)

$\forall G \in \mathcal{G}, \quad n \ge 2 \implies \lambda_2^{\mathcal{L}}(G) \le \frac{n}{n - (1)}$

Requires at least two vertices; retain that premise when reusing it.

### Unique neighbors and code distance

[parity_code_unique_neighbor_distance](proofs/fde0354b867d056aae097fff88d93a337f1d9e5eeb071b5a9404cc3e042f9e9a.lean)

$\forall G \in \mathcal{G}, \quad u_{\mathrm{adj}}(G) + 1 \le d_{\mathrm{adj}}(G)$

The binary adjacency-kernel distance is at least the unique-neighbor radius plus one. Zero-code sentinel conventions are part of the definition.

### Code dimension

[parity_code_dimension_le_order](proofs/777bd7350fe65b0bff26a45dbfd0148c3bfac6d2ad5178f482f2e0a38445b36e.lean)

$\forall G \in \mathcal{G}, \quad k_{\mathrm{adj}}(G) \le n$

The binary adjacency kernel is a subspace of the vertex-coordinate space, so its dimension is at most the graph order.

## Replay the theorem you choose

After the [pinned setup](../README.md#start-without-ai):

```sh
python scripts/replay_results.py --id archetype_chi_ge_omega \
  --timeout 60 --output runs/clique-replay.json
```

Repeat `--id` to select several theorems. The command validates every catalog binding before compiling the selected sources; it makes no AI requests. Use a fresh report path on each run. Challenge files intentionally contain unproved placeholders and should not be compiled as proof sources.

## Read assessments separately

The frozen snapshot contains **27 known results, 54 routine consequences and 260 awaiting review**. Automated assessments are provisional and expert review is pending. Fresh kernel replay establishes correctness of the exact statement under its declared premises; it does not settle mathematical priority. See the [investigated routine comparisons](originality-notes.md) and [negative results](../docs/negative-results.md).
