# Five proofs to read and build on

These walkthroughs explain five results from the [341-proof snapshot](../results/README.md). Each applies to **every finite simple undirected graph**: there is no connectivity, regularity or nonempty-graph premise. The Lean declarations use a finite vertex type `V`, decidable vertex equality and decidable adjacency. These are known mathematical results, presented as reusable checked proofs, not discoveries.

Write `n` for the number of vertices, `m` for the number of undirected edges, `Δ` for maximum degree, `ω` for maximum clique size and `χ` for chromatic number. The Lean statements use `G.chromaticNumber.toNat`; finite graphs have a finite chromatic number. Let `A` be the real adjacency matrix, `ρ` its largest eigenvalue, and `E = Σᵢ |λᵢ(A)|` its spectral energy. Eigenvalues are counted with multiplicity; the archive sets `ρ=0` for the vertexless graph.

Each section links to the exact target in both its unchanged proof source and its importable archive module. The module's qualified declaration is `MathFoundry.Archive.<name>.<name>`; the eight foundations also have shorter `MathFoundry.<name>` exports.

## Clique versus coloring

**Statement:** `ω ≤ χ`. Any proper coloring gives different colors to every pair of vertices in a clique, so a clique of size four rules out a three-coloring.

The retained proof directly reuses Mathlib's `G.cliqueNum_le_chromaticNumber`. Mathlib represents the chromatic number with extended naturals; the source uses its finite vertex-count bound to justify conversion to a natural number, then casts the inequality to reals. It does not independently implement a clique search.

Use this as a certified lower bound, as in the [coloring-obstruction example](lean-examples.md#rule-out-a-proposed-coloring). You still provide a proof that your graph has the required clique.

[Lean proof](../results/proofs/9c811cc19988fc3c8cfaf48a9f85fa1461ca632847cdac0b138dafbc2e1a79ad.lean#L12) · [Importable target](../certified_lean/MathFoundry/Archive/archetype_chi_ge_omega.lean#L18)

## Greedy coloring

**Statement:** `χ ≤ Δ + 1`. A vertex has at most `Δ` neighbors, so among `Δ+1` colors at least one is available when extending a coloring.

The embedded helper `generative_chromatic_degree_pilot` proves this by induction on finite vertex sets. It counts neighbor colors using Mathlib's finite-set lemmas, chooses a missing color and extends the partial coloring. Mathlib then converts the resulting colorability witness into a chromatic-number bound. The final archived target reuses that helper.

The historical name `archetype_brooks_standard` denotes this **greedy bound**, not the sharper Brooks theorem. Combine it with a matching clique lower bound to [certify an exact chromatic number](lean-examples.md#certify-an-exact-chromatic-number).

[Lean proof](../results/proofs/8c8654240c0f7fd70f3dc854ad434f91d356998d59c422a1988c80782ad5ccfb.lean#L55) · [Importable target](../certified_lean/MathFoundry/Archive/archetype_brooks_standard.lean#L61)

## Wilf's spectral coloring bound

**Statement:** `χ ≤ ρ + 1`, the Wilf spectral coloring bound.

The proof uses Mathlib's orthonormal eigenbasis to show `xᵀAx ≤ ρ‖x‖²`. Applying this to a vertex-set indicator bounds the sum of its induced degrees by `ρ` times its size. Every nonempty vertex set therefore contains a vertex with induced degree at most `ρ`.

If `χ > ρ+1`, set `k=χ−1`. Repeatedly remove such a vertex, color the remaining set with `k` colors and restore it using an available color. This produces a coloring with fewer than `χ` colors, a contradiction. The empty graph is handled separately. This is a spectral argument followed by a coloring construction, not just an invocation of a preexisting Wilf theorem.

A spectral upper bound can be combined with a clique lower bound using the same [matching-bounds pattern](lean-examples.md#certify-an-exact-chromatic-number).

[Lean proof](../results/proofs/73070a86f8b8be27dba056bd0f1f4147ec63686ae2a191bbc03d0feb6a6d46cf.lean#L99) · [Importable target](../certified_lean/MathFoundry/Archive/archetype_spectral_wilf.lean#L105)

## McClelland's energy bound

**Statement:** `E ≤ √(2mn)`, the McClelland energy bound. It supplies an upper estimate from two simple graph counts without needing every eigenvalue individually.

The checked helper proves `Σᵢ λᵢ² = tr(A²) = 2m`, using Mathlib's spectral theorem, trace identities and degree-sum theorem. Cauchy–Schwarz gives `E² ≤ n Σᵢ λᵢ² = 2mn`; the final target takes square roots. Earlier regular-graph lemmas in the file add no premise to this result.

Here “energy” means adjacency spectral energy, not a measured physical quantity. For extensions, follow the [consumer axiom-checking pattern](lean-examples.md#check-what-your-new-theorem-depends-on).

[Lean proof](../results/proofs/2715a679aa18d9420bab1ba6ef86b952f310fe3d03220cb80fd858b89667a2fc.lean#L232) · [Importable target](../certified_lean/MathFoundry/Archive/mcclelland_graph_energy_upper.lean#L238)

## Binary adjacency-code dimension

**Statement:** `dim C(G) ≤ n`, where `C(G)=ker A(G)` over GF(2). Variables and parity checks are separate copies of the vertices; this is the square adjacency-check construction.

The kernel is a subspace of the binary coordinate space `V → ZMod 2`. The proof directly uses Mathlib's `Submodule.finrank_le` and `Module.finrank_fintype_fun_eq_card`, then casts the natural-number dimension inequality to reals. Unrelated coloring helpers retained earlier in the file are not used by this target.

The [dimension-budget example](lean-examples.md#bound-a-binary-adjacency-code-dimension) turns it into a natural-number bound for a 16-vertex graph. The theorem holds for all finite orders; the separate Python enumeration cap is 16. It does not establish distance, decoding performance or a useful code rate. The [four-cycle walkthrough](adjacency-code-example.md#what-the-graph-represents) shows a concrete code with dimension two.

[Lean proof](../results/proofs/777bd7350fe65b0bff26a45dbfd0148c3bfac6d2ad5178f482f2e0a38445b36e.lean#L40) · [Importable target](../certified_lean/MathFoundry/Archive/parity_code_dimension_le_order.lean#L46)

To try these results, follow the [Lean reuse guide](using-proofs.md#reuse-in-your-own-lean-project). Formal correctness and [mathematical originality](originality-frontier.md) remain separate questions.
