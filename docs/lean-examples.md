# Build on the Lean library

These examples turn existing Math Foundry results into small certificates you can
use in another Lean project. They require no Python or model account. The complete
source is [ImportFoundry.lean](../examples/ImportFoundry.lean); it imports the
published library and defines the reusable theorems and their three concrete
applications in the `FoundryConsumer` namespace.
They are illustrations of known mathematics, not additional research discoveries.
The Lean snippets below are declarations copied from that source and belong
inside `namespace FoundryConsumer`; use the complete file when trying them.

## Set up a consumer project

Follow the [three-file Lake setup](using-proofs.md#reuse-in-your-own-lean-project),
using Lean **4.34.1** and the locked Mathlib revision. Save
[ImportFoundry.lean](../examples/ImportFoundry.lean) as `MyResearch.lean` in that
project, replacing the guide's short example, then run:

```sh
lake update
lake exe cache get
```

For these examples, change its first import from `import MathFoundry` to
`import MathFoundry.Foundations`. Only the eight foundation modules are needed.
Prebuild them serially to keep the first build small and avoid starting competing
Lean compilers:

```sh
for proof_name in archetype_chi_ge_omega archetype_brooks_standard \
  archetype_spectral_wilf mcclelland_graph_energy_upper \
  cvetkovic_signless_laplacian_max_deg chung_normalized_laplacian_gap_upper \
  parity_code_unique_neighbor_distance parity_code_dimension_le_order; do
  lake build "certifiedResearch/+MathFoundry.Archive.$proof_name:olean" || exit 1
done
lake build "certifiedResearch/+MathFoundry.Foundations:olean"
lake build
```

Keep the generated `lake-manifest.json` and pin the resolved Math Foundry commit
in your Lake dependency for reproducibility. You can import a single archive
module instead when your project uses only one bound. The
[reuse guide](using-proofs.md#reuse-in-your-own-lean-project) explains individual
imports and the full collection.

## Rule out a proposed coloring

Suppose your graph contains a clique larger than the proposed number of colors.
`FoundryConsumer.coloring_obstruction` turns that lower-bound certificate into
the statement that no proper coloring with that many colors exists:

```lean
theorem no_three_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclique : 3 < G.cliqueNum) : ¬ G.Colorable 3 := by
  exact coloring_obstruction G 3 hclique
```

The reusable proof combines `MathFoundry.archetype_chi_ge_omega` with Mathlib's
bound on the chromatic number of a colorable graph. You still supply a Lean proof
of `hclique`: a numerical estimate or an unverified list of vertices cannot fill
that premise. This is useful for verifying a lower-bound certificate produced by
a separate search.

## Certify an exact chromatic number

If the clique lower bound and the greedy degree upper bound meet, their common
value is the exact chromatic number. The example accepts both structural facts
explicitly:

```lean
theorem four_colors_from_matching_bounds {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclique : G.cliqueNum = 4) (hdegree : G.maxDegree + 1 = 4) :
    G.chromaticNumber.toNat = 4 := by
  exact chromatic_number_from_matching_bounds G 4 hclique hdegree
```

This pattern avoids a separate proof about the chromatic number once the two
certificates are available. It determines the number; it does not return a color
assignment. The archive's historical `archetype_brooks_standard` name denotes
the greedy bound **χ ≤ Δ + 1**, not the sharper Brooks theorem.

## Bound a binary adjacency-code dimension

For a graph with at most `budget` vertices, its adjacency-matrix kernel over
`ZMod 2` has dimension at most `budget`. The example converts the archive's
real-valued inequality into a natural-number certificate that is convenient for
index sizes and resource limits:

```lean
theorem sixteen_vertex_dimension_budget (G : SimpleGraph (Fin 16))
    [DecidableRel G.Adj] :
    Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
      ≤ 16 := by
  exact adjacency_code_dimension_budget G 16 (by simp)
```

Here the code is exactly `ker(A(G))` over GF(2), with vertices indexing both matrix
axes. A different incidence matrix or Tanner-graph construction needs its own
definitions and proofs. The theorem bounds dimension; it does not certify
distance, decoding performance or a code construction. For finite codewords and
erasure recovery, see the separate [four-cycle walkthrough](adjacency-code-example.md).

## Check what your new theorem depends on

Append these commands to the consumer source and run `lake env lean MyResearch.lean`:

```lean
#print axioms FoundryConsumer.clique_bound
#print axioms FoundryConsumer.coloring_obstruction
#print axioms FoundryConsumer.chromatic_number_from_matching_bounds
#print axioms FoundryConsumer.adjacency_code_dimension_budget
#print axioms FoundryConsumer.no_three_coloring
#print axioms FoundryConsumer.four_colors_from_matching_bounds
#print axioms FoundryConsumer.sixteen_vertex_dimension_budget
```

CI builds the exact Git dependency, compiles this source, and checks every one of
these reports. The permitted transitive axioms are `propext`, `Classical.choice`
and `Quot.sound`; `sorryAx` or an additional axiom fails verification. Keep full
premises in your own extensions and audit their axioms too. Compilation and
formal reuse establish correctness under the displayed assumptions, while
[originality](originality-frontier.md) requires a separate comparison.
