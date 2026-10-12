# Four supplemental generated proofs, explained

[All explanations](README.md) · [Supplemental source corpus](../../library/generated/README.md)

These four retained model-generated sources supplement the main frozen
[341-artifact index](../../results/all-proofs.md); they are not four additional
exports from `import MathFoundry`. Their catalog records historical kernel
checks and independent replays. They prove known mathematics, not new discoveries.

All four concern finite simple graphs. Here **χ** is chromatic number, **Δ**
maximum degree, **α** independence number, **n** vertex count and **m** edge count.
Each explanation follows the actual target body. Linked proof files include
checked prerequisites; challenge files contain intentional placeholders and
are not the proofs.

## generative_chromatic_degree_pilot

**Meaning.** Every finite simple graph can be colored with at most Δ+1 colors. This gives a guaranteed upper bound even when finding an optimal coloring is difficult. No connectivity, regularity or nonempty-graph premise is required.

**Proof idea.** The proof constructs a coloring one finite vertex set at a time. After coloring the smaller set, it considers the colors currently assigned to the new vertex’s neighbors. There are at most Δ such colors, so one of Δ+1 colors is unused. Giving the new vertex that color preserves proper coloring. Applying the construction to all vertices and converting the coloring witness yields the bound. The retained synthesis history includes an initial rejected attempt followed by this accepted repair.

[Lean proof](../../library/generated/proofs/f2e50fbabed138112f1e02070ee1a304c5f3f3015b3e059b0456f9216b824fc1.lean#L5) · [Historical provenance and assessment](../../library/generated/catalog.json)

## pilot_bipartite_two_colors

**Meaning.** A bipartite graph needs at most two colors: vertices on one side can use one color and vertices on the other side the second.

**Proof idea.** In this formalization the bipartite premise is already `G.Colorable 2`, a witness of a proper two-coloring. The target converts that witness into an upper bound on the chromatic number, then casts the natural-number inequality to reals. It does not build a partition from an odd-cycle characterization. This is a short example of preserving and using a structural premise in a generated proof.

[Lean proof](../../library/generated/proofs/3111cf7351031dcd8aa1a48d1bdae9cc10dc1c4d24f96975d6336708bbe900e0.lean#L20) · [Historical provenance and assessment](../../library/generated/catalog.json)

## pilot_independence_le_order

**Meaning.** An independent set cannot have more vertices than the graph: α≤n. There is no graph-property premise.

**Proof idea.** The formal independence number is the clique number of the complement graph: vertices with no edges between them in G are pairwise adjacent in its complement. The target applies the retained clique-size bound `composed_2cd2dd810fbb9720` to that complement. That parent combines “a clique needs distinct colors” with “one color per vertex suffices,” giving clique size ≤ vertex count. Taking the complement changes adjacency, not the vertex type, so the same n bounds α.

[Lean proof](../../library/generated/proofs/e3febcf8bf907c8a0294447029cbcea16e0db1e3a2ef8b5a5a4da59fbea37af8.lean#L94) · [Historical provenance and assessment](../../library/generated/catalog.json)

## model_e679ce9c7fa60e2c7bfd

**Meaning.** If a finite simple graph needs χ colors, it must have at least χ(χ−1)/2 edges. This lets an edge budget limit how many colors could be necessary. No connectivity or regularity premise is required.

**Proof idea.** Start with an optimal coloring and form a graph whose vertices are its colors; join two colors when an original edge connects them. This color graph must be complete: otherwise two nonadjacent color classes could be merged, contradicting optimality. Every oriented edge of the color graph has an original oriented edge mapping to it, so its edge count is at most m. The checked parent `clique_edges_density_bound` gives χ(χ−1)≤2 times that complete graph’s edge count, which finishes the argument. The greedy-coloring helper earlier in this source is not used by the target.

[Lean proof](../../library/generated/proofs/5062e8b1c67dc97af3397ffffc6edb836e619942d83f240398f014cff6f3f831.lean#L145) · [Historical provenance and assessment](../../library/generated/catalog.json)
