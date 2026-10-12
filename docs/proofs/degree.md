# Degree, density and triangles: proof explanations

[Back to the proof index](../../results/all-proofs.md#degree-density-and-triangles) · [All explanations](README.md)

Here **n** is vertex count, **m** edge count, **Δ** maximum degree, **δ** minimum
degree, and **T** triangle count. Average degree is 2m/n (zero for an empty
graph). **p** denotes edge density, 2m/[n(n−1)], defined as zero for n<2.
The archive’s historical formulas sometimes call density ρ; it is distinct
from the adjacency spectral radius. All graphs here are finite and simple.

These are informal explanations of the retained arguments. Use the linked
Lean theorem for exact premises and the index for its frozen originality
assessment. A short arithmetic consequence is still a useful checked lemma;
it is not evidence of a new discovery.

## degree_sum_density_bound

**Meaning.** Twice the edge count is at most the number of vertices times the largest degree: 2m ≤ nΔ. There is no connectivity or regularity assumption.

**Proof idea.** Every edge contributes two to the total degree. The proof replaces each vertex degree in that sum by the upper bound Δ, giving a sum of n copies of Δ, then converts the natural-number inequality to real numbers.

[Lean proof](../../results/proofs/109978ea304852ecfea4a12bd3f3876142e7a9af22a37801e8b6764d1535fe9e.lean#L25) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_ge_0_1_diameter_min_degree_0_is_bipartite_4065a324009b

**Meaning.** For a bipartite graph, the largest degree is at least the smallest degree. Bipartiteness is retained as a premise, although this proof does not use it.

**Proof idea.** Lean simplifies the claim with the general minimum-versus-maximum degree inequality. No spectral or diameter argument is needed; those words in the historical identifier do not add quantities to this target.

[Lean proof](../../results/proofs/bfca885b807131d242173c0f4716b143f5a7fde5b2fb9b9218589cf220650ba8.lean#L161) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_ge_0_1_order_density_0_is_regular_3887d517131d

**Meaning.** For a regular graph, maximum degree bounds edge density p. Here p is the fraction of available vertex pairs that are edges; it is not an adjacency eigenvalue.

**Proof idea.** For n < 2 density is defined as zero. Otherwise the degree sum gives 2m ≤ nΔ, and dividing by n(n−1) only makes that upper bound smaller because n−1 ≥ 1. The regularity premise is not needed by this argument.

[Lean proof](../../results/proofs/d1c4fc4749b243c669c71becc255a8b16f6234707955407b5aee618fe925666c.lean#L161) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_ge_1_0_min_degree_girth_0_is_regular_9277ab7750da

**Meaning.** For a regular graph, maximum degree is at least minimum degree. This is one direction of the equality of degrees in a regular graph.

**Proof idea.** The actual target is discharged by Lean’s general minimum-versus-maximum degree simplification. It does not need to unpack regularity or reason about girth, despite the historical identifier.

[Lean proof](../../results/proofs/ba21914dfe150723f3e45d79a14bb30d5b67578b77415133b34ab4d8315b7ad6.lean#L129) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_le_1_-1_order_density_0_is_regular_f85632d19957

**Meaning.** For a regular graph, Δ ≤ n−p, where p is edge density. The retained statement includes regularity; the proof obtains the inequality using facts valid for every finite simple graph.

**Proof idea.** A vertex has at most n−1 neighbors, and density is at most one. Combining Δ+1 ≤ n with p ≤ 1 yields the result. The proof treats n < 2 separately so the zero-density convention and natural-number subtraction are handled correctly.

[Lean proof](../../results/proofs/9d86787e28ad8d563e3ac9abc1325214e907482d65460cd58ef8b4f87167f114.lean#L126) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_le_1_0_min_degree_girth_0_is_regular_a8cd4d70ab45

**Meaning.** For a regular graph, maximum degree is at most minimum degree. Together with the reverse inequality, this says both equal the common degree.

**Proof idea.** The empty vertex type is handled separately. In the nonempty case the proof extracts the common degree from the regularity premise, rewrites both extrema to that degree, and closes the resulting equality.

[Lean proof](../../results/proofs/ca674905f20f2ab8f0ab15ba3ec224d7bbce04077dd73b6972f762a436ac4306.lean#L129) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a

**Meaning.** For a bipartite graph, maximum degree cannot exceed the total number of edges. The bipartite premise remains part of this artifact.

**Proof idea.** Each vertex’s incident edges are among all the graph’s edges, so each degree is at most m. Lean applies that bound to the maximum degree and casts the result to real numbers. The argument itself does not require bipartiteness.

[Lean proof](../../results/proofs/95cf174539bbae4b61227f6502d27d558c3e6f89d93ca513801d4f64f8c2a721.lean#L195) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_order_ge_-1_2_density_average_degree_1_is_tree_39f653f393cf

**Meaning.** For a tree, the number of vertices bounds the combination 2 times average degree minus density plus one. Density here is p, not spectral radius.

**Proof idea.** The tree identity m=n−1 reduces the expression to (5n−6)/n. Orders one and two are evaluated directly; for n≥3 the remaining inequality follows from the nonnegative product (n−2)(n−3). This is arithmetic using the tree edge count.

[Lean proof](../../results/proofs/a402415e81b9cc0b7d275588e48347f3695e7dd9fcf18177fe707df5ccab81f0.lean#L30) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_order_ge_-3_3_density_average_degree_1_is_tree_f65c2da0bfec

**Meaning.** For a tree, n ≥ 3 times average degree minus 3 times density plus one. This relates three size statistics under the tree premise.

**Proof idea.** Substituting m=n−1 reduces the right side to (7n−12)/n. The proof checks orders one, two and three explicitly, then uses (n−3)(n−4) ≥ 0 for n≥4. It clears only denominators proved positive.

[Lean proof](../../results/proofs/1af8b8c45bec9048f048dc9402cca2ac1874833ef7e73b2fc5199f09c01dddcf.lean#L57) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_order_ge_-6_4_density_average_degree_1_is_tree_180d33acce2c

**Meaning.** For a tree, n ≥ 4 times average degree minus 6 times density plus one. The density is p=2m/[n(n−1)] with the small-order convention.

**Proof idea.** The tree edge count turns the right side into (9n−20)/n. Order one is handled directly. For integer n≥2, (n−4)(n−5) is nonnegative: n is either at most four or at least five. Clearing the positive denominator gives the result.

[Lean proof](../../results/proofs/e9d8fd397479a036c5acca38ca0838e3cb56b8e34c85262670d3ad75dd1a4364.lean#L57) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_order_le_1_0_size_estrada_index_1_is_connected_982287c31193

**Meaning.** Every connected finite graph has at least n−1 edges, equivalently n ≤ m+1. Connectivity is essential to the retained statement.

**Proof idea.** The target uses Mathlib’s connected-graph vertex-count bound. Lean rewrites the finite edge-set cardinality into the stored edge count and casts the natural-number inequality to real numbers. It does not use an Estrada-index estimate.

[Lean proof](../../results/proofs/c330e97cf8545d0ba7d47d47c1eb62f7c1d7f2cc517afbc18721b83c129f216c.lean#L30) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull3d_size_ge_1_0_max_degree_normalized_laplacian_spectral_gap_0_is_connected_9b83028c151a

**Meaning.** For a connected graph, edge count is at least maximum degree. Connectivity is included in this artifact, though this argument works without it.

**Proof idea.** For every vertex, the incident edges form a subset of the graph’s edges. Lean bounds each degree by m, transfers that bound to the maximum, and casts it. No normalized Laplacian calculation is used in the target.

[Lean proof](../../results/proofs/523454a4e68368ece49f2e4f448be80b15d2835c0a6521f86297694e8209516c.lean#L144) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull_density_le_0_max_degree_1_0c030c3b90f0

**Meaning.** Edge density is at most one for any finite simple graph. The displayed maximum-degree term has coefficient zero and contributes nothing.

**Proof idea.** Density is zero when n<2. Otherwise each degree plus one is at most n; summing gives 2m+n ≤ n², or 2m ≤ n(n−1). Division by that positive denominator establishes p ≤ 1.

[Lean proof](../../results/proofs/0798d204d0c45ff1e4a2b5db28c29abbae6d3e64e23833bf806d483caf71f32b.lean#L161) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull_density_le_0_min_degree_1_13d2302d7d68

**Meaning.** Edge density is at most one. This is a second artifact for the same conclusion, with a zero-coefficient minimum-degree term.

**Proof idea.** The proof counts possible unordered vertex pairs: m ≤ n choose 2. It converts that count to 2m ≤ n(n−1), proves the density denominator positive for n≥2, and divides. Smaller orders use the defined zero density.

[Lean proof](../../results/proofs/1d66193e92720dac72fcaf66fba50077e66672c89e0e343e32c50bbb931cab75.lean#L5) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull_density_le_1_max_degree_0_f5fbcb14104c

**Meaning.** For any finite simple graph, density p is at most maximum degree Δ. Both are nonnegative, but they measure different things.

**Proof idea.** For n<2 the result is immediate. Otherwise the degree sum gives 2m ≤ nΔ; multiplying the right side by n−1≥1 preserves the bound. Dividing by n(n−1) produces the desired density inequality.

[Lean proof](../../results/proofs/6eaa7064fbbb6b39a67a0bb9061e1c17372077bc7acf96922bb95db709c53090.lean#L161) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull_density_le_1_sqrt_max_degree_0_b7a2501e7c1f

**Meaning.** For any finite simple graph, edge density is at most the square root of maximum degree. This is a loose size bound rather than a spectral theorem.

**Proof idea.** Small orders have zero density. If Δ=0 the graph has no edges. Otherwise Δ is an integer at least one, hence √Δ≥1, while counting possible neighbors gives p≤1. Combining those inequalities proves the target.

[Lean proof](../../results/proofs/cb20b649e15b9f2279216dc8219d0629a06714cf4306e69e2e0b11e2b8396177.lean#L161) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## hull_min_degree_le_1_average_degree_0_36a8fb326490

**Meaning.** Minimum degree is at most average degree, with average degree defined as zero for the empty graph.

**Proof idea.** The empty graph is simplified directly. For nonempty graphs every degree is at least δ; summing yields nδ ≤ 2m. The proof establishes n>0, divides by it, and obtains δ ≤ 2m/n.

[Lean proof](../../results/proofs/cdae4f994a38f95d02ae664d7dea6aed5e28b40955dae333e48772885a7fdd34.lean#L5) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## model_5d619440ee288c0ae37f

**Meaning.** For connected graphs with Δ≥2, the number of triangles is bounded above with a correction for how far total degree falls short of nΔ. The exact expression is in the index.

**Proof idea.** A triangle through a vertex uses a pair of its neighbors, so 3T ≤ Σ choose(degree(v),2). Each degree lies between δ and Δ; the nonnegative product (degree−δ)(Δ−degree) bounds those pair counts. Summing and using Σ degree=2m yields the displayed correction.

[Lean proof](../../results/proofs/bd9984ce9490cfcc655e8f5358fe11120613eb15d89e3f6c424ca4a03c8e7c02.lean#L14) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## model_8371fb8fc2bcba3921ce

**Meaning.** For graphs with n≥2, a triangle lower bound includes an extra nonnegative term measuring the difference between maximum and average degree. It is informative only when its right side is positive.

**Proof idea.** Counting common neighbors across oriented edges gives Σ degree² ≤ nm+3T. Choose a maximum-degree vertex and apply Cauchy–Schwarz to the other n−1 degrees, whose sum is 2m−Δ. Combining these facts and clearing positive denominators gives the squared deviation term.

[Lean proof](../../results/proofs/68e40858b79b081b94ca7303d78c4267659dd71da95d31bae6578858ef14c62a.lean#L677) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## model_a1f6745517cbad451a6c

**Meaning.** For a connected graph, T ≤ (Δ−1)(m−n+1). Thus the edges beyond a spanning tree limit how many triangles can occur.

**Proof idea.** Choose a spanning tree, which has n−1 edges and no triangle. Every graph triangle therefore contains an edge outside that tree. Each such edge lies in at most Δ−1 triangles, because its third vertex must be a neighbor of an endpoint other than the other endpoint. Counting this cover yields the bound, with zero-surplus cases treated separately.

[Lean proof](../../results/proofs/9aa11ca68c0e0cece833ca00bbc3224665261275a881bcffcd80e92910ec2b8a.lean#L678) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## model_bdf9be88d9b1c8373345

**Meaning.** Triangle count satisfies 3nT ≥ m(4m−n²) in every finite simple graph. If m is large enough to make the right side positive, the graph must contain triangles.

**Proof idea.** For each oriented edge, its endpoint degrees sum to at most n plus their number of common neighbors. Sum these inequalities: each triangle contributes at most six oriented-edge/common-neighbor triples, giving Σ degree² ≤ nm+3T. Cauchy–Schwarz and Σ degree=2m then give the target.

[Lean proof](../../results/proofs/5848350a0e9f2073ccc6e878a521741b9435b7c344da5b5662ef4510e9b50723.lean#L424) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)

## model_fadaed797ff612bf4d71

**Meaning.** For a triangle-free graph, m ≤ Δ(n−Δ). In a graph with no triangle, the neighbors of any one vertex cannot be adjacent to one another.

**Proof idea.** Every vertex neighborhood is therefore an independent set, giving α≥Δ; for the empty graph both are zero. The checked parent model_8ce30216566f34c2605a says m ≤ (n−α)Δ: the complement of a largest independent set meets every edge. Substitute α≥Δ and use Δ≥0 to finish.

[Lean proof](../../results/proofs/892b67fb8b08da3e3664cd8d3839861ecc4b010e1d5841b7620e3e71ecc55ded.lean#L97) · [Statement and assessment](../../results/all-proofs.md#degree-density-and-triangles)
