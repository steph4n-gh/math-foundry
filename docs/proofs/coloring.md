# Coloring, cliques and independence

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

These informal explanations cover the 72 results in this part of the [full proof index](../../results/all-proofs.md#coloring-cliques-and-independence). They explain the retained sources; they are not certificates and do not change the frozen assessments.

All graphs are finite, simple, and undirected. Write χ for chromatic number, ω for maximum clique size, α for maximum independent-set size, n for vertex count, m for undirected edge count, Δ for maximum degree, δ for minimum degree, and T for triangle count. In Lean, α is the clique number of the complement and χ uses the finite value of `chromaticNumber.toNat`. A proper coloring gives adjacent vertices different colors. “Regular” means all vertices have one common degree; the bipartite premise in these sources is an explicit proper two-coloring.

Write d̄=2m/n for average degree, set to zero when n=0; r for the largest eigenvalue of adjacency matrix A; q₁ for the largest eigenvalue of the signless Laplacian D+A; and µ₂ for the second-smallest eigenvalue of the ordinary Laplacian D−A, where D is the diagonal degree matrix. The sources set r and q₁ to zero when n=0. Write p=2m/[n(n−1)] for edge density, set to zero when n<2. The index renderer sometimes uses ρ for both density and adjacency spectral radius; the explanations distinguish them by following the actual Lean expression. Integer-valued premises with thresholds just above or below an integer are described by their equivalent integer bounds. Decimal coefficients are exact rationals in Lean; the links retain their precise values.

## archetype_brooks_standard

**Meaning.** Every finite simple graph can be properly colored with at most Δ+1 colors. Thus a graph of maximum degree four needs no more than five colors, including when it has several components. The historical theorem name here denotes this greedy bound.

**Proof idea.** The embedded helper builds colorings by induction on finite vertex sets. Neighbor colors occupy at most Δ places in a palette of Δ+1 colors, so one color remains available for the newly inserted vertex. It extends the coloring and converts that witness into a bound on χ. The final target reuses the helper.

[Lean proof](../../results/proofs/8c8654240c0f7fd70f3dc854ad434f91d356998d59c422a1988c80782ad5ccfb.lean#L55) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## archetype_chi_ge_omega

**Meaning.** A clique requires a different color for each of its vertices, so ω≤χ for every finite simple graph. A clique of size four, for example, rules out any proper coloring using only three colors. There are no connectivity or nonempty-graph premises.

**Proof idea.** The source directly applies Mathlib’s clique-number lower bound for chromatic number. It also uses χ≤n to establish that the extended-natural chromatic number is finite. This justifies conversion to an ordinary natural number, followed by a cast of the inequality to the real numbers used in the statement.

[Lean proof](../../results/proofs/9c811cc19988fc3c8cfaf48a9f85fa1461ca632847cdac0b138dafbc2e1a79ad.lean#L12) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## archetype_ramsey_chi_alpha

**Meaning.** For a graph with at least one vertex, χ≥n/α: a proper coloring must have enough independent color classes to cover every vertex. The source’s threshold just below one is equivalent to n≥1 because n is an integer.

**Proof idea.** Take a coloring with χ colors and collect the vertices of each color. Each class is a clique in the complement, so its size is at most α. A fiber-counting identity sums the class sizes to n, giving n≤χα. The proof casts this count to reals and applies a division inequality; the declared guard is not needed by that final argument.

[Lean proof](../../results/proofs/d501f144a401bd934c0ac46744ab4ca6f395667959ab5e29f8f96f2572108ccc.lean#L256) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## archetype_spectral_wilf

**Meaning.** Every finite simple graph satisfies χ≤r+1, where r is the largest adjacency eigenvalue, taken as zero for the vertexless graph. This connects the number of colors to a spectral quantity rather than directly to maximum degree.

**Proof idea.** An orthonormal eigenbasis gives xᵀAx≤r‖x‖². Vertex-set indicator vectors show that every nonempty induced vertex set has a vertex of induced degree at most r. If χ exceeded r+1, repeatedly removing such a vertex and restoring it with an available color would construct a coloring with χ−1 colors. The empty graph is treated separately.

[Lean proof](../../results/proofs/73070a86f8b8be27dba056bd0f1f4147ec63686ae2a191bbc03d0feb6a6d46cf.lean#L99) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## chromatic_le_order

**Meaning.** A graph on n vertices can be colored with at most n colors. Assigning a separate color to each vertex always works, whether or not the graph is connected. The bound also covers the vertexless graph, whose chromatic number is zero.

**Proof idea.** The proof uses Mathlib’s chromatic-number bound by the cardinality of the vertex type. Because its upper bound is a finite natural number, the extended-natural inequality can be converted to an ordinary natural-number inequality. The last step casts both sides to reals, matching the archived statement.

[Lean proof](../../results/proofs/dfa8e9aa62928ad38607dd4c8f777217c8667fd6cbb4193b37062304df537824.lean#L5) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## clique_edges_density_bound

**Meaning.** A maximum clique already accounts for at least ω(ω−1)/2 edges, expressed here as ω(ω−1)≤2m. This gives an edge-count obstruction to a large clique and applies even when the graph has vertices outside that clique.

**Proof idea.** Choose a clique of size ω. For each vertex in it, deleting that vertex leaves ω−1 neighbors, giving a degree lower bound. Sum these bounds over the clique, then enlarge the sum to all vertices using nonnegative degrees. The degree-sum identity identifies the total as twice the number of undirected edges.

[Lean proof](../../results/proofs/d5edc340a5254cfb6b965330c445ceea26b638da6a43764e446eb12eb1f740e3.lean#L63) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## clique_le_max_degree_plus_one

**Meaning.** Every finite simple graph satisfies ω≤Δ+1. A clique of size k forces each of its vertices to have at least k−1 neighbors, so maximum degree alone limits its size. The statement also includes the vertexless graph.

**Proof idea.** The proof chooses a maximum clique and splits on whether it is nonempty. In the nonempty case, erase one chosen vertex: all remaining clique vertices lie in its neighbor set. Comparing cardinalities and bounding that vertex’s degree by Δ gives the result. An empty maximum clique has size zero and is handled by arithmetic.

[Lean proof](../../results/proofs/3d0ed77fed9eb05fec363b447e8e7f384cf2f8cce90fb8765dbba2a82e1f4ebd.lean#L38) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_04950e5f807d8d18

**Meaning.** The largest clique has size at most r+1, with r the largest adjacency eigenvalue and the empty-graph convention described above. This transfers a spectral upper bound for coloring to an upper bound for clique size.

**Proof idea.** The source chains two checked inequalities. First, the clique-versus-coloring parent says ω≤χ because clique vertices need distinct colors. Second, the spectral coloring parent proves χ≤r+1 by a quadratic-form estimate followed by a vertex-removal coloring construction. Transitivity gives the requested inequality directly, with no extra graph premise.

[Lean proof](../../results/proofs/dfd664a5d98780352fd75c52e22fdf5dbb804c6e1ac687aea40e1cdfb00ea32a.lean#L176) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_1f689b2150941b00

**Meaning.** Every finite simple graph satisfies ω≤m+1. Thus the total edge count supplies a simple, though often loose, upper bound on the number of vertices in a clique. No connectivity or regularity assumption is required.

**Proof idea.** The proof chains ω≤χ with the checked coloring bound χ≤m+1. That coloring parent first bounds every vertex’s degree by the total number of edges, obtaining Δ≤m, and then applies the greedy bound χ≤Δ+1. The target itself is just transitivity of those inequalities.

[Lean proof](../../results/proofs/1140183d246a2596df115383957c600764256b7aecf69438d153b26b18645b8f.lean#L70) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_2cd2dd810fbb9720

**Meaning.** A clique cannot contain more vertices than the graph, expressed as ω≤n. The archived proof establishes this through coloring inequalities rather than by directly comparing the clique vertex set with the full vertex set.

**Proof idea.** It loads two checked parents: χ≤n, supplied by assigning distinct colors to vertices, and ω≤χ, since clique vertices require distinct colors. Linear arithmetic combines the inequalities into ω≤n. Both parents apply to all finite simple graphs, so this target has no connectivity, regularity, or nonempty-graph premise.

[Lean proof](../../results/proofs/4dac2d29aacf1ba9aa9f827ef20d8bdb1802ea819f2c0dc4d3f855c03d51c336.lean#L20) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_2d2bb804bd98be4f

**Meaning.** Every finite simple graph satisfies ω≤m/10+11/2. This is a linear estimate of clique size from the edge count, with an intercept that allows the same statement to cover graphs with very few edges.

**Proof idea.** The source chains ω≤χ with the checked coloring estimate χ≤m/10+11/2. That parent maps an optimal coloring to a complete graph on χ color labels, counts its edges, and obtains χ(χ−1)≤2m. The fact that the integer χ lies outside the interval between 10 and 11 makes the needed quadratic product nonnegative, yielding the linear estimate.

[Lean proof](../../results/proofs/018b0a28db0872081e85bf66bd99cb2b8e84851417456c92f7a584859b050c86.lean#L85) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_523e52793bb52ffb

**Meaning.** The chromatic number is at most α+m. The bound uses the largest independent-set size together with the total number of edges, and holds for every finite simple graph, including one with no vertices.

**Proof idea.** Two checked parents supply χ≤n and n≤α+m. For the second, choose one endpoint from every edge. There are at most m chosen vertices, and the vertices left over form an independent set, so their number is at most α. The target combines the two inequalities by transitivity; it does not construct a new coloring.

[Lean proof](../../results/proofs/fb13e8964903823c29edcff0b70a0c89da4cf1e726ec0b12c17e2453bc83b872.lean#L53) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_5b68d6860ef6baca

**Meaning.** Every finite simple graph satisfies ω≤α+m. A large independent set and the edge count together give an upper budget for clique size. The result has no graph-class premise and includes the empty graph.

**Proof idea.** The proof uses ω≤n and n≤α+m. The first parent chains clique-versus-coloring with the vertex-count coloring bound. The second selects one endpoint per edge, leaving an independent set after the selected vertices are removed. Its count proves n≤α+m. Transitivity then gives the displayed clique estimate.

[Lean proof](../../results/proofs/b9dd57ea5a0461371fe6fa44b2f1bc4ac44c35223a6677cdeb3989320981c430.lean#L63) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_b214f1e86200a2e1

**Meaning.** The quadratic clique count is bounded by the maximum-degree budget: ω(ω−1)≤nΔ. This measures how many ordered pairs a maximum clique forces relative to the sum of n degree upper bounds.

**Proof idea.** The source collects several checked clique, coloring, and degree inequalities and invokes polynomial arithmetic. The decisive chain is ω(ω−1)≤2m≤nΔ: a maximum clique forces the first edge count, and summing degree(v)≤Δ over all vertices gives the second. The additional loaded parents give ω≤Δ+1 and ω≤χ≤n; nonnegativity supports the arithmetic step.

[Lean proof](../../results/proofs/3f3d1a0c27d82cdef9129b5414ab84db31d8d37203cc110c09cf0359e1277243.lean#L95) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_d02339f02f9fade4

**Meaning.** Every finite simple graph satisfies ω≤m/8+9/2. This gives another linear estimate for maximum clique size from the total edge count, without requiring a minimum-degree or graph-class hypothesis despite the generated name.

**Proof idea.** The target chains ω≤χ with the checked bound χ≤m/8+9/2. The coloring parent maps an optimal coloring onto its color-label graph, proves that graph complete, and counts edges to get χ(χ−1)≤2m. Integer χ is either at most 8 or at least 9, so (χ−8)(χ−9) is nonnegative and supplies the linear conclusion.

[Lean proof](../../results/proofs/6a2a79b3b272c49087c8e999ad2b093e7f1efa5baad42028f93abbce4fe247a0.lean#L85) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## composed_ef727e745e60525c

**Meaning.** Every finite simple graph satisfies χ(χ−1)≤nΔ. A need for many colors therefore imposes a lower requirement on the product of vertex count and maximum degree. The result includes disconnected and vertexless graphs.

**Proof idea.** The target is an explicit chain of two checked bounds. The coloring-edge parent maps an optimal coloring to a complete graph on χ labels and shows its edge count cannot exceed m, proving χ(χ−1)≤2m. The degree-sum parent sums degree(v)≤Δ and uses the handshaking identity to obtain 2m≤nΔ. Transitivity finishes.

[Lean proof](../../results/proofs/492d09f8f89fb8c8772fb6034fb5275295babc5b033418fce1e31d33126f7abb.lean#L202) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_ge_3_-1_average_degree_size_0_is_regular_c63a1b194af4

**Meaning.** For a regular graph, χ≥3d̄−m. Regularity means every vertex has one common degree d, and for nonempty graphs this equals the average degree d̄. The bound retains that regularity premise and defines d̄ as zero for the vertexless graph.

**Proof idea.** The degree sum gives nd=2m, and every positive-degree graph needs at least two colors. When n≥6, 3d−m is nonpositive. The proof treats smaller orders separately using d<n and parity from nd=2m. When d=n−1 it proves the graph complete and uses χ=n; degree-zero and empty cases follow from nonnegativity.

[Lean proof](../../results/proofs/bfa027cdf859fd167e17485eac788c9a7d3890cbe7be176793ae050b60334d2d.lean#L20) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_le_0_0.125_min_degree_size_4.5_7567eb13d98d

**Meaning.** For every finite simple graph, χ≤m/8+9/2. Although the generated identifier mentions minimum degree, the actual conclusion uses only the edge count and has no minimum-degree premise.

**Proof idea.** Map an optimal χ-coloring to a graph on its χ color labels. Chromatic-number monotonicity forces this graph to be complete; every label-edge comes from an original edge. Counting complete-graph degrees yields χ(χ−1)≤2m. Cases χ≤1 are immediate. Otherwise χ is at most 8 or at least 9, making (χ−8)(χ−9) nonnegative; polynomial arithmetic gives the stated linear bound.

[Lean proof](../../results/proofs/4a07d90ccf778a0d583b88e5282817ce87c6c4b4b2a887d3d7a6c7611665498b.lean#L370) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_le_0_0.1_min_degree_size_5.5_47ced30dbf96

**Meaning.** For every finite simple graph, χ≤m/10+11/2. This is an edge-count estimate with no minimum-degree condition; the minimum-degree term in the historical identifier has coefficient zero in the actual statement.

**Proof idea.** The proof sends an optimal coloring to its color-label graph. Since that graph still needs χ colors on χ vertices, it is complete, and its edges are images of original edges. Hence χ(χ−1)≤2m. After handling χ≤1, integrality makes (χ−10)(χ−11) nonnegative. Combining that product with the quadratic edge count proves the linear estimate.

[Lean proof](../../results/proofs/64b811eb143bce533ef5595d0fc3a899107f7f92a9c33dafdac9bbd56c9beaa4.lean#L370) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_le_0_1_normalized_laplacian_spectral_gap_max_degree_1_is_connected_9348b37553d1

**Meaning.** A connected finite simple graph satisfies χ≤Δ+1. Connectivity is an explicit premise of this archived declaration, but the same greedy estimate is available without it. No normalized Laplacian quantity appears in the actual conclusion.

**Proof idea.** The source invokes the checked greedy coloring parent, which constructs a coloring with Δ+1 colors by extending finite partial colorings using a color absent from the neighbor colors. It then passes that inequality and standard nonnegativity facts to polynomial arithmetic. The connectivity hypothesis is not used in this deduction.

[Lean proof](../../results/proofs/dd004625e9ec550b817b1b61393644b8f2a640d5fd1a0d21dc995fa37b270ae4.lean#L62) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_le_0_1_radius_min_degree_1_is_regular_4c85f75f684a

**Meaning.** For a regular graph, χ≤δ+1. This is the greedy coloring estimate written with minimum degree, which equals maximum degree when all vertices have the same degree. The regularity premise remains part of the theorem.

**Proof idea.** Unpack the common degree d. For a nonempty vertex type, Mathlib identifies both Δ and δ with d; for the empty type the proof simplifies both to zero. It then rewrites the checked greedy helper χ≤Δ+1 using Δ=δ. Thus the change from maximum to minimum degree comes entirely from regularity.

[Lean proof](../../results/proofs/3ec2f2ce138c2c14932d52b892817637ecbd6ed009561e9aa57aa9a2059e4c1b.lean#L70) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_chromatic_number_le_1_0_average_degree_size_1_is_regular_a43a97392584

**Meaning.** For a regular graph, χ≤d̄+1. The common vertex degree equals the average degree when the graph is nonempty, while the statement sets d̄=0 for the vertexless graph. Regularity is a substantive premise of this version.

**Proof idea.** The empty case follows from χ≤n. Otherwise unpack the common degree d and sum all degrees to get nd=2m, hence d̄=d. Every degree is at most d, so Δ≤d. The checked greedy helper gives χ≤Δ+1; substituting the average-degree identity and combining these inequalities yields the result.

[Lean proof](../../results/proofs/9569ab8025e2a0a94994076c0d36dc90c37e377da0b6d1209cb33d60d9239cfb.lean#L66) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_ge_0_1_max_degree_chromatic_number_0_is_bipartite_ec9e10a80eea

**Meaning.** For a graph supplied with a proper two-coloring, ω≥χ. Together with the general reverse inequality, this says that its clique number and chromatic number agree. The source represents the bipartite premise by two-colorability.

**Proof idea.** The arithmetic step loads several checked bounds, but the equality parent χ=ω already supplies the needed conclusion. That parent handles the empty and edgeless cases separately. If an edge exists, its endpoints form a two-vertex clique; two-colorability gives χ≤2 and clique-versus-coloring gives ω≤χ, forcing equality. The target extracts the reverse inequality.

[Lean proof](../../results/proofs/0e04b896d0a9e9542b10850d27d4a9ab7ce7245dbeada23e612df96e9165fc0d.lean#L250) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_-1_1_order_size_3_is_connected_2016b11ea37b

**Meaning.** For a connected graph, ω≤m−n+3. The quantity m−n+1 counts edges beyond a spanning tree, so the bound limits clique size using that excess plus two. Connectivity is needed for the spanning-tree construction.

**Proof idea.** Choose a spanning tree and select one endpoint from each edge outside it. Give those selected vertices distinct new colors, and use the tree’s two-coloring on the rest. Any remaining edge is a tree edge, making this a proper coloring with at most two plus the number of extra edges. The tree has n−1 edges, so χ≤m−n+3; ω≤χ finishes.

[Lean proof](../../results/proofs/90fd1a0af39583b2f79db30d6e1ac616217952851a0b8e2207e9fe9bfb4a4cf7.lean#L19) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_0.0357143_0_triangle_count_radius_6_is_connected_ba575443a060

**Meaning.** For a connected graph, clique size is bounded by approximately T/28+6. The coefficient in the source is the exact rational corresponding to the recorded decimal, slightly above 1/28. The connectivity premise is retained, although the counting proof does not use it.

**Proof idea.** Every three-element subset of a maximum clique is a triangle, so choose(ω,3)≤T. An induction proves 28k≤choose(k,3)+168 for every natural k: small cases are checked directly, and later increments use choose(k,2)≥28. Applying this at ω gives the bound with coefficient 1/28; nonnegative T permits its slight increase to the recorded coefficient.

[Lean proof](../../results/proofs/fc3a1c0844b467e72be6dbbd7711e30d58eafd9ca12e469f716cfe6e959e0068.lean#L46) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_0.1_0_triangle_count_radius_4.66667_is_connected_4d92cb1e01e5

**Meaning.** For a connected graph, ω≤T/10 plus the recorded constant 4.666666666666667. That constant is an exact rational in Lean, slightly above 14/3. Connectivity stays in the declaration, though the proof establishes its triangle count without using it.

**Proof idea.** Three-element subsets of a maximum clique give choose(ω,3)≤T. Induction proves the stronger numerical estimate 10k≤choose(k,3)+40. It checks small k directly and then uses the binomial recurrence with choose(k,2)≥10. Therefore ω≤T/10+4, and arithmetic relaxes the constant to the one in the archived statement.

[Lean proof](../../results/proofs/3277ca91024dc0f0f85dfcef4af3c42824392aa99775f58ca05afc03c82f0df8.lean#L46) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_0_0.0416948_estrada_index_size_12.5_is_regular_cc3a4d4bc0d5

**Meaning.** For a regular graph, ω is at most about 0.04169484539605529m+12.5, with the exact rational coefficient in the linked statement. The actual formula uses only edge count; the identifier’s Estrada-index term has coefficient zero.

**Proof idea.** Unpack the common degree d. The clique-degree and clique-order parents give ω−1≤d and ω≤n; regularity supplies nd=2m. Thus ω(ω−1)≤2m. Adding the nonnegative square (64ω−1567)² yields a linear bound with coefficient 64/1535 and intercept 25/2. Because m is nonnegative, increasing that coefficient to the recorded rational preserves the inequality.

[Lean proof](../../results/proofs/8298379972ca6fb88f80107bc66fffcbcdd82561f0a24b9f533784309a6be902.lean#L142) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_0_0.1_estrada_index_size_9.1_is_regular_300bb35a749b

**Meaning.** For a regular graph, ω≤m/10+91/10. This linear clique estimate retains regularity as a premise. Its conclusion depends only on the edge count, despite the historical identifier also mentioning the Estrada index.

**Proof idea.** Write d for the common degree. The checked bounds ω≤Δ+1 and ω≤n give ω−1≤d and ω≤n, while the degree sum gives nd=2m. Multiplying these inequalities produces ω(ω−1)≤2m. Polynomial arithmetic combines this quadratic bound with the nonnegative square (2ω−21)² and obtains the displayed linear estimate.

[Lean proof](../../results/proofs/26e4a1b66b12a1b8a89703135becbdc7d473d57881628e4e1535afd7cdf1dec8.lean#L44) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_0_1_estrada_index_size_1_is_regular_281545d7bef9

**Meaning.** For a regular graph, ω≤m+1. Regularity is present in the declaration, but the argument actually proves this edge-count estimate for every finite simple graph. No Estrada-index quantity appears in the formula.

**Proof idea.** Every vertex degree is at most the total number of edges, since incident edges form a subset of the edge set. This gives Δ≤m. The checked clique-degree parent proves ω≤Δ+1 by counting the other vertices adjacent to a vertex in a maximum clique. Linear arithmetic combines the two inequalities; the regularity witness is unused.

[Lean proof](../../results/proofs/06ab4d3da060ac548ccba979fb1c3c3ddc741ddb4a805d1a67941b1850265acc.lean#L44) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_clique_number_le_1_0_triangle_count_radius_2_is_connected_cd22e0a14a95

**Meaning.** For a connected graph, ω≤T+2. Thus a clique larger than two requires triangles, and the total triangle count controls the excess. Connectivity remains in the source declaration but is not used in the proof.

**Proof idea.** Choose a maximum clique; all its three-element subsets lie in the graph’s triangle set, giving choose(ω,3)≤T. A natural-number induction shows k≤choose(k,3)+2. The first cases are checked explicitly; subsequent steps use the binomial recurrence and choose(k,2)≥1. Apply this estimate to ω and cast the resulting count to reals.

[Lean proof](../../results/proofs/02790a89aeb1f0d27d0669b23a0d1b9e0088242e8b6571b346521e800cd8679e.lean#L85) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_ge_0.125_-0.00784314_average_degree_size_0_0828eb27ee4f

**Meaning.** Every graph satisfies α≥d̄/8−cm, where c is the recorded exact rational approximately 0.00784313725490196. The empty-graph convention sets d̄=0. This is a weak numerical lower bound supported largely by the existence of a one-vertex independent set.

**Proof idea.** For nonempty graphs, α≥1. Counting degrees gives 2m≤n². Splitting at n=32 and using a nonnegative square proves d̄≤8+m/16. Dividing by eight bounds d̄/8−m/128 by one. The recorded penalty coefficient is at least 1/128, so nonnegative m and α≥1 finish. The empty case uses only nonnegativity.

[Lean proof](../../results/proofs/0e02c2e1ce1e54ae8e34206b391a2373423a1fe8a785d518ea33d5965cb6cb8d.lean#L13) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_ge_0.1_-0.00511509_average_degree_size_0_7b2e86994adb

**Meaning.** Every graph satisfies α≥d̄/10−cm, with the exact recorded rational c approximately 0.005115089514066497. Average degree is zero for the vertexless graph. A nonempty graph’s independent singleton supplies the lower bound used in the proof.

**Proof idea.** Count ordered adjacent pairs to obtain 2m≤n². Splitting at n=40 and using n(n−20)²≥0 establishes d̄/10−m/200≤1. The recorded coefficient c is larger than 1/200, so its subtraction only lowers the right side. Combine this with α≥1 for nonempty graphs; the empty branch follows from nonnegative α and m.

[Lean proof](../../results/proofs/dea59f572fe09c31291a5c34e58dd9d6e947fc45ba95f79dcea359bf4f19d881.lean#L13) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_ge_2_-1_average_degree_size_0_9f3e4d10bb4b

**Meaning.** Every finite simple graph satisfies α≥2d̄−m, with d̄=0 for the vertexless graph. The expression on the right can become nonpositive, so the proof separates large vertex counts from the few small cases where a positive bound matters.

**Proof idea.** For n≥4, 2d̄=4m/n≤m, and α≥0 suffices. For nonempty orders one, two, and three, use α≥1 and the possible edge counts m≤choose(n,2), namely zero, one, and three. Direct arithmetic verifies each case. The empty graph is handled separately using nonnegativity.

[Lean proof](../../results/proofs/548bb871f9c90fe5c5752b615c324347c055a8e95adbcb29a3cd5e2a7b17e037.lean#L13) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_le_-1_1_max_degree_order_0_is_regular_171db394fb55

**Meaning.** For a regular graph, α≤n−Δ. An independent set and the full neighborhood of any one of its vertices must be disjoint, and regularity ensures that chosen vertex has the maximum degree.

**Proof idea.** The empty vertex type is simplified first. Otherwise choose a maximum independent set, represented as a maximum clique in the complement, and take one of its vertices. None of that vertex’s neighbors can belong to the set. The union therefore has α+d vertices and lies inside V. The common degree d equals Δ, so α+Δ≤n; rearranging gives the result.

[Lean proof](../../results/proofs/83c917acef5d08c81fe01f738c850f7bfc56a2192ae6365b30f98e775e399885.lean#L13) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_le_1_-1_order_clique_number_1_is_regular_4dc3b3af73f6

**Meaning.** For a regular graph, α≤n−ω+1. Equivalently, the sizes of a maximum clique and a maximum independent set total at most n+1. The proof does not use regularity, although the archived declaration retains it.

**Proof idea.** Choose both maximum sets. Their intersection has at most one vertex: two distinct shared vertices would be adjacent because of the clique and nonadjacent because of independence. The union has at most n vertices. Inclusion-exclusion then gives α+ω≤n+1, and a real-number cast and arithmetic rearrange it to the stated bound.

[Lean proof](../../results/proofs/1c9b9684e92dfc764083ee5e7e32bdc0d7cdcf9e6df4957d6c2c3fb0f2fb3713.lean#L28) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d

**Meaning.** A regular graph has α≤n, since an independent set consists of vertices from the graph. Regularity is a stated premise of this declaration, even though the bound holds without it and includes the vertexless graph.

**Proof idea.** The source invokes the checked independence-versus-order parent and passes the resulting inequality, together with standard nonnegativity facts, to polynomial arithmetic. That parent applies ω≤n to the complement graph; a clique in the complement is an independent set in the original, and complementing preserves the vertex type. No regularity fact enters the deduction.

[Lean proof](../../results/proofs/1ed37be5bf210b5c2b31ad1aaa6de6d2a25cfda007794c1cad7959fd8b264097.lean#L28) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_max_degree_ge_0_1_size_chromatic_number_-1_is_bipartite_5d0243263afc

**Meaning.** For a graph supplied with a proper two-coloring, Δ≥χ−1. This is the greedy upper bound for chromatic number rearranged to place maximum degree on the left. Two-colorability is a declared premise, though this particular consequence holds for every finite simple graph.

**Proof idea.** The proof loads Δ≥δ, the checked neighborhood estimate Δ≤α+T, and the greedy bound χ≤Δ+1. Polynomial arithmetic gives the target directly from the greedy bound. That parent builds colorings by choosing a color absent from the neighbors when extending a partial coloring; the two-coloring premise is unnecessary for this final rearrangement.

[Lean proof](../../results/proofs/ae746f69fd316494fc5c111c475cd2c327b981f6c8dc924c762bd8167fd9f87f.lean#L144) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_max_degree_le_0.2_2_size_independence_number_0_is_regular_9061eecc7f21

**Meaning.** For a regular graph, Δ≤m/5+2α. The edge count and independent-set size together bound the common degree. Regularity is essential to the degree-count identity used here, and the empty graph is handled separately.

**Proof idea.** For a nonempty d-regular graph, Δ=d, n≥d+1, and nd=2m, giving d(d+1)≤2m. Also α≥1. Because d is an integer, it is either at most four or at least five, so (d−4)(d−5)≥0. Polynomial arithmetic combines these facts to obtain the displayed estimate. Empty-graph maximum degree is zero.

[Lean proof](../../results/proofs/5244f820dcc711de9ff2819785ec8464bc32cabe601f0cdddfda9be99f31bf4e.lean#L295) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull3d_max_degree_le_1_1_independence_number_clique_number_-2_is_tree_9f6ecc4441d8

**Meaning.** For a tree, Δ≤α+ω−2. The source uses the usual connected, acyclic tree premise, which includes a one-vertex tree. Its two branches distinguish that edgeless possibility from a tree containing an edge.

**Proof idea.** An edgeless tree has Δ=0, while nonemptiness gives α≥1 and ω≥1. Otherwise acyclicity excludes triangles, so the checked neighborhood bound Δ≤α+T becomes Δ≤α. An existing edge supplies a two-vertex clique and hence ω≥2. Adding ω−2 to that upper bound finishes the nontrivial branch.

[Lean proof](../../results/proofs/1818a4423ab64ad66a2758af80b4cad2bfe0ea2b9e5aabfeba363c2e035f6875.lean#L300) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_chromatic_number_le_0.25_size_2.5_c4ad0bee6a10

**Meaning.** Every finite simple graph satisfies χ≤m/4+5/2. This estimates the number of colors from the edge count alone, with no restriction on connectivity or degrees. Integrality of the chromatic number is used to obtain the linear form.

**Proof idea.** Map an optimal coloring to its graph of color labels. This graph needs χ colors on χ vertices and is therefore complete, while its edges come from original edges. Consequently χ(χ−1)≤2m. Cases χ≤1 are immediate. In the remaining cases, χ≤4 or χ≥5 gives (χ−4)(χ−5)≥0; polynomial arithmetic yields the estimate.

[Lean proof](../../results/proofs/6420927c136bb6057fcf8a9ac309bafa803f8460f061d324978b8fb96c619739.lean#L302) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_chromatic_number_le_0.5_signless_laplacian_spectral_radius_1_d6eec3bf02f8

**Meaning.** Every finite simple graph satisfies χ≤q₁/2+1, where q₁ is the largest eigenvalue of the signless Laplacian D+A. It is taken as zero for the vertexless graph. This supplies a spectral upper bound for proper coloring.

**Proof idea.** The proof establishes the signless-Laplacian quadratic-form upper bound using an eigenbasis. Since D−A is positive semidefinite and D+A=2A+(D−A), testing adjacency eigenvectors shows every adjacency eigenvalue is at most q₁/2. Thus r≤q₁/2. The checked spectral coloring bound χ≤r+1 completes the nonempty case; χ≤n handles the empty one.

[Lean proof](../../results/proofs/e1feacadab0a5036c1ad707bd1ec998a55ceadf1b03aa9040a70790dd5122d35.lean#L306) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_chromatic_number_le_0.5_size_1.5_4ae9b1d23719

**Meaning.** Every finite simple graph satisfies χ≤m/2+3/2. An edge count can therefore certify a simple upper bound on how many colors are needed. The inequality has no graph-class or degree premise.

**Proof idea.** The graph on labels of an optimal coloring must be complete and has no more edges than the original graph, yielding χ(χ−1)≤2m. The proof handles χ≤1 and χ=2 explicitly. For χ≥3, (χ−2)(χ−3) is nonnegative. Combining this product with the quadratic edge inequality gives χ≤m/2+3/2 by polynomial arithmetic.

[Lean proof](../../results/proofs/c90e12b320bf3fa70920de8bd3b553ff161af724b655f222890afff2da323750.lean#L240) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_chromatic_number_le_1_size_1_658db08f8c3d

**Meaning.** Every finite simple graph satisfies χ≤m+1. This is a convenient coloring estimate using just the total number of edges, although it can be much looser than estimates using maximum degree or more detailed structure.

**Proof idea.** Each vertex’s incident edges are contained in the full edge set, so degree(v)≤m for every vertex. The source turns these bounds into Δ≤m, casts the inequality to reals, and invokes the checked greedy helper χ≤Δ+1. Linear arithmetic combines them into χ≤m+1. No extra coloring construction is performed in this target.

[Lean proof](../../results/proofs/d2cfa08d8e42beb362d02ba7eef25445774fdb697020dc4ea8035fe68b4ea44c.lean#L70) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_clique_number_le_0.25_size_2.5_e8558e9f6029

**Meaning.** Every finite simple graph satisfies ω≤m/4+5/2. This converts the quadratic edge requirement of a clique into a linear estimate for its size. Integrality of clique size is part of the argument.

**Proof idea.** Choose a maximum clique and bound the degree of each of its vertices below by ω−1. Summing those degrees and then using the full degree sum gives ω(ω−1)≤2m. Since integer ω is either at most four or at least five, (ω−4)(ω−5)≥0. Polynomial arithmetic combines this product with the quadratic count to prove the stated line.

[Lean proof](../../results/proofs/f1a25dbb88c34dbce83521566b0844df17200d038cf9d4d3cdb20e3ebdd93f2c.lean#L142) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_clique_number_le_0.5_signless_laplacian_spectral_radius_1_fe853c08d6ab

**Meaning.** Every finite simple graph satisfies ω≤q₁/2+1. Here q₁ is the largest signless-Laplacian eigenvalue, with value zero for the empty graph. The proof derives this directly from a clique indicator rather than transferring a coloring bound.

**Proof idea.** An eigenbasis establishes xᵀ(D+A)x≤q₁‖x‖². For the indicator of a maximum clique, the degree term and adjacency term each contribute at least ω−1 at every clique vertex, so the quadratic form is at least 2ω(ω−1), while its norm squared is ω. Cancel positive ω and rearrange. The vertexless case follows from ω≤n.

[Lean proof](../../results/proofs/ea18be46f2c3f8155f47a4c17b8c7a31597d364b49df4f1493b178ad258e9c44.lean#L195) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_clique_number_le_0.5_size_1.5_c9441521e80d

**Meaning.** Every finite simple graph satisfies ω≤m/2+3/2. This is another linear relaxation of the edge count forced by a clique, and it has no connectivity or degree premise.

**Proof idea.** For ω≤2, the checked bound ω≤m+1 suffices when combined with the small clique size. Otherwise choose a maximum clique, sum the inequalities ω≤degree(v)+1, and use the full degree sum to obtain ω²≤2m+ω. Here ω≥3, so (ω−2)(ω−3)≥0. Polynomial arithmetic combines these facts to get the displayed line.

[Lean proof](../../results/proofs/d2ea7d5ea224d388e14eb55534a6c5707c5e6c1ce0a1ab5568ad2bb75b5faf0f.lean#L142) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## hull_density_le_0_chromatic_number_1_e2a3f249a4cd

**Meaning.** Edge density p is at most one for every finite simple graph. The statement’s zero coefficient on χ removes coloring from the actual inequality. Here p means 2m/[n(n−1)], with value zero when n<2; it is not an adjacency eigenvalue.

**Proof idea.** The small-order branch simplifies to zero≤one. Otherwise every edge is an unordered pair of distinct vertices, so m≤choose(n,2). The proof converts this into 2m≤n(n−1), carefully justifying the natural-number subtraction when casting to reals. Since n≥2 makes the denominator positive, division yields p≤1.

[Lean proof](../../results/proofs/989975cfd53c27b676a6ad4b54f8904b1021302b12735144f7d42904f6ce1490.lean#L70) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_067a59b774064887e40b

**Meaning.** For a connected graph with Δ≥2 and ω≤3, 6T≤mΔ. These premises are retained in the declaration; the proof’s structural restriction is the absence of a four-vertex clique, which follows from ω≤3.

**Proof idea.** Each vertex’s induced neighborhood is triangle-free. The checked bounds Δ≤α+T and m≤(n−α)Δ, applied there, yield four times its edge count at most its order squared. Triangles containing the vertex inject into those neighborhood edges. Sum over vertices: every triangle is counted three times, and degree(v)²≤Δ·degree(v). The degree sum is 2m, giving the result.

[Lean proof](../../results/proofs/d0fa5576c036694feef8c3cbcf6f05ac27e3898160d884914e4b5a99e6e7c20f.lean#L145) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_255bb4d9cb35aa834f3d

**Meaning.** For a triangle-free graph, m≤α(n−α). This relates the edge count to a maximum independent set and the number of vertices outside it. Triangle-freeness is the premise that bounds each neighborhood’s size by α.

**Proof idea.** Choose a maximum independent set S. Every neighborhood is independent in a triangle-free graph, so every vertex has degree at most α. Every edge has an endpoint outside S, since no edge lies inside S. Cover the edge set by the incidence sets of those n−α vertices and bound their total cardinality by α(n−α).

[Lean proof](../../results/proofs/3325f7045b1a8e665eb765e928c0cff2ce852b5bfb1529581e7f8e86d1b842b9.lean#L196) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_3307c010f6ed4887361d

**Meaning.** Every finite simple graph satisfies α(α−1)+2m≤n(n−1). The ordered pairs of distinct vertices inside an independent set and the ordered adjacent pairs must fit into all ordered pairs of distinct vertices.

**Proof idea.** Choose a maximum independent set S and form its ordered off-diagonal pairs. These are disjoint from the set of ordered adjacent pairs, whose size is 2m. Their union lies in the off-diagonal pairs of all vertices, of size n(n−1). Comparing cardinalities gives the natural-number inequality. A separate identity handles subtraction when converting these counts to the displayed real-number products.

[Lean proof](../../results/proofs/57679a2dff24a584cd6d2141289a55e9796320b10dd32aa9491916066120c0b9.lean#L84) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_59ab30aca63b22f5c121

**Meaning.** Every finite simple graph satisfies 2mω≤(ω−1)n². This is the density restriction supplied by a maximum clique bound: a graph cannot have more edges than the corresponding clique-free extremal estimate permits.

**Proof idea.** The source proves that no clique has ω+1 vertices, then invokes Mathlib’s Turán edge-count theorem with parameter ω. It multiplies that edge bound by 2ω and applies the library’s estimate for the Turán number, producing the displayed inequality. If ω=0, absence of even a one-vertex clique forces the vertex type to be empty, and the formula simplifies directly.

[Lean proof](../../results/proofs/d09d18e53ac9bfc9b425c9f0c5637e04401ab7af7a68f88c7e3cb89e9d681760.lean#L283) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_647c8331689b635ebdea

**Meaning.** Every finite simple graph satisfies 2χ≤n+ω. This bounds coloring needs using both vertex count and maximum clique size. It captures the saving obtained when a nonadjacent pair can share one color.

**Proof idea.** The proof inducts over finite vertex sets. If the set is a clique, give every vertex a distinct color and use its size≤ω. Otherwise remove two nonadjacent vertices, color the smaller set inductively, then restore both with one shared new color. Removing two vertices and adding one color preserves the inequality. Apply the construction to all vertices and bound χ by its number of colors.

[Lean proof](../../results/proofs/0d9b5072ee4cc2769b7425205547d669b4affb263ba8df20f5935508b94baa83.lean#L163) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_67bca380d677e1278e8a

**Meaning.** A triangle-free graph with α≤2 has at most five vertices. The source’s upper threshold just above two is equivalent to α≤2 because independent-set size is an integer. There is no connectivity premise.

**Proof idea.** Triangle-freeness gives ω≤2, and α≤2 makes the complement triangle-free as well. For any chosen vertex, its neighborhood in each graph is independent, so the original degree is at most α≤2 and the complement degree is at most ω≤2. These two degrees total n−1, hence n≤5. The empty vertex type is handled separately.

[Lean proof](../../results/proofs/94ee33a4225dcd4e5dcf6b8bfe7f000614b5d2a503cff739ed44e60160aa5c52.lean#L20) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_6a9d528a62da01e31f36

**Meaning.** For a connected graph with n≥3, the triangle lower bound counts triangles inside a maximum clique plus guaranteed triangles with one vertex outside it. Set h=max(0,δ+ω+1−n); equivalently, the conclusion is T≥choose(ω,3)+(n−ω)choose(h,2).

**Proof idea.** An outside vertex has at least h neighbors in the clique, since at most n−ω−1 neighbors lie outside it. Every pair of its clique neighbors forms a triangle. These triangles are distinct across outside vertices and disjoint from triangles wholly in the clique. The proof adds the counts, then converts binomial coefficients to the polynomial expression in the index; the declared guards are unused.

[Lean proof](../../results/proofs/c2618c483d70861e653f4c68cf29b667da90c7573d90be5a73886fa047f634a8.lean#L18) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_6ef1594add3b905d1214

**Meaning.** For a connected graph with n≥2, put t=r−(ω−1) and u=r−d̄. The conclusion bounds ω times the squared positive part of µ₂(n−ω)−nt by n³tu. It relates clique size and Laplacian connectivity to two adjacency spectral deficits.

**Proof idea.** The checked parents give t,u≥0. The matrix rI−A is positive semidefinite; testing the clique indicator and constant vector yields a Cauchy–Schwarz inequality involving the clique boundary. A centered clique indicator gives the Laplacian lower bound for that boundary using µ₂. Combining these estimates, squaring the positive excess, and cancelling positive ω proves the result.

[Lean proof](../../results/proofs/77efe022d88b5238dfb14f555c545bb3ec9d14053412eca0bc1d6e728c1f9cb6.lean#L495) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_886a365b7173b119a27a

**Meaning.** Every finite simple graph satisfies α+m≥n. Removing at most one selected endpoint per edge leaves an independent set, so the vertex count cannot exceed the independent-set size plus the edge count.

**Proof idea.** The source chooses one endpoint of each undirected edge and takes their image T. Repeated selections only decrease its size, so |T|≤m. The remaining set S has no internal edge: either endpoint selected for such an edge would lie in T. Thus |S|≤α, while |S|+|T|=n. Add the bounds and cast to reals.

[Lean proof](../../results/proofs/0ac27c399a67c11337227a725e909f723295a6ef0db0007baa7414e1f9d8ec04.lean#L840) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_8b660ccec0c7e356f6cf

**Meaning.** Every finite simple graph satisfies Δ≤α+T. In particular, when there are no triangles, maximum degree is at most the largest independent-set size. The general bound charges each additional neighbor to a triangle.

**Proof idea.** For each vertex v, choose a largest independent subset S of its neighborhood. Every remaining neighbor has a neighbor in S, otherwise S could be enlarged. Select one such connection: together with v it forms a triangle. Distinct remaining neighbors give distinct triangles because each triangle has exactly one neighbor outside S. Hence degree(v)≤|S|+T≤α+T; take the maximum degree.

[Lean proof](../../results/proofs/44b631c36b92f80ded04a7f47d98a710bab9a73688575e5e9f5cac2859c0b574.lean#L280) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_8ce30216566f34c2605a

**Meaning.** Every finite simple graph satisfies m≤(n−α)Δ. The vertices outside a maximum independent set form a vertex cover, so their number and degree budget give an upper bound on the total edge count.

**Proof idea.** Choose an independent set of size α, represented as a clique in the complement. Every edge has at least one endpoint among the remaining n−α vertices. The source covers all edges by those vertices’ incidence sets. A union’s cardinality is at most the sum of their degrees, and each degree is at most Δ. Counting the remaining vertices and casting to reals gives the result.

[Lean proof](../../results/proofs/5015cbd8b07e6ae6f22d8ff791e192aa58cc6d688ce31895ca0ade283979f002.lean#L202) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_92debe23dc15135cb8a8

**Meaning.** Every finite simple graph satisfies α(2m+n)≥n². For a nonempty graph this yields α≥n²/(2m+n), a lower bound on independence size from order and edge count. The multiplied form also covers the vertexless graph.

**Proof idea.** Give each vertex weight 1/(degree(v)+1). Repeatedly choose a vertex of minimum original degree among those remaining and remove its closed neighborhood. Each removed block has weight at most one, producing an independent set whose size bounds the total weight. Cauchy–Schwarz gives n²≤(total weight)·Σ(degree(v)+1). The degree sum makes the latter factor 2m+n.

[Lean proof](../../results/proofs/f2097d0c3ebee23ad1229b83f5e3036b8d10ac8563e4b80a7ba3ae46fe5eae00.lean#L220) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_a00de82f9ab8ab051b93

**Meaning.** When α≥2, the surplus αχ−n has square at most (α−1)[α(2m+n)−n²]. Color-class counting ensures that surplus is nonnegative. The inequality strengthens the basic bound α(2m+n)≥n² by incorporating the chromatic number.

**Proof idea.** If the surplus is zero, the basic independence bound suffices. Otherwise choose a smallest induced subgraph still needing χ colors; deleting any vertex shows its closed neighborhood inside that subgraph has at least χ vertices. A weighted independence inequality, proved by greedy removal and Cauchy–Schwarz, is applied with one weight inside this subgraph and another outside. Factoring and transferring the resulting inequality proves the target.

[Lean proof](../../results/proofs/ec1fa1d2132c01289810fceaa4dea8316f81e10efbfef7308017616df21267a9.lean#L129) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_a659fd0df8bac9fe2f61

**Meaning.** Every finite simple graph satisfies χ+α≤n+1. A maximum independent set can share one color, while each remaining vertex receives its own color. The inequality includes the vertexless graph as well.

**Proof idea.** The source chooses a maximum clique in the complement, hence a maximum independent set S in the original graph. It builds a coloring with one distinguished color for S and distinct colors indexed by vertices outside S. Independence handles edges whose endpoints would both have the distinguished color; all other cases use distinct labels. The palette has n−α+1 colors, giving the result.

[Lean proof](../../results/proofs/e8d792f1194c71de8fdc1236f0b84b6ad52fea0bcba2a3a691779eb8a9b873da.lean#L256) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_ad89177ba7a4bf76dbff

**Meaning.** For a connected graph with n≥4, n q₁[q₁−2(ω−1)]≥µ₂[n q₁−2ω(ω−1)]. This couples the largest signless-Laplacian eigenvalue with the Laplacian spectral gap and clique size. Both stated premises are retained.

**Proof idea.** Use indicators of a maximum clique and its complement. Eigenbases give an upper quadratic-form bound for D+A and a lower bound for D−A on zero-sum vectors. These bounds control the clique boundary and yield a nonnegative quadratic for vectors constant on each part. Its discriminant gives a determinant inequality, whose factorization proves the target. If ω=n, checked spectral bounds give q₁=2(n−1) directly.

[Lean proof](../../results/proofs/4ac12c2eada405d9ff66f5b407e3ebb14cee5d92521a171e1d71b658618ff838.lean#L258) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_badc6853af6fae3c590c

**Meaning.** For a connected graph with n≥2, µ₂(n−ω)≤n(Δ−ω+1). The maximum degree above the internal degree of a clique limits how strongly the Laplacian can connect that clique to the rest of the graph.

**Proof idea.** An eigenbasis proves the Laplacian lower bound on zero-sum vectors, using connectedness to identify its zero eigenspace with constants. Apply it to the centered indicator of a maximum clique. Its squared norm is nω(n−ω), while its Laplacian form is n² times the clique boundary. Each clique vertex has at most Δ−ω+1 outside neighbors. Combine the bounds and cancel positive nω.

[Lean proof](../../results/proofs/ee06a7412f06edd3fb673f0cc63ec786f73cdd9234c0e84b0522502bbff4f674.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_c36bd6bfd40d117b3da2

**Meaning.** If δ≥1, then (Δ+1)α≤Δn. The premise says every vertex has a neighbor, excluding isolated vertices. The source’s threshold just below one is equivalent to this integer minimum-degree condition.

**Proof idea.** Choose one neighbor f(v) for each vertex and a maximum independent set S. Each chosen neighbor of a vertex in S lies outside S. For any outside vertex, the vertices mapped to it form a subset of its neighborhood and therefore number at most Δ. Counting these fibers gives α≤(n−α)Δ. Rearranging yields the displayed bound.

[Lean proof](../../results/proofs/4fb4c7df5b57462ab37f7de967106a00e2f69ef5bd0b01b535d561ac30936f4a.lean#L214) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_c9e8fb9fc8b8b997104d

**Meaning.** When α≥2, the squared positive part of αω−n is at most (α−1)[α(2m+n)−n²]. The positive part is needed because clique size does not force αω≥n. This refines the basic independence-count inequality when that product does exceed n.

**Proof idea.** If αω≤n, the basic checked bound α(2m+n)≥n² settles the claim. Otherwise prove a weighted independence inequality by greedy closed-neighborhood removal and Cauchy–Schwarz. For a maximum clique, assign weight n−ω inside and ω(α−1) outside. Each clique vertex’s closed neighborhood contains the whole clique. Bounding the weighted neighborhood sum and factoring the resulting expression gives the target.

[Lean proof](../../results/proofs/4c859db780ba7715dab5938161a54a75ba659d4195234b2a3303f3cff2bc80c0.lean#L229) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_ccdcf6b440caaa736914

**Meaning.** For a nonempty graph, α+m≥n+(ω−1)(ω−2)/2. This improves the basic bound α+m≥n by the edges forced among vertices of a clique after its possible overlap with an independent set is removed.

**Proof idea.** Choose maximum independent and clique sets. Every vertex outside the independent set has a neighbor inside it, producing at least n−α distinct crossing edges. The two chosen sets overlap in at most one vertex, so at least ω−1 clique vertices remain outside and force choose(ω−1,2) additional edges. These are disjoint from the crossing edges. Add both counts and convert the binomial coefficient to the displayed polynomial.

[Lean proof](../../results/proofs/81a8fcc05c4b7add3a8e2a06b4be40309cc3b9d1d7a03d79d658d75bdd7342a0.lean#L145) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_cd7c90572aced445fec8

**Meaning.** For a connected graph with χ≥4, m−n+1≥(χ−1)(χ−2)/2. Thus requiring many colors forces a minimum number of edges beyond a spanning tree. The source’s threshold just below four is equivalent to χ≥4.

**Proof idea.** Choose a smallest induced subgraph that is not (χ−1)-colorable. Restoring a deleted vertex proves every degree there is at least χ−1, and its order is at least χ. Compare its edges with a spanning tree of the whole graph; the tree contains at most one fewer internal edge than the subgraph’s order. Degree counting and this comparison yield the bound after polynomial arithmetic.

[Lean proof](../../results/proofs/b9bcb08ec90ec33a1de30dcd55ffac5ff2d14f597a1d57530bfac8a40f403876.lean#L14) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_e0b140f9bf3d5870fe9f

**Meaning.** A graph supplied with a proper two-coloring has χ=ω. This covers three possibilities: a vertexless graph has both values zero; a nonempty edgeless graph has both one; and a graph with an edge has both two.

**Proof idea.** The proof splits on empty versus nonempty vertex type, then on whether any edge exists. The first two cases simplify directly. An edge gives a two-vertex clique, so ω≥2. The checked two-colorability parent gives χ≤2, while the general clique-versus-coloring parent gives ω≤χ. These bounds squeeze the values together and establish equality.

[Lean proof](../../results/proofs/69891b74ef61e4930bd828d47f77d3acdeac0b02b593ed1f0d459be17193c390.lean#L70) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_e679ce9c7fa60e2c7bfd

**Meaning.** Every finite simple graph satisfies χ(χ−1)≤2m. A graph requiring χ colors must contain enough edges to connect every pair of color classes in an optimal coloring. The statement does not require a χ-vertex clique in the original graph.

**Proof idea.** The proof maps an optimal coloring to a graph on χ color labels. Chromatic-number monotonicity forces that graph to be complete. Each of its directed edges has a preimage directed edge in the original graph, so its edge count is at most m. Apply the checked clique-edge bound to this complete graph, whose clique number is χ, and transfer the inequality.

[Lean proof](../../results/proofs/5062e8b1c67dc97af3397ffffc6edb836e619942d83f240398f014cff6f3f831.lean#L145) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## model_eb72426fa9b067f5a247

**Meaning.** Every finite simple graph satisfies ω(ω−1)(ω−2)≤6T. A clique of size ω contains choose(ω,3) triangles, so total triangle count supplies an obstruction to a larger clique. The formula also handles clique sizes zero, one, and two.

**Proof idea.** Choose a maximum clique and show that its three-element subsets belong to the graph’s triangle set. Their count is choose(ω,3), giving choose(ω,3)≤T. For ω≥2, a descending-factorial identity converts six times this binomial coefficient into ω(ω−1)(ω−2), with justified real-number subtraction. Smaller clique sizes make the product zero and are handled separately.

[Lean proof](../../results/proofs/054ab54c97e40178d2ffb11a48deca6165a6f30e0d0d82aa3cb53bb7fc14e079.lean#L60) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## pilot_bipartite_two_colors

**Meaning.** If a graph is supplied with a proper two-coloring, its chromatic number is at most two. This is the formal bipartite guard used here: the premise itself already provides the coloring witness needed for the conclusion.

**Proof idea.** The source invokes the premise’s chromatic-number upper bound, giving an inequality in extended natural numbers. Since the upper bound is the finite number two, it converts the inequality to a bound on `chromaticNumber.toNat`. A final cast produces the real-number inequality in the archive. No new partition or coloring is constructed.

[Lean proof](../../results/proofs/3111cf7351031dcd8aa1a48d1bdae9cc10dc1c4d24f96975d6336708bbe900e0.lean#L20) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)

## pilot_independence_le_order

**Meaning.** Every finite simple graph satisfies α≤n. An independent set contains only vertices of the graph, so its maximum size cannot exceed the order. The result applies without connectivity, regularity, or nonempty-graph premises.

**Proof idea.** The proof applies the checked clique-versus-order theorem to the complement graph. Complementing preserves the vertex type, and its maximum clique size is exactly α in the original graph. That parent obtains ω≤n by chaining clique-versus-coloring with the vertex-count coloring upper bound. Substitution gives the requested independence inequality directly.

[Lean proof](../../results/proofs/e3febcf8bf907c8a0294447029cbcea16e0db1e3a2ef8b5a5a4da59fbea37af8.lean#L94) · [Full statement and frozen assessment](../../results/all-proofs.md#coloring-cliques-and-independence)
