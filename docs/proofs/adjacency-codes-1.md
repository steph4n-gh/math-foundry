# Adjacency codes and unique neighbors: proof explanations, part 1

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

These are informal explanations of the linked Lean proofs. The index retains each exact statement and its frozen assessment.

All graphs here are finite and simple. Write n for the number of vertices, m for the number of edges, δ for the minimum degree, Δ for the maximum degree, and α for the largest independent-set size. A regular graph has the same degree at every vertex; a bipartite graph admits two color classes with no edges within either class.

The binary adjacency code is the kernel of the adjacency matrix over GF(2), where addition is modulo two. Its dimension is k. A word’s weight is the number of its nonzero coordinates; its support is the set of those coordinates. Write d for the minimum nonzero word weight, with d = n + 1 when there is no nonzero word. A kernel word has an even number of supported neighbors at every vertex.

The unique-neighbor radius u is one less than the smallest nonempty vertex set S for which no vertex has exactly one neighbor in S. The witnessing vertex may lie inside or outside S. If there is no such set, u = n. Equivalently, every nonempty set of at most u vertices has a unique neighbor. The minimum defining u includes n + 1 as a fallback before subtracting one.

For the spectral comparison, λ denotes the second-smallest eigenvalue of the normalized Laplacian, defined here as zero when the graph is disconnected or has fewer than two vertices. Floors round down, ceilings round up, and log means the natural logarithm. Integer-valued guards are described by their equivalent integer conditions.


## composed_98f6a5db9b7b63f3

**Meaning.** For every finite simple graph, the unique-neighbor radius is at most the number of vertices: u + 1 ≤ n + 1. This also covers graphs whose adjacency code contains only the zero word, using the distance convention described above.

**Proof idea.** The proof chains two checked parents. `parity_code_unique_neighbor_distance` gives u + 1 ≤ d: a nonzero kernel word cannot have exactly one supported neighbor at any vertex, because that would violate its zero neighbor sum. `hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e` gives d ≤ n + 1, since n + 1 is included among the candidate weights.

[Lean proof](../../results/proofs/43f28b472a6e83733c53a43a433853b5bb0113254f6f953a0fff006306b2fd59.lean#L85) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_min_degree_le_0.0310263_0.1_parity_code_distance_size_6.5_is_connected_8f22405c2232

**Meaning.** For a connected graph, the minimum degree is bounded by the stated positive multiple of d, plus m/10 + 6.5. The distance term can only increase the right-hand side, so this statement allows both a nonzero adjacency code and the zero-code distance convention.

**Proof idea.** The degree-sum identity gives nδ ≤ 2m, and a simple graph has n ≥ δ + 1. Together these yield δ(δ + 1) ≤ 2m. A nonnegative square then proves the stronger bound δ ≤ m/10 + 6.5. Finally, the proof adds the nonnegative distance term with its exact coefficient.

[Lean proof](../../results/proofs/8ca386c64cbab92999c0920a9550240d32a5b6c473719fdf800d06af7f3f59df.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_min_degree_le_0.25_0.5_parity_code_distance_size_-0.25_is_connected_bd60c60d3850

**Meaning.** For a connected graph, δ ≤ d/4 + m/2 − 1/4. Thus the edge count and adjacency-code distance jointly bound the smallest vertex degree, including when d takes the zero-code value n + 1.

**Proof idea.** Every candidate distance is at least one, while degree sums give δ(δ + 1) ≤ 2m. If m ≥ 2δ, these facts suffice. Otherwise the integer inequalities force δ to be one or two and n = δ + 1. The graph is then complete; its kernel equations rule out weights below three. This stronger distance estimate handles the remaining cases.

[Lean proof](../../results/proofs/cf6ca3ddd97714eed3b736adbfe2607ad54b325f3a7d968fb5bb95b2059503d4.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_min_degree_le_0.4_0.4_parity_code_distance_size_-0.4_is_connected_6ace68e0f43e

**Meaning.** For a connected graph, the minimum degree is at most two fifths of d + m − 1. This is the exact rational form of the displayed decimal bound; no assumption that the adjacency code is nonzero is required.

**Proof idea.** Degree sums first give δ(δ + 1) ≤ 2m. The proof examines the minimum candidate weight. The sentinel n + 1 and weights at least three satisfy the desired arithmetic bound directly. A weight-one kernel word forces an isolated vertex. A weight-two word has nonadjacent supported vertices, giving n ≥ δ + 2 and a stronger edge bound. Integer cases for δ finish that last branch.

[Lean proof](../../results/proofs/2f33f3f64999cd89d674161ebd3c8413a3a47f54f3993b5830a83847601b92b4.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_min_degree_le_1_0.25_parity_code_distance_size_-1_is_connected_6c1d8e96f797

**Meaning.** For a connected graph, δ ≤ d + m/4 − 1. A small codeword therefore constrains the minimum degree unless the graph has enough edges. The statement retains the convention d = n + 1 when the code has no nonzero word.

**Proof idea.** The proof combines degree sums with n ≥ δ + 1, then considers the minimum weight. The sentinel and weights at least three are handled by arithmetic. At positive minimum degree, a weight-one word is impossible. A weight-two word has a nonadjacent support pair, strengthening the edge bound to δ(δ + 2) ≤ 2m. The integer case δ = 3 is treated separately; the other cases follow from a nonnegative product.

[Lean proof](../../results/proofs/57cb154f3bcba36e40a71bd28763a190f6c485b34ca582b94125da0c80fd87d6.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_parity_code_dimension_ge_-1_0_min_degree_parity_code_distance_1_is_connected_d17614a8e073

**Meaning.** For a connected graph, k ≥ 1 − δ. When the minimum degree is positive, the right-hand side is nonpositive and the bound follows from the fact that a dimension is nonnegative. When the minimum degree is zero, the statement requires a nonzero kernel.

**Proof idea.** The proof splits on δ = 0. In that case, the minimum-degree characterization supplies an isolated vertex. The vector that is one there and zero elsewhere is a nonzero adjacency-kernel vector, so k ≥ 1. If δ is not zero, its integer value is at least one; combining this with k ≥ 0 completes the inequality.

[Lean proof](../../results/proofs/deccaabab05c569c5c7b3946c5d3ac2dde674a8a7eb4d4aa5cd5b353cd4ad221.lean#L1034) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_parity_code_distance_ge_1_0_unique_neighbor_radius_min_degree_1_is_regular_42ada867cd60

**Meaning.** For a regular graph, the minimum nonzero adjacency-code weight satisfies d ≥ u + 1. The regularity premise is part of this indexed statement, although the supporting inequality holds for every finite simple graph.

**Proof idea.** The checked parent `parity_code_unique_neighbor_distance` proves exactly u + 1 ≤ d. It takes the support of a nonzero codeword and observes that a unique neighbor would make one adjacency row sum nonzero. That support is therefore a set with no unique neighbor, so its size is at least u + 1. The target simply applies this parent inequality.

[Lean proof](../../results/proofs/6c803884484842ae83ccccf0006b3090ba5ff1ced7b733d97e90d01cd1d07afb.lean#L74) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e

**Meaning.** For every finite simple graph, d ≤ n + 1. If the adjacency code is zero, equality holds by the adopted distance convention. Otherwise the minimum is taken over actual nonzero codeword weights together with that same fallback value.

**Proof idea.** The proof opens the finite set used to define d. It explicitly contains n + 1, regardless of the graph or its kernel. The minimum of a nonempty finite set cannot exceed any member, so d ≤ n + 1 follows immediately. The final step views this integer inequality as an inequality between real numbers.

[Lean proof](../../results/proofs/7c5a763135a1d9b92e2467660d6e42100a6cc31e4b5da4d8a89f3680b8a77404.lean#L109) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_size_ge_1_0_parity_code_distance_normalized_laplacian_spectral_gap_-2_is_connected_97851a6e314b

**Meaning.** For a connected graph, m ≥ d − 2, or equivalently d ≤ m + 2. This includes the zero-code case. The bound uses connectivity and the distance convention; the spectral-gap term suggested by the identifier does not appear in the actual statement.

**Proof idea.** The proof first bounds d by the candidate value n + 1. It then uses the connected-graph fact n ≤ m + 1: a connected graph needs at least n − 1 edges. Substituting the second inequality into the first gives d ≤ m + 2, which is rearranged into the stated form.

[Lean proof](../../results/proofs/8bfc29b40f482db9eb16211ffd1f385a5420cd9be2743f929dc8bcf62f25d194.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## hull3d_unique_neighbor_radius_ge_1_0_normalized_laplacian_spectral_gap_order_0_is_bipartite_f9946b253195

**Meaning.** For a bipartite graph, u is at least the normalized Laplacian gap λ defined above. The statement uses that gap as zero for disconnected graphs and for graphs with fewer than two vertices. Its proof actually establishes the comparison without using the bipartite premise.

**Proof idea.** The checked parents give u ≥ 0 and λ ≤ n/(n − 1) ≤ 2 in the connected case. If u ≥ 2, this suffices. Otherwise a smallest set with no unique neighbor consists of two vertices with identical neighborhoods. Their scaled difference produces a normalized-Laplacian eigenvector of eigenvalue one. Together with the zero eigenvalue and eigenvalue ordering, this gives λ ≤ 1 = u.

[Lean proof](../../results/proofs/ae7c6f28f748f3fd779c8962ac38a576e6dbbadd0aeeffd42eaf6126804c3989.lean#L149) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_01fb90bd2b4c0045f68b

**Meaning.** Assume δ ≥ 1, Δ ≥ 2, and k ≥ 1. Then k + 2⌈n/(2Δ)⌉ ≤ n. In terms of the adjacency matrix, the available number n − k of independent constraints must cover the vertices, with an additional even-rank restriction.

**Proof idea.** The target applies the checked parent `model_5c1b1cd577e96807f60f`, which proves the same conclusion already under Δ ≥ 1. Its proof chooses independent adjacency columns whose supports cover every vertex, yielding n ≤ Δ times the matrix rank. It also proves that the symmetric zero-diagonal binary matrix has even rank. Rank plus kernel dimension equals n; rounding the resulting half-rank bound gives the ceiling term.

[Lean proof](../../results/proofs/14955392a1bb0c96b1977e5ca6e1c0647032a020dac3237da67eee86e9109f8f.lean#L334) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_02ce2b029db2bd60d69c

**Meaning.** Assume the graph is regular, δ ≥ 1, and k ≥ 1. If its common degree is even, k + d ≤ n + 1; if the degree is odd, the bound improves to k + d ≤ n. The floor expression in the statement encodes this degree parity.

**Proof idea.** A dimension argument finds a nonzero codeword supported on n − k + 1 positions, giving the first bound. To sharpen it for odd degree, the proof assumes equality. This would make the indicator of every d-element subset a codeword. If d = n, the all-ones word contradicts odd degree. Otherwise swapping one vertex for an adjacent vertex changes an adjacency row sum by one, again contradicting the kernel condition.

[Lean proof](../../results/proofs/b01f5a2641d8514cb94597217ed166332f5deeb216cc671fdee48d99b94260d4.lean#L125) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_02ea1aa899a63c06ad70

**Meaning.** For a bipartite graph with k ≥ 1, k + 2d ≤ n + 2. Compared with the usual one-distance dimension bound, bipartiteness allows the proof to remove d − 1 coordinates from each color class while still determining every codeword.

**Proof idea.** Restricting a codeword to either color class leaves it in the kernel. The proof first shows each class has at least d − 1 vertices. It then removes that many vertices from both classes. A codeword vanishing outside the removed vertices splits into two kernel words of weight below d, so both vanish. The remaining-coordinate projection is therefore injective. Its dimension bound gives the result. The parent `parity_code_dimension_le_order` supplies k ≤ n in the zero-distance branch.

[Lean proof](../../results/proofs/174128a177211789be5c79bf73b4f929a43033ff877c34aee5fb0f7f2355a285.lean#L125) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_0619a96c0eebea1f3be2

**Meaning.** Assume the graph is bipartite and regular, δ ≥ 2, and k = 2. For odd δ, the conclusion is d ≥ u + 1. For even δ, it strengthens to d ≥ u + δ − 1. The displayed floor term selects these two cases.

**Proof idea.** The checked parent `parity_code_unique_neighbor_distance` supplies the odd-degree bound. At even degree, both color-class indicators are codewords. Since k = 2, they account for the whole kernel, so every nonzero word contains a full color class. Removing δ − 2 vertices from either class leaves a nonempty set with no unique neighbor. Comparing its size with u + 1 gives the additional δ − 2 improvement.

[Lean proof](../../results/proofs/365ec462712bfc8e9b7bc94a3f1833a9d24878a1f4bba5134a6d47fdafa906a3.lean#L482) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_07612542eeadcf3d9e01

**Meaning.** If k ≥ 4, then k + d + ⌈d/2⌉ + ⌈d/4⌉ + ⌈d/8⌉ ≤ n + 4. The four weight terms limit how much distance a binary adjacency code can retain while also having the stated dimension.

**Proof idea.** The proof repeatedly chooses a least-weight nonzero word and restricts the code to positions outside its support. Each restriction loses at most one dimension. Comparing a word with its sum with the chosen word shows that the new minimum weight is at least half the old one, rounded upward. Four restrictions yield the four displayed weight terms. The remaining dimension is at most the number of remaining coordinates, producing the extra k and the allowance of four.

[Lean proof](../../results/proofs/d6dafa5db52711381aba99e463d36df4da24e9e454ea1638c2f1d40171e51480.lean#L914) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_09e1e211ed16a9f315c7

**Meaning.** Assume the graph is regular, δ ≥ 1, and k ≥ 1. At even degree, d ≥ u + 1. At odd degree, d is at least the smallest even integer no smaller than u + 1. The ceiling correction adds one exactly when that lower bound is odd.

**Proof idea.** The checked parent `parity_code_unique_neighbor_distance` provides the starting bound. For odd regular degree, multiplying the all-ones vector by the adjacency matrix returns all ones. Symmetry then shows that every kernel word has coordinate sum zero over GF(2), so its weight is even. Positive dimension ensures the minimum is attained by a nonzero word. Rounding the starting lower bound up to an even integer proves the correction.

[Lean proof](../../results/proofs/2efba80c077108a7db851d97b03b2b1ebd932e5a9fd3c45c4cd9fcfc9d2489bc.lean#L90) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_0a01f6ea5c2542c96796

**Meaning.** Assume Δ ≤ 2, δ ≥ 1, and k ≥ 1. Then kd ≤ m. Thus, in a graph where every vertex has one or two neighbors, the product of adjacency-code dimension and minimum weight cannot exceed the edge count.

**Proof idea.** The proof groups vertices by their coordinate-evaluation functions on the kernel. A leaf forces its neighbor’s function to be zero, and a degree-two vertex forces its neighbors’ functions to agree. Each nonzero group has a kernel indicator word, so has at least d vertices; one representative per group determines every word, giving k ≤ the number of groups. Degree counting bounds the total size of those groups by m.

[Lean proof](../../results/proofs/9d8c2ff1cd64f8cb70b0bda2c013231bf2b20e9f74c88dceef078f13091f8afe.lean#L462) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_10001ff1f3df81eb1d71

**Meaning.** Assume the graph is bipartite, δ ≥ 1, and k ≥ 1. Both δd and 2(d − 1) are at most m; the maximum in the statement combines these two edge bounds into one inequality.

**Proof idea.** A minimum-weight codeword can be restricted to one color class without increasing its weight or leaving the kernel. Its support therefore has size d in one class. Summing degrees over that support gives δd ≤ m. For the second bound, the adjacency map is injective on vectors supported on any d − 1 of those positions. Their neighbor set consequently has at least d − 1 vertices, each of degree at least two. Summing degrees on that opposite class gives 2(d − 1) ≤ m.

[Lean proof](../../results/proofs/8eb835304d8a69409cba80bb1477f04ef5cfc7a2e304256559be4f1338d294f4.lean#L351) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_19ffa035acae97b080f4

**Meaning.** If δ ≥ 1 and k ≥ 2, then k + d ≤ n. The graph has no isolated vertices, and the code has enough dimension to choose two independent words after a suitable coordinate restriction.

**Proof idea.** An edge supplies two independent adjacency columns, so the matrix rank is at least two. Forcing k − 2 codeword coordinates to vanish leaves a subspace of dimension at least two. Choose independent words x and y there; x, y, and x + y are all nonzero and each has weight at least d. At each remaining coordinate, these three binary words contribute at most two ones. Summing and using the integer bounds gives k + d ≤ n.

[Lean proof](../../results/proofs/93fb1bfb0d3b2e8811d823e1e30809cd1aeff5c3b5fd127d4ba0fa184710397a.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_1b0dcaf9ab0652a505ad

**Meaning.** Assume the graph is bipartite and regular, δ ≥ 2, and k ≥ 1. Then δd ≤ n⌊δ/2⌋. For even δ this gives d ≤ n/2; for odd δ the right-hand side is smaller because a kernel word meets each neighborhood in an even number of vertices.

**Proof idea.** Positive regular degree makes the two color classes equally large. Restrict a nonzero kernel word to a color class where it remains nonzero, and call its support S. Every vertex in S has δ neighbors in the opposite class. Every opposite vertex has an even number of neighbors in S, hence at most 2⌊δ/2⌋. Counting these incidences from both sides and using d ≤ |S| proves the bound.

[Lean proof](../../results/proofs/713d8b843882995c84d69ed580cc686e79d6aa6d54f1df3359067b672099928a.lean#L294) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_1e20e84ccbb96865c657

**Meaning.** Assume k ≥ 1 and u ≥ 2. With t = ⌊u/2⌋, the statement bounds t log((n + 1)/(u/2)) by (n − k) log 2. It limits the unique-neighbor radius in terms of the number of independent adjacency constraints.

**Proof idea.** Two subsets of size at most t cannot have the same adjacency image: their difference would be a kernel word supported on at most u vertices, where a unique neighbor forces a nonzero row sum. Thus those subsets inject into the image space, which has 2^(n − k) elements. Counting t-tuples in an augmented set of n + 1 elements gives a lower estimate for the subset count. Taking logarithms and using t ≤ u/2 yields the stated inequality.

[Lean proof](../../results/proofs/77d7c33f6e51682407ac39fb6640096096a0d9cbbf70800b3f40cbe9a0176738.lean#L337) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_21f2572ddea1929363be

**Meaning.** For a connected graph with δ ≥ 2 and Δ ≥ 3, k < 2(m − n + 1). Here m − n + 1 counts independent cycles. The strict bound requires a vertex of degree at least three.

**Proof idea.** The proof finds a cycle containing a vertex of degree at least three. It then builds a set of coordinates whose values determine every kernel word: each adjacency row determines one unknown neighbor once the others are known. Expanding from a cycle edge costs at most degree minus two coordinates per processed vertex. The cycle and its branching vertex save one coordinate. Thus k < 2 + Σ(degree − 2); the degree-sum identity converts this to the conclusion.

[Lean proof](../../results/proofs/f3d204aa0794d4eac4123f4124d299bff3a7d6055c7cce783e6b36aceafc8046.lean#L1419) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_2209847bd37567ccf0ff

**Meaning.** Assume k ≥ 1 and u ≥ 6. Then (n³ + 5n + 6)/6 ≤ exp((n − k) log 2), which equals 2^(n − k). The polynomial counts all vertex subsets of sizes zero through three.

**Proof idea.** Every nonempty set of at most six vertices has a unique neighbor. If two subsets of size at most three had the same adjacency image, their nonempty symmetric difference would violate that fact: its indicator would lie in the kernel, while a unique neighbor would give a row sum of one. The subsets therefore inject into the adjacency image. Counting them gives 1 + n + C(n,2) + C(n,3); rank plus nullity supplies n − k, and arithmetic gives the polynomial.

[Lean proof](../../results/proofs/b0287652ac9e76b37265d0eaf41751d20154523f6853542612d52a4648d68b83.lean#L337) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_24f5a5ae83b29af4e2eb

**Meaning.** Assume the graph is bipartite, δ ≥ 2, and k ≥ 1. Then u + δ ≤ ⌊n/2⌋ + 1. The indexed statement includes positive code dimension, although the construction proving this radius bound uses the graph’s bipartition and minimum degree.

**Proof idea.** Choose the smaller color class T, so |T| ≤ ⌊n/2⌋. Both classes contain at least δ vertices. Remove δ − 2 vertices from T. In the remaining nonempty set, any vertex with a neighbor has at least two: a unique neighbor would imply its entire neighborhood fits into the removed vertices plus one, contradicting minimum degree δ. This set bounds u + 1 from above by |T| − δ + 2.

[Lean proof](../../results/proofs/9b7c62a9df694182ce7c4ec6ecb94dc5f7d5ed0a8533cd4f12ecb66c017f922b.lean#L39) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_256a48c23c065a850877

**Meaning.** Assume δ ≥ 1 and k ≥ 1. Then Δk ≤ (Δ − 1)n. Equivalently, the adjacency-matrix rank n − k satisfies n ≤ Δ(n − k). A graph without isolated vertices needs enough independent columns to cover all its vertices.

**Proof idea.** The proof chooses a basis from the adjacency columns. Its column supports cover every vertex: if a vertex were absent from all basis supports, every column would vanish there, contradicting its positive degree. Each chosen column has at most Δ nonzero entries. Counting the union gives n ≤ Δ times the basis size. Rank plus kernel dimension equals n, so substituting the basis size n − k and rearranging proves the result.

[Lean proof](../../results/proofs/41460aec5db55c65b38fd64a8e44afe6f2a301641fe6bdafc0bcf6103340483b.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_2d03d1de373ecdb63c88

**Meaning.** If k ≥ 4, then d + ⌈d/2⌉ + ⌈d/4⌉ + ⌈d/8⌉ ≤ n. These four lower bounds on successive codeword weights must fit within the available n vertex positions.

**Proof idea.** The proof establishes a general induction for binary subspaces supported on a finite set. Choose a minimum-weight word and discard its support. The resulting image loses at most one dimension, because a nonzero word supported entirely there must be the chosen word. Comparing a word and its sum with that word gives a new minimum weight at least half the old one, rounded upward. Applying this construction four times gives the four displayed terms and the length bound.

[Lean proof](../../results/proofs/7e64c85f331fc168c8dc8b9cdea0300c58b04f201c137d2d542d2c7bd7f96eba.lean#L1020) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_3666c21f3f0671245865

**Meaning.** For a tree with Δ ≤ 2, k is zero when n is even and one when n is odd. The floor expression n − 2⌊n/2⌋ is simply the parity of n. Such a tree is a path, including the one-vertex case.

**Proof idea.** Choose a vertex of degree at most one. The kernel row equations and the degree-two bound propagate zero values along walks, so knowing the value at that vertex determines the entire word; hence k ≤ 1. A tree has a bipartition. In that ordering its adjacency matrix has two off-diagonal blocks that are transposes and have equal rank. Its total rank is even. Rank plus nullity equals n, so k ≤ 1 forces the claimed parity value.

[Lean proof](../../results/proofs/09a57cc8c1544a2bdbd44e0924d186f0cd6b3d918a2e42b4de5d04e4e7000150.lean#L244) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_3e6fe089e7f561723b1e

**Meaning.** Assume the graph is connected, δ ≥ 2, Δ ≤ 3, and k ≥ 1. Then Δ(n − d) ≥ 2(m − n). The number of positions outside a minimum codeword must be large enough to accommodate the graph’s excess degree above two.

**Proof idea.** Take any nonzero kernel word and split vertices into its support S and zero positions T. Each vertex has an even number of neighbors in S; since Δ ≤ 3, that number is at most two. Thus its degree is at most two plus its number of neighbors in T. Summing gives 2m ≤ 2n + Δ|T|. Since d ≤ |S| and |S| + |T| = n, we have |T| ≤ n − d, yielding the conclusion.

[Lean proof](../../results/proofs/e4505d34aa9978617ccaf56ebd3d7ddeb85984f513c6d85cd239642ebb7acedb.lean#L410) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_40c9febc51378f8e7106

**Meaning.** Assume the graph is connected, Δ ≤ 2, and k ≥ 1. The formula determines kd: for δ = 2 it equals n; for δ = 1, positive dimension forces an odd-order path and kd = (n + 1)/2. The δ = 0 case is a single vertex.

**Proof idea.** For δ = 2, the proof applies `model_b25136df53f5aa6f52de`, the checked connected degree-two identity kd = n. For δ = 0, connectivity gives n = 1 and `nonzero_parity_code_distance_le_order` supplies d ≤ n. For δ = 1, row equations propagate alternating zero and equal coordinate functions from a leaf. This yields k = 1; degree counting makes the nonzero class one vertex larger than the zero class, and d equals its size.

[Lean proof](../../results/proofs/9121f37d9fb18aa4583d12adacee3fcb7887fae4148ae44707aa6343687c3d97.lean#L676) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_4484035064be73e8a4fc

**Meaning.** For a regular graph with δ = 4 and k ≥ 2, 2d ≤ n. The adjacency code therefore has a nonzero word whose weight is at most half the number of vertices.

**Proof idea.** Since every degree is even, the all-ones vector belongs to the kernel. Dimension at least two guarantees another codeword x different from both zero and all ones. Its complement, all ones minus x, is also a nonzero kernel word. In a binary vector, these two supports partition the vertex set, so their weights add to n. Each weight is at least d; adding those lower bounds gives 2d ≤ n.

[Lean proof](../../results/proofs/9c403760d21b07de6169294786a8f23fb973fb35d790f4a3c8ab0f973b21670c.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_45f837d4bac6b9091532

**Meaning.** Assume the graph is bipartite and regular, δ ≥ 1, and k ≥ 1. Then k is even: k = 2⌊k/2⌋. In particular, the positive kernel dimension in this statement cannot be one.

**Proof idea.** The checked parent `parity_code_dimension_le_order` gives k ≤ n and ensures there are vertices. Positive regular degree balances the two color-class sizes by counting edges. In the bipartition, the adjacency map consists of a block B and its transpose. Their images lie on separate color classes and have equal rank, so the total adjacency rank is twice rank B. Rank plus nullity equals n, and n is twice a class size. Hence k is even.

[Lean proof](../../results/proofs/b7bd65a1b9763c80c380590fd847bfbec96ce06bd2795779f24200a9c60cd8df.lean#L1145) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_4940d5883385d864ef0a

**Meaning.** For a forest, k + n ≤ 2α, where α is the size of a largest independent vertex set. Thus its adjacency-kernel dimension is bounded by twice the independence number minus the graph’s order. Connectivity is not assumed.

**Proof idea.** The proof invokes the checked parent `model_fcf51e36faf8ebb9be9b` under exactly the same acyclicity premise. That parent states k ≤ 2α − n, representing α as the clique number of the complement graph. Adding n to both sides gives this target statement. The target does not perform a second combinatorial construction; its final step is the arithmetic rearrangement of the parent bound.

[Lean proof](../../results/proofs/7244fa1b1266d858bad58e0c8297cc2482dc0c36ce7d3e8b3ec54b5b1340a8ab.lean#L669) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_498663d70c6a4882faec

**Meaning.** For a connected regular graph with δ = 2, k is two when n is even and one when n is odd. Such a graph is a cycle, and the formula 2 − (n − 2⌊n/2⌋) records these two possibilities.

**Proof idea.** The proof identifies the graph with a cycle using a cycle’s closed neighborhood and connectivity. Kernel rows force the two neighbors of each vertex to have equal values. Consequently two adjacent coordinates determine a word, so k ≤ 2, while constant words give k ≥ 1. An even cycle’s two color-class indicators give dimension two. On an odd cycle, a nonconstant kernel word would define a forbidden two-coloring, forcing dimension one.

[Lean proof](../../results/proofs/dea1b8670d344a7f779be6391f314775ef6be7d1e10efb71ba26828962c89fd3.lean#L122) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_4a232a5cfb6290dedc16

**Meaning.** Assume the graph is regular, δ ≥ 1, and k ≥ 2. At even degree, the conclusion is 2d ≤ n. At odd degree it is d ≤ n. The factor containing the floor is two in the first case and one in the second.

**Proof idea.** Dimension at least two supplies a kernel word x different from zero and all ones. For even regular degree, all ones is itself a kernel word, so all ones minus x is another nonzero word. Their weights add to n, and both are at least d. For odd degree, only the weight bound d ≤ weight(x) ≤ n is needed. Expressing the degree remainder modulo two through the floor gives the displayed factor.

[Lean proof](../../results/proofs/e0a37751aa1725de1a9626a5df4afbde0e855f754f41d83ba15c20b428436b67.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)


## model_4c93851913291e3da7ff

**Meaning.** Assume δ ≥ 1, Δ ≥ 2, and k ≥ 1. Then k + d + ⌈k/(Δ − 1)⌉ ≤ n + 2. The denominator reflects the redundant coordinate in each neighborhood parity equation.

**Proof idea.** The proof inducts on the support size of a nonzero code subspace. At dimension at most Δ − 1, the usual projection bound on dimension and distance suffices. Otherwise a supported vertex has a neighbor whose parity equation makes one of at most Δ positions redundant. Making those positions vanish loses at most Δ − 1 dimensions and leaves a smaller support. Induction gives k + (Δ − 1)(k + d) ≤ (Δ − 1)(n + 2). Division and integer rounding supply the ceiling.

[Lean proof](../../results/proofs/94610b090e7fd68ee1a75ac28a4c3c9a53df831c8ef6cd6eae0680e5913dd0e2.lean#L731) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)
