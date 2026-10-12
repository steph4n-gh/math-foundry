# Adjacency codes and unique neighbors (3)

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

The binary adjacency code is the kernel of the adjacency matrix over GF(2), the field with two elements. Here n is the vertex count, m the edge count, k the code dimension, and d the minimum number of nonzero coordinates in a nonzero codeword. If there is no nonzero codeword, d is defined as n + 1. A unique neighbor of a set is any vertex adjacent to exactly one member of that set. The radius u is one less than the smallest nonempty set with no unique neighbor; if there is no such set, u = n. The symbols δ and Δ mean minimum and maximum degree, while α and ω mean largest independent-set and clique size. These are informal explanations of the linked arguments; the links retain the exact statements and frozen assessments.

## model_ae22b995b67aeeffd271

**Meaning.** For a graph with maximum degree at most two and a nonzero adjacency code, the minimum codeword weight is exactly one more than the unique-neighbor radius: d = u + 1.

**Proof idea.** The general unique-neighbor distance theorem supplies u + 1 ≤ d. For the reverse inequality, take a nonempty set with no unique neighbor and use its indicator as a binary vector. Every vertex has at most two neighbors in the set, and the absence of a unique neighbor excludes exactly one. Its neighbor count is therefore zero or two, so the indicator lies in the adjacency kernel. Its weight is the set size, giving equality of the two minima.

[Lean proof](../../results/proofs/4684a95e89637cfd7348095943ad22c26de738044789ca8967a15c3008359276.lean#L90) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_af2f7de6fc0dc093a01d

**Meaning.** If the adjacency code is nonzero and every nonzero codeword has weight at least four, then n ≤ 2^(n − k − 1). The exponential in the linked statement is this power of two.

**Proof idea.** Fix a vertex a. For each codeword, choose a vertex v and a binary value b, then add a flip at v and the value b at a. Equal resulting vectors would make the difference of two codewords supported on at most three vertices. The distance assumption forces that difference to vanish; the remaining coordinates recover v and b. Thus 2^k · 2n distinct vectors fit among the 2^n binary vectors, which gives the bound.

[Lean proof](../../results/proofs/9ac88942c01475fa26ce85b2e3853819eaa8f17e61d13f6cdbc5c519d5733c5c.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_b019db4c751eaa507b7c

**Meaning.** For a bipartite graph with a nonzero adjacency code and unique-neighbor radius at least six, the stated cubic expression in n cannot exceed 2^((n − k)/2).

**Proof idea.** Choose the larger color class, of size a ≥ n/2. Map every subset of that class with at most three vertices to its adjacency image. A collision gives a nonempty symmetric difference of size at most six with zero image, contradicting its unique neighbor. Hence 1 + a + binomial(a,2) + binomial(a,3) ≤ 2^r, where r is the rank of the matrix between the classes. The bipartite block form gives n − k = 2r. Expanding the count and using a ≥ n/2 yields the polynomial.

[Lean proof](../../results/proofs/9c5000533d4f3eadcadd27a2adf172b80efb50598ca9726d579894afa61b47d9.lean#L337) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_b25136df53f5aa6f52de

**Meaning.** In a connected regular graph of degree two with a nonzero adjacency code, dimension and minimum weight multiply to the graph order: kd = n.

**Proof idea.** The proof uses the degree-two bound kd ≤ n. To reverse it, label each vertex by its coordinate evaluation on all codewords. The two neighbors of any vertex have the same label. Connectivity propagates at most two labels, and counting edges makes their classes equally large when distinct. Indicators of the classes are independent kernel vectors, so k is at least their number. Every nonzero codeword contains an entire class in its support, so d is at least their common size. Consequently n ≤ kd.

[Lean proof](../../results/proofs/8c867a4cf715fe5be5889dd2d9ee30e90315da0a87c5d68b6b877a1310aec8ac.lean#L557) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_b3dcf100435ee5144e0c

**Meaning.** For a bipartite graph with no isolated vertices, a nonzero adjacency code, and d ≥ 3, both 2Δ and n + 2 − 2Δ are at most 2^((n − k)/2). Here Δ is the maximum degree.

**Proof idea.** Distance three makes the images of the empty set and individual vertices distinct. At a chosen vertex, partition these images by whether that coordinate is zero or one. Adding an adjacent column flips the coordinate and gives disjoint translated copies. Applying this count separately to both color classes bounds the degree and the number of nonneighbors on each side. The two side maps have the same rank r, while the full adjacency map has rank 2r. Summing the side bounds gives the second expression.

[Lean proof](../../results/proofs/60fc363e3d54cf4311638220378b4fd07cdb8f07f267f4a0ddad69f47a09eb9f.lean#L1361) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_bd745c7d8b877a7a34e8

**Meaning.** Let δ be the common degree of a regular graph, with δ ≥ 1, a nonzero adjacency code, and d ≥ 3. Writing p for its parity gives n + 1 − p − δ ≤ 2^(n − k − 1 − p).

**Proof idea.** Distance three makes all adjacency columns distinct; positive degree makes them nonzero. For even δ, take zero and the nonneighbor columns of a fixed vertex. Translating by a neighboring column gives a disjoint second copy. For odd δ, the sum of a column’s coordinates is one, providing a second binary label and four disjoint copies of the nonneighbor columns. Counting these vectors in the adjacency image and using its dimension n − k gives the respective bounds.

[Lean proof](../../results/proofs/5d12b6ab26b4f615fe0f4004a0139de2b7320f90738275d60f17fa4e738de9f6.lean#L1103) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_c0b68b8f55a47e0a3735

**Meaning.** For every graph, the twice-edge count satisfies 2m ≤ (n − k)Δ², where m is the number of edges and Δ the maximum degree. Thus a large edge count requires enough independent adjacency columns.

**Proof idea.** Select r columns spanning all adjacency columns, with r = n − k by rank–nullity. The union of the selected vertices’ neighborhoods has at most rΔ vertices. Outside that union every selected column vanishes, hence every column vanishes there; those vertices are isolated. The degree sum is therefore supported on at most rΔ vertices, each of degree at most Δ. The degree-sum identity 2m = Σ degree then gives 2m ≤ rΔ².

[Lean proof](../../results/proofs/8ee765d4aae27c744108f2cf68d2fac1fad710a2a2bb818d2b1bb005a2c2deb4.lean#L148) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_c445ee6b05c501ffd5f3

**Meaning.** For a nonzero adjacency code, 2d(1 − 2^(−k)) ≤ n. This compares the smallest nonzero weight with the average weight of all 2^k codewords.

**Proof idea.** At each coordinate, at most half the codewords are nonzero. If any codeword is nonzero there, translating by it sends the nonzero group injectively into the zero group. Summing over coordinates bounds twice the total codeword weight by n · 2^k. On the other hand, the 2^k − 1 nonzero codewords each have weight at least d. Combining these counts and dividing by 2^k proves the inequality. The proof derives both counts directly from the kernel subspace.

[Lean proof](../../results/proofs/218721598b2b4d1330fffb22c9c925c52021231848d2f05ff07e34cee954bfbf.lean#L58) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_c8537defc43c08b8b928

**Meaning.** For a forest of maximum degree at most two with a nonzero adjacency code, k(2d − 1) ≤ n. Each independent code coordinate needs a component with at least 2d − 1 vertices.

**Proof idea.** Choose an endpoint in each tree component. Kernel equations force its neighbor to vanish and propagate alternating coordinate evaluations along the component. Recording endpoint values on components where that evaluation is nonzero determines every codeword, so k is at most their number. On each such component, its nonzero-class indicator is a codeword of weight at least d. The tree edge count and the degree-two equations show that component has twice this class size minus one vertices. Their disjoint sizes add to at most n.

[Lean proof](../../results/proofs/85b1202fd0c13cd5de40f9df7f959cb00970d578dd5f2cca11b87ca7d0c904d0.lean#L715) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_ceb714b3b8492a9c6002

**Meaning.** For a bipartite regular graph with common degree δ ≥ 2 and k ≥ 3, the distance bound depends on the parity of δ. Even degree gives 4d ≤ n; odd degree gives 4d(1 − 2^(−k/2)) ≤ n.

**Proof idea.** For odd degree, the regular bipartite averaging bound applies under positive degree and dimension. For even degree, the all-ones vector is in the kernel, and both color classes have size n/2. Their indicators span at most two dimensions. Since k ≥ 3, another codeword has a nontrivial projection onto one class. That projection and its complement within the class are nonzero codewords whose weights add to n/2. Each weight is at least d, giving 4d ≤ n.

[Lean proof](../../results/proofs/dd170f91b3d67de71a35d236572f845f0afe3dad0e3d562e25880b65c0b2bd21.lean#L933) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_cfda7a879c33977862b8

**Meaning.** Assume minimum degree δ ≥ 1, maximum degree at least two, a nonzero adjacency code, and u ≥ 2. Then (δ + 1)k ≤ 2m − n, so dimension is limited by the degree sum beyond n.

**Proof idea.** Choose a basis of adjacency columns indexed by a set S of size n − k. The unique-neighbor property for singletons and pairs makes the neighbor subsets inside S nonempty and distinct. At most |S| can be singletons; the others have at least two members. Their total size is therefore at least n + k. This is the sum of degrees on S. Its complement has k vertices, contributing at least δk more. The total degree sum is 2m.

[Lean proof](../../results/proofs/fd36c043a3852f368c587da9eac9c1711377440ee6618907d583f5311a86e813.lean#L1433) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d1a96951729d303c134a

**Meaning.** For a forest with Δ ≥ 1 and a nonzero adjacency code, k + 2⌈m/Δ⌉ ≤ n. The ceiling records how many bounded-size batches are needed to account for the edges.

**Proof idea.** Repeatedly remove a leaf and its neighbor. A kernel vector is determined by its values on the remaining vertices: the leaf equation sets the neighbor value to zero, and the neighbor equation recovers the leaf value. Thus restriction is injective into the smaller forest’s kernel. Each removal deletes two vertices and at most Δ edges. Induction produces a count t with k + 2t ≤ n and m ≤ tΔ. Since Δ is positive, ⌈m/Δ⌉ ≤ t, yielding the result.

[Lean proof](../../results/proofs/d95ed5e613495fd7a2b436a72c82a8556f76bb6150e98aa9f4382390bbdbb656.lean#L731) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d45ad2c0d7094fae13a3

**Meaning.** For a forest with maximum degree at most two and a nonzero adjacency code, k(2u − 1) ≤ 2m − n. This uses the unique-neighbor radius, which is defined even when it is zero.

**Proof idea.** The proof splits the forest into components and adds their vertex counts, edge counts, and kernel dimensions. For a connected component, the degree-two dimension formula and tree edge count show that its kernel dimension is zero or one. In the one-dimensional case, the bipartite radius bound gives 1 + 2u_component ≤ n_component. The global unique-neighbor property persists inside each component, so u ≤ u_component. The zero-dimensional case is handled separately. Adding the component inequalities proves the stated bound.

[Lean proof](../../results/proofs/c84aa01187fea819868a463da545f9e85a969659c2b2d9615bfd6a7d3ecd9d7c.lean#L1320) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d5876bce3d63a657ae5c

**Meaning.** For a regular graph of degree two with a nonzero adjacency code, kd ≤ n. Connectivity is not required: the argument counts coordinate classes across the entire graph.

**Proof idea.** Label each vertex by its evaluation function on the kernel. At every vertex, the two neighbor values must add to zero, so those neighbors carry equal labels. Consequently the indicator of any label class is a nonzero codeword. Every class therefore contains at least d vertices. Evaluating a codeword at one representative of each class determines it, giving an injective linear map into the binary functions on the classes and hence k ≤ the number of classes. Their disjoint sizes sum to n, proving kd ≤ n.

[Lean proof](../../results/proofs/5409309924b11f07db2c2891ff53a4d64d3687b291960bb9df396637213d4ee8.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d5cff71652de3b782468

**Meaning.** For a forest with a nonzero adjacency code, k + d ≤ α + 1, where α is the maximum size of an independent vertex set. The code effectively lives on an independent set.

**Proof idea.** First, the support of any kernel vector is independent. Otherwise its induced forest has a leaf whose adjacency equation has exactly one nonzero term, a contradiction. The union T of all codeword supports is also independent: if different codewords activate adjacent vertices, their sum supplies the same contradiction. Delete d − 1 coordinates from T. Restriction to the remaining coordinates is injective because a nonzero kernel vector cannot have weight below d. Thus k + d ≤ |T| + 1 ≤ α + 1.

[Lean proof](../../results/proofs/763bacd6cb43fb8a5ca4f1d23aa4ac65c5c3f97234c9608899ef3daf19b06c9b.lean#L820) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d70c85bd82968301a073

**Meaning.** For a graph with Δ ≥ 1, a nonzero adjacency code, and d ≥ 3, both Δ and n − Δ + 1 are at most 2^(n − k − 1).

**Proof idea.** Choose a maximum-degree vertex a and a neighbor b. Consider single-coordinate flips at neighbors of a, or zero together with flips at its nonneighbors. Each family has constant adjacency-image value at a. Adding either zero or the flip at b distinguishes two copies by that value. Combining these perturbations with all codewords remains injective: after recovering that binary choice, a collision would give a codeword of weight at most two. Their sizes are Δ and n − Δ + 1, so counting binary vectors proves both bounds.

[Lean proof](../../results/proofs/f7ed1e53bbf684c7790a2500a8d7d79ed29bb94d7093d9d914e01fdd26c7543e.lean#L803) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_d72c4575e624d63da528

**Meaning.** For a connected bipartite graph of maximum degree at most two with a nonzero adjacency code, k + 2d = n + 2.

**Proof idea.** The proof uses the bipartite upper bound k + 2d ≤ n + 2 and the nonzero-code bound d ≤ n. Project a minimum-weight codeword onto a color class containing a nonzero coordinate; its weight remains d. Its support S and neighborhood T cover the connected graph. Every vertex of T has two neighbors in S, so edge counting gives |T| ≤ |S| and n ≤ 2d. A strict inequality forces equality by integer arithmetic. In the balanced case the graph is degree-two regular, and the all-ones vector gives a second independent codeword, again forcing equality.

[Lean proof](../../results/proofs/bb5048d7dbbebe679a664647ccf62f3aea5fca57f6b221f7e496a18e8aee6928.lean#L835) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_dd843afc5379fbd73f35

**Meaning.** If k ≥ 3, then k + d + ⌈d/2⌉ + ⌈d/4⌉ ≤ n + 3. This relates three successive minimum weights to the available coordinates.

**Proof idea.** Choose a minimum-weight nonzero word and restrict the code to coordinates outside its support. The kernel of this restriction has dimension at most one, so the new code loses at most one dimension. Comparing a word and its sum with the chosen word shows that every nonzero restricted word has at least half the previous minimum weight, rounded up. Repeat this operation three times. The removed supports have sizes at least d, ⌈d/2⌉, and ⌈d/4⌉; the remaining dimension cannot exceed the remaining number of coordinates. Adding these inequalities gives the bound.

[Lean proof](../../results/proofs/5fe479bb12c6254e131e63b4d4c75c0da5b01205a7a4a77a3f51597e248372e9.lean#L125) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_de47993e34075cfd3cba

**Meaning.** For a regular graph of positive common degree δ, even δ guarantees k ≥ 1 when n is odd and k ≥ 2 when n is even. For odd δ, the parity expression reduces to k ≥ 0.

**Proof idea.** Rewrite each floor expression as a remainder modulo two. In the even-degree case, the all-ones vector is a nonzero kernel vector. If n is even and the kernel had dimension one, deleting one vertex would leave an invertible principal adjacency matrix of odd order. Expanding its determinant rules that out: inverse permutations have equal terms that cancel over GF(2), while a self-inverse permutation has a fixed point and hence a zero diagonal factor. This contradiction gives the second dimension.

[Lean proof](../../results/proofs/fa1e5fd0029a9c70610b169dd11bd957531557717e8abc85291f8bdc47610279.lean#L1443) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_dfaed9baaa0b19367366

**Meaning.** For a bipartite graph with a nonzero adjacency code, put t = ⌈k/2⌉. Then 4d(1 − 2^(−t)) ≤ n − k + 2t.

**Proof idea.** The code splits into kernels supported on the two color classes, with dimensions adding to k and a common adjacency-block rank r = (n − k)/2. One side has dimension at least t. Set enough of that side’s coordinates to zero to remove its excess dimension; the resulting subcode still has dimension at least t and uses r + t coordinates. Averaging its codeword weights bounds 2d(1 − 2^(−t)) by r + t. Doubling and substituting for r gives the conclusion.

[Lean proof](../../results/proofs/05e628f11c9064383e1d2ddf3ea7439834e8cc712b815d51ae4efd72b7b2a409.lean#L959) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_e2fedcd7edb750c79aa1

**Meaning.** For a forest with k ≥ 2, k + 2(d + ⌈d/2⌉) ≤ n + 4. The forest assumption supplies the additional case at dimension two.

**Proof idea.** When k ≥ 3, the proof applies the corresponding bipartite distance bound, since every forest is bipartite. For k = 2, choose independent codewords x and y. Forest kernel vectors have independent supports, and this also makes the union S of their supports independent. The three words x, y, and x + y have total weight at most 2|S|, so 3d ≤ 2|S|. The adjacency map from S to its complement has kernel dimension at most two, giving 2|S| ≤ n + 2. These inequalities imply the required ceiling bound.

[Lean proof](../../results/proofs/87bc8029bda46e6f9397166972f0335190c966b082083f65b3d32f7dcfb83b82.lean#L309) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_e81886cff56180757296

**Meaning.** For a connected graph with maximum degree Δ ≥ 2 and a nonzero adjacency code, (Δ − 1)k ≤ (Δ − 2)n + 2.

**Proof idea.** Start with the two independent adjacency columns of an edge. Extend a set S of independent columns while controlling the union U of their neighborhoods by |U| ≤ (Δ − 1)|S| + 2. If U does not cover the graph, connectivity supplies an edge across its boundary. The inside endpoint’s column is independent, because its outside coordinate is nonzero where the chosen columns vanish. Adding it enlarges U by at most Δ − 1. A maximal choice therefore covers all vertices. Using |S| ≤ n − k and rearranging proves the bound.

[Lean proof](../../results/proofs/30727d5795a71bf5435e5936d176acb65992fea3d171c58254639c6b64110b31.lean#L1114) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_e8a4faa6fbd8ed9be99d

**Meaning.** For a bipartite graph with a nonzero adjacency code, k + 2u ≤ n. The unique-neighbor radius forces at least 2u independent adjacency constraints.

**Proof idea.** A kernel vector supported on at most u vertices must vanish, since its nonempty support would have a unique neighbor. Project a nonzero codeword onto one color class; this remains a nonzero codeword, so that class has more than u vertices. Choose u of them. Their adjacency map into the opposite class is injective, proving that class has at least u vertices too. Choose u there as well. The two image spaces occupy opposite classes and cannot cancel, giving an injective map of dimension 2u into the adjacency image. Rank–nullity finishes the argument.

[Lean proof](../../results/proofs/e04b7f5f4fb1e5ab3f1130836394c1d56bdce5a92b7c57b8e2d6dd384bfd1f29.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_eabebff9b71f02bee112

**Meaning.** For a bipartite graph with k ≥ 7, the sum d + ⌈d/2⌉ + ⌈d/4⌉ + ⌈d/8⌉ appears twice in the bound k + 2 times that sum ≤ n + 8.

**Proof idea.** Restrict the code to the color classes. Their kernel dimensions sum to at least k, so one is at least four. The proof establishes a repeated projection inequality for a binary code: remove a minimum-word support, lose at most one dimension, and retain minimum weight at least the rounded-up half. Four steps give side_dimension plus the four-weight sum ≤ side_size + 4. The adjacency blocks have equal rank r, so r is at least that sum minus four. Combining k + 2r ≤ n gives the result.

[Lean proof](../../results/proofs/9dbec4f32ec522bbae0419f033c7552260c718c6b142344e25a8ebf939717bcf.lean#L1086) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_eccaeecd0caf8e058231

**Meaning.** For a graph with a nonzero adjacency code and u ≥ 4, 1 + n(n + 1)/2 ≤ 2^(n − k). The left side counts all vertex subsets of size zero, one, or two.

**Proof idea.** The unique-neighbor condition for nonempty sets of size at most four excludes every nonzero kernel vector of weight at most four. Map each subset of size at most two to the adjacency image of its indicator. If two images coincide, their indicator difference is a kernel vector supported on at most four vertices, hence zero; the subsets must coincide. The image space has 2^(n − k) elements by rank–nullity. Counting the subsets gives 1 + n + binomial(n,2), equal to the displayed expression.

[Lean proof](../../results/proofs/0d2224c96d1c49ead63dda0976914aae8966fe6effdaf0718bea7e20b4ca8be2.lean#L337) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_f625da6cfd36c5bd35d9

**Meaning.** For every graph, k + 2⌊ω/2⌋ ≤ n, where ω is the largest clique size. An even-sized portion of a clique contributes that many unavoidable independent adjacency constraints.

**Proof idea.** Choose a clique subset S of size 2⌊ω/2⌋. Suppose a kernel vector is supported on S. At each vertex of S, the adjacency equation says that its value equals the sum of all values on S. Thus all its values there are equal. Because |S| is even, their sum is zero over GF(2), forcing every value to vanish. Restriction of the full kernel to the vertices outside S is therefore injective. Its target has dimension n − |S|, which proves the bound.

[Lean proof](../../results/proofs/f5d62b37943fb4d25da12240a08f6e4a871617901de0be390e3c67d5176ed483.lean#L895) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_f62f129648dab0844b7e

**Meaning.** For a nonzero adjacency code, k + d ≤ n + 1. Larger minimum weight leaves fewer coordinates available for independent codewords.

**Proof idea.** Remove any d − 1 coordinates, and restrict kernel vectors to the remaining coordinates. If a vector maps to zero, its support is contained in the removed set. A nonzero such vector would have weight at most d − 1, contradicting the defining minimum d. The restriction is therefore injective. Its target is the space of binary functions on n − d + 1 vertices, whose dimension is that vertex count. Hence k ≤ n − d + 1. The proof also checks the positivity and sentinel bounds needed to choose the removed set.

[Lean proof](../../results/proofs/c0d6225b4ad1595dfe739d502261ca8d1db448f9faee0cba47e77c59d276c8d6.lean#L120) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_f77e93b699329a958881

**Meaning.** For a bipartite graph with no isolated vertices, Δ ≥ 2, and a nonzero adjacency code, k + 2d + 2⌈k/(2(Δ − 1))⌉ ≤ n + 4.

**Proof idea.** The two color-class kernels have a common block rank r, and one has dimension at least k/2. Its parity-check rows each use at most Δ coordinates, and every coordinate occurs in a row. The proof chooses a row basis and counts unions of its supports. Ruling out short nonzero vectors gives the local inequality side_dimension ≤ (Δ − 1)(r + 2 − d). Thus the integer r + 2 − d is at least the ceiling in the statement. Combining this with k + 2r ≤ n yields the bound.

[Lean proof](../../results/proofs/6ff1567ee82a1ce820b8999b68f00c270ba5b81ffe77c3848903c6190890951b.lean#L934) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_f802d84309924757f734

**Meaning.** For a forest of maximum degree at most two with a nonzero adjacency code, 2k(d − 1) ≤ m. The minimum-weight requirement therefore consumes edges as well as vertices.

**Proof idea.** Group vertices by their equal nonzero evaluation functions on the code. These classes determine codewords, so their number is at least k; each indicator is a codeword with at least d vertices. Forest structure makes active vertices independent. Their neighboring check vertices have degree two and belong to only one class. Delete one representative from a class: mapping the remaining coordinates to its checks is injective, so it needs at least d − 1 checks. The classes’ checks are disjoint and independent; each contributes two distinct edges. Counting gives the result.

[Lean proof](../../results/proofs/4c134876d1374d2642282c0e848d178096e789eaf75774bfe1e95faef0dd2637.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_f8571bfd6c9f0cfa3cdf

**Meaning.** For a forest with at least one edge and a nonzero adjacency code, its graph energy E, the sum of absolute adjacency eigenvalues, satisfies E² ≤ 2m(n − k).

**Proof idea.** The proof first removes leaf–neighbor pairs to show that adjacency nullity is the same over the reals and over GF(2): each removal preserves kernel dimension over either field, and an edgeless graph has the same dimension over both. Thus the real adjacency matrix has n − k nonzero eigenvalues. Spectral diagonalization and the degree-sum identity give the sum of their squares as trace(A²) = 2m. Applying Cauchy–Schwarz to their absolute values yields E² ≤ (n − k) · 2m.

[Lean proof](../../results/proofs/00e90a5a4c0fcf8454f10c3dc73bb21053a3d252832153dace1b96dfc44c4f9d.lean#L1120) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_fcd0348bfb1dad4c00a3

**Meaning.** For a forest with a nonzero adjacency code, d ≤ (n + 1)/2. The argument constructs a nonzero kernel vector whose support occupies at most that many vertices.

**Proof idea.** Use the forest’s two-coloring and select a color class where some codeword is nonzero. If this class is no larger than the other, its projected codeword already has small enough support. Otherwise choose a subset containing one more vertex than the opposite class. Its adjacency map into that class has more input coordinates than output coordinates, so it has a nonzero kernel vector. Extending that vector by zero gives a full adjacency codeword. In either case its weight is at most (n + 1)/2, and d is no greater.

[Lean proof](../../results/proofs/61a7d5186212bdeabf44a935400b1af85999affc06803342e094fd360dbfc338.lean#L733) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_fcf51e36faf8ebb9be9b

**Meaning.** For every forest, k ≤ 2α − n, where α is its largest independent-set size. Some independent set therefore has at least (n + k)/2 vertices.

**Proof idea.** The proof uses induction on induced subgraphs. If there are no edges, take all remaining vertices. Otherwise find a leaf and remove it together with its neighbor. Restricting the adjacency kernel to the remaining graph is injective: the leaf equation forces the neighbor value to zero, and the neighbor equation recovers the leaf value. Apply induction to the smaller graph, then add the removed leaf to its independent set. Two vertices were removed but one independent-set vertex is restored, preserving k + n ≤ twice the set size. Finally bound that size by α.

[Lean proof](../../results/proofs/4996f09d0e12bbf31d2bba70e6d35341530b8a265b5d36bc8caa311f14d2c468.lean#L732) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## nonzero_parity_code_distance_le_order

**Meaning.** If the adjacency code has positive dimension, its minimum nonzero weight d is at most n. The condition guarantees that an actual nonzero word exists, so the fallback value n + 1 cannot determine the minimum.

**Proof idea.** Positive kernel dimension supplies a nonzero kernel vector. Its Hamming weight counts a subset of the n vertices and is therefore at most n. That weight belongs to the finite set used to define d, so d is at most the chosen weight. Combining these two inequalities proves d ≤ n. The proof obtains the vector from the finite-dimensional kernel and then uses only support counting.

[Lean proof](../../results/proofs/2941dfaebf44d4fb092549c1fc7e3a6ca624aebc2b53805844254ee630b5230b.lean#L40) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## parity_code_dimension_le_order

**Meaning.** For every finite graph, the adjacency-code dimension k is at most the vertex count n. Each codeword has one binary coordinate per vertex, so its independent degrees of freedom cannot exceed the number of coordinates.

**Proof idea.** The adjacency kernel is a linear subspace of the space of all functions from the vertices to GF(2). The subspace dimension bound places its dimension below that of this ambient function space. The latter has dimension n, with one independent coordinate function per vertex. The proof combines these two facts and converts the natural-number inequality to the real-valued form used in the statement.

[Lean proof](../../results/proofs/777bd7350fe65b0bff26a45dbfd0148c3bfac6d2ad5178f482f2e0a38445b36e.lean#L40) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## parity_code_unique_neighbor_distance

**Meaning.** For every graph, u + 1 ≤ d. A nonzero adjacency codeword cannot be supported on a vertex set that has a unique neighbor.

**Proof idea.** Take the support S of a nonzero kernel vector. It is nonempty, and its size is the word’s weight. If a vertex had exactly one neighbor w in S, its adjacency sum would be the single nonzero value at w, contradicting the kernel equation. Thus S is among the sets used to define the smallest failure size for the unique-neighbor property. That minimum is no greater than every nonzero codeword weight. Both minima include the same fallback n + 1, and the failure minimum is positive, giving u + 1 ≤ d.

[Lean proof](../../results/proofs/fde0354b867d056aae097fff88d93a337f1d9e5eeb071b5a9404cc3e042f9e9a.lean#L12) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## unique_neighbor_radius_nonnegative

**Meaning.** For every graph, the unique-neighbor radius u is nonnegative. This remains true for the empty graph and when no nonempty set fails the unique-neighbor condition.

**Proof idea.** The definition takes the smallest failure size, with the fallback n + 1 included, subtracts one as a natural number, and then regards the result as a real number. Natural-number subtraction always produces a natural number, even before any property of the graph is considered. Every natural number has a nonnegative real value. The proof applies precisely this elementary positivity fact; it does not need to analyze the graph’s neighborhoods.

[Lean proof](../../results/proofs/4690d286ebe37fc348de7cc175e35c85165f7c74b14c9e12a42d3c68c0d7912a.lean#L12) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)
