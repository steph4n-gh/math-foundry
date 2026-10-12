# Adjacency codes and unique neighbors — explanations, part 2

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

These are informal explanations of the linked Lean statements and proofs. The full statement links retain the exact premises and frozen assessments.

For a finite simple graph, let $n$ be its number of vertices and $m$ its number of edges. Its binary adjacency code is the kernel of its adjacency matrix over $\mathrm{GF}(2)$, the field with two elements: a codeword assigns zero or one to each vertex so that every vertex has an even number of neighbors assigned one. Write $k$ for the code dimension and $d$ for the minimum number of ones in a nonzero codeword. The exact definition includes an $n+1$ fallback, so $d=n+1$ when there is no nonzero codeword.

A nonempty set $S$ has a unique neighbor when some vertex has exactly one neighbor in $S$; that vertex need not lie outside $S$. A stopping set is a nonempty set with no such vertex. The unique-neighbor radius $u$ is one less than the smallest stopping-set size, using $n+1$ as the fallback before subtracting one. Thus $u=n$ if no stopping set exists. Write $\delta$ and $\Delta$ for minimum and maximum degree, $\alpha$ for largest independent-set size, and $\lambda_2$ for the stated normalized-Laplacian gap. For a connected graph, $m-n+1$ counts edges outside a spanning tree. Floors and ceilings round down and up, respectively; the source’s expressions $\exp(x\log2)$ equal $2^x$.

## model_4eddad5da0216e0d66b2

**Meaning.** For a forest with a nonzero adjacency code, the unique-neighbor radius is exactly one less than the minimum nonzero codeword weight: $u=d-1$. Thus the first set size at which a unique neighbor can fail coincides with the code distance.

**Proof idea.** The proof uses the parent theorem `model_9507736b3513f2c06029`, which establishes $d=u+1$ under the same forest and positive-dimension premises. It reverses that equality and moves the added one to the other side. The graph-theoretic work is contained in the parent result.

[Lean proof](../../results/proofs/747eea2845803254a8774dbbb51f54ca01647b277869b87afa010571f02334f9.lean#L465) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_50989e8eb15a8fad02e7

**Meaning.** If the adjacency code has dimension at least two, its dimension and distance satisfy $k+d+\lceil d/2\rceil\le n+2$. This limits how much minimum weight a binary code can retain while keeping several independent codewords.

**Proof idea.** Choose $k-2$ coordinates and restrict the code to them. Rank and nullity leave two independent codewords vanishing there. Those words and their difference are nonzero, so each weighs at least $d$. At each remaining binary coordinate their three weights contribute at most two. Hence $3d\le2(n-k+2)$; rounding $d/2$ upward gives the stated inequality.

[Lean proof](../../results/proofs/b4e6647b80e6f9776713e08eb3f92d3db33601bc7e1500923d8d0d1f1864b7ac.lean#L125) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_51eba1be302c229af8c6

**Meaning.** For a bipartite graph whose adjacency code has dimension at least five, $2k+7d\le2n+12$. The bipartition makes the restriction on distance stronger than a bound that treats all coordinates as one block.

**Proof idea.** Split the adjacency equations between the two color classes, using a rectangular matrix of rank $r$. The two side-code dimensions sum to at least $k$, so one is at least three. If that side has dimension $j$, impose zeros on $j-3$ selected coordinates. The resulting code has at least eight words; summing their weights gives $7d\le4r+12$. Rank and nullity also give $k+2r\le n$, completing the calculation.

[Lean proof](../../results/proofs/f70650e9251ab2c452b3c8fad440470d1cc8c165fb84826f13f085c2c0fe74d6.lean#L935) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_56fd438976032be55956

**Meaning.** For a connected graph with minimum degree at least two and a nonzero adjacency code, $(\delta-1)k\le2(m-n+1)$. The number of independent cycles bounds its code dimension, with a stronger restriction as the minimum degree rises.

**Proof idea.** Begin with the endpoints of an edge and enlarge a set of known vertex values. At a boundary vertex, choose values for all but one new neighbor; the adjacency equation determines the remaining value. An induction budgets these choices using the minimum degree and the sum of excess degrees. Restriction to the chosen coordinates is injective on the code. The degree sum $2m$ then turns that budget into the bound.

[Lean proof](../../results/proofs/9cce597887e0aa7da298d622ddac41839012161ad4a9d107500fc49301bdb36e.lean#L27) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_58528c34ec3c39380ad7

**Meaning.** If the graph is connected, has minimum degree at least three, and has a nonzero adjacency code, then $k\le m-n+1$. There can be no more independent codeword directions than the number of edges outside a spanning tree.

**Proof idea.** The proof constructs coordinates that determine a codeword. Starting from an edge, it adds a boundary vertex’s new neighbors, leaving one value to be recovered from its adjacency equation. An induction charges the chosen values against unvisited vertices and degree excess above three. The resulting coordinate restriction is injective. Summing degrees converts its size bound into $k+n\le m+1$, which is rearranged.

[Lean proof](../../results/proofs/6ec52c1f38cc76ac217f73fb8fbb68a9da11da1eeeed6674f32926f68a912e92.lean#L27) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_5c1b1cd577e96807f60f

**Meaning.** For a graph with no isolated vertices, maximum degree at least one, and a nonzero adjacency code, $k+2\lceil n/(2\Delta)\rceil\le n$. The number of vertices therefore imposes a minimum loss of code dimension when degrees are bounded.

**Proof idea.** First prove that a symmetric binary matrix with zero diagonal has even rank, by eliminating two coordinates at a time. Choose a basis from the adjacency columns. Their supports cover every vertex, since there are no isolated vertices, and each support has size at most $\Delta$. Thus $n\le\Delta(n-k)$. The even rank makes $(n-k)/2$ an integer, allowing the quotient to be rounded upward.

[Lean proof](../../results/proofs/beb9bbca0f5fb9a0515de4e5960673edddee09d9fc2155b49e2f84aceb230d92.lean#L1093) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_5e76b721dff9cc8391a8

**Meaning.** For a bipartite regular graph of positive degree with a nonzero adjacency code, $4d(1-2^{-k/2})\le n$. Larger dimension forces the distance toward a stricter fraction of the graph order.

**Proof idea.** Positive regular degree makes the two color classes equally large. Projecting codewords onto either class preserves the adjacency equations, and one of the resulting subcodes has dimension at least $k/2$. Each coordinate is nonzero in at most half its words, while every nonzero word has weight at least $d$. Comparing total weights gives a bound involving the reciprocal number of subcode words. That number is a power of two, yielding the displayed factor.

[Lean proof](../../results/proofs/0ebf383fe4f3d983f59ffd37dab2aa5f61355046b6ce632dff0a7b5e4149e093.lean#L556) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_639525f7a46b1b3dbd00

**Meaning.** For a bipartite graph with a nonzero adjacency code and distance at least four, $n\le2^{(n-k)/2}$. The graph cannot have too many vertices relative to half the number of independent adjacency equations.

**Proof idea.** On either color class, choose an anchor and form twice as many binary vectors as vertices: a singleton indicator, optionally changed at the anchor. Distinct vectors differ in at most three coordinates, so the distance premise prevents them from having the same adjacency image. Both side images have dimension $r$, the rectangular adjacency rank. Counting their possible images gives $2|S|,2|T|\le2^r$. Finally $n-k=2r$.

[Lean proof](../../results/proofs/f512c8a1196be73b6ab5279df1bcadc956de7daa9ccc1818bc99ca7326dee556.lean#L1144) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_63cbbf2849b9c52dbcc9

**Meaning.** For a connected graph with a nonzero adjacency code, $k\le2\alpha-n+2(m-n+1)$. This compares code dimension with the largest independent set, allowing a correction for edges beyond a spanning tree.

**Proof idea.** Choose a spanning tree and remove one endpoint of each extra edge. The remaining induced graph is a forest, and at most $m-n+1$ vertices were removed. Its adjacency matrix is a submatrix, so the original code dimension is at most its dimension plus the number removed. The parent `model_fcf51e36faf8ebb9be9b` bounds forest dimension by twice independence number minus order. Independence cannot increase beyond that of the original graph; combining these bounds gives the correction.

[Lean proof](../../results/proofs/36db0ab83c3001665a7489d895da4e794299c7ea7379fd2aeed2793c4b1ca23e.lean#L925) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_64b918fcd8a802d68329

**Meaning.** Under connectedness, regularity, $n\ge2$, and the source’s normalized-Laplacian gap condition $\lambda_2>1.0000001$, the code dimension is the parity of $n$: zero for even order and one for odd order.

**Proof idea.** The spectral premise makes the Laplacian quadratic form strictly larger than squared length on vectors orthogonal to its lowest eigenvector. If two vertices were nonadjacent, a vector supported on them would violate that inequality. Hence every pair of distinct vertices is adjacent. The adjacency equations of this complete graph force every codeword to be constant. A nonzero constant word satisfies them exactly when $n$ is odd, giving the dimension formula.

[Lean proof](../../results/proofs/6c8504e970b9701a0d6546ec06b77f28311c6b8ff9f29e361233c0a15779ce22.lean#L1135) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_6609825288e9b0c185f3

**Meaning.** If the minimum degree is at least two and the adjacency code is nonzero, $u+\delta\le n+1$. A graph with larger minimum degree must contain a set lacking a unique neighbor at a smaller size.

**Proof idea.** Remove any $\delta-2$ vertices and let $S$ be the complement. It is nonempty. If a vertex had exactly one neighbor in $S$, all its other neighbors would lie among the removed vertices, giving degree at most $\delta-1$, a contradiction. Thus $S$ is a stopping set of size $n-\delta+2$. The smallest stopping-set size is $u+1$, so the required upper bound follows.

[Lean proof](../../results/proofs/b42bca453fbe80bf2cdb5b944d99259034997ee10879b0682e0a2371aeb03b9e.lean#L418) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_6a99e9dbd16d921e7d7c

**Meaning.** For a bipartite graph with a nonzero adjacency code and $d\ge3$, $n/2+1\le2^{(n-k)/2}$. This bounds the order using half the number of independent adjacency equations.

**Proof idea.** On each color class, consider the zero vector and all singleton indicators. Two distinct such vectors differ in at most two coordinates, so distance at least three forces distinct adjacency images. If the rectangular matrix between the classes has rank $r$, each image space has exactly $2^r$ elements. Each class therefore has at most $2^r-1$ vertices. Adding these bounds and using $n-k=2r$ proves the claim.

[Lean proof](../../results/proofs/97721d0b1464d4c7ac74d5fd9034fa36c4c00c3141fde32b7a2870b762bca26f.lean#L1178) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_6c69a9fac94e8d24072f

**Meaning.** For a bipartite regular graph with minimum degree at least two and a nonzero adjacency code, $2u+\max(k,2\delta-2)\le n$. Both code dimension and degree place limits on the unique-neighbor radius.

**Proof idea.** In each color class, deleting $\delta-2$ vertices leaves a stopping set, giving $u+\delta-1$ as a lower bound on that class’s size. Separately, choose $u$ vertices in each class. No nonzero codeword can be supported on their union: its nonempty support in one class would have a unique neighbor, contradicting an adjacency equation. Restricting codewords to the remaining $n-2u$ vertices is therefore injective. Combine the degree and dimension bounds using the maximum.

[Lean proof](../../results/proofs/d569432d3c26076518229b3a09edc6df4d8f3b9c8830d289c770ae7a8f2f68fb.lean#L43) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_6d91818f8f8347c7ef4c

**Meaning.** For a forest with no isolated vertices and a nonzero adjacency code, $(\Delta+1)k\le(\Delta-1)n$. This refines the dimension bound by using acyclicity as well as the degree limit.

**Proof idea.** The proof combines parent results algebraically. The two forest upper bounds and the general lower bound identify $k=2\alpha-n$. Another parent gives $(\Delta+1)\alpha\le\Delta n$ when there are no isolated vertices; substituting the identity gives the claim. The proof also supplies the parents $\Delta k\le(\Delta-1)n$ and $k\le n$, together with nonnegative graph counts, to its final inequality calculation.

[Lean proof](../../results/proofs/e7ac8271bcc045fae4421311d63173dc5e305da55a6eaff94212ad5589440bf9.lean#L488) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_7378e4999b7091aa506b

**Meaning.** For a connected graph of maximum degree at most two, the displayed formula determines $k$ from order parity and $m-n+1$. It gives parity of $n$ in the tree case and two minus that parity in the degree-two case.

**Proof idea.** If every degree is two, the parent `model_498663d70c6a4882faec` gives the dimension, and summing degrees gives $m=n$. Otherwise some degree is below two; connectivity and the edge count force a tree. Neighbor equations then show that one coordinate determines each codeword, so $k\le1$. Bipartition shows that $n-k$ is even. This fixes $k$ as the order parity, while $m-n+1=0$, completing the formula.

[Lean proof](../../results/proofs/094ba7bdb2a37479c678d3ec0adba0a5818b212640cac12d8009279b28ed9ba8.lean#L760) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_76e242812f261f42bd47

**Meaning.** For a bipartite graph with a nonzero adjacency code and $d\ge5$, $1+n/4+n^2/8\le2^{(n-k)/2}$. The distance premise requires enough independent adjacency equations to distinguish all sets of up to two vertices within each color class.

**Proof idea.** Map the indicators of the empty set, singletons, and pairs in each class through the adjacency matrix. Two different indicators differ in at most four coordinates, so they cannot have the same image. A class of size $a$ consequently satisfies $1+a+\binom a2\le2^r$, where $r$ is the rectangular adjacency rank. Combine the two class inequalities using the nonnegativity of their squared size difference, and use $n-k=2r$.

[Lean proof](../../results/proofs/93abe45cd02f7fcb4626349bf32219ea52d926c8ca0d76417206827797a4868d.lean#L337) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_77a1528e1be7c262c434

**Meaning.** For any graph with a nonzero adjacency code, $u\ge\min(2,d-1)$. In particular, distance at least three ensures that every nonempty set of one or two vertices has a unique neighbor.

**Proof idea.** A stopping set of size at most two has either zero or two neighbors at every vertex; exactly one is excluded by definition. Its binary indicator is therefore a nonzero codeword, and its size is at least $d$. If the smallest stopping-set size is at least three, then $u\ge2$ directly. Otherwise the indicator argument bounds $d$ by that size. The proof also handles the $n+1$ sentinel in the minimum.

[Lean proof](../../results/proofs/a907a6f3bdbe48d862bf1fb03166fea46e3c9f1d4728b00e7d1c0364ccfb7cea.lean#L90) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_786f11efe68814161b2e

**Meaning.** For a connected graph with minimum degree at least two and a nonzero adjacency code, $k\le\max(2,2(m-n+1)-1)$. The bound permits dimension two in the degree-two case and improves the cycle-count bound elsewhere.

**Proof idea.** The parent `model_7da27d5b31f5312db00b` gives $k\le2(m-n+1)$. If the maximum degree is at least three, `model_21f2572ddea1929363be` makes this inequality strict. Since all counts are integers, strictness saves one. If the maximum degree is below three, every degree equals two. The degree sum gives $m=n$, and the first parent bounds $k$ by two. Each case is bounded by the displayed maximum.

[Lean proof](../../results/proofs/6d9b43c3b2684e625152ed2709af002f27160f8fc60dccf831a19363bdb84295.lean#L609) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_795b4e4fa4acd67ccfeb

**Meaning.** For a forest with a nonzero adjacency code, $k=2\alpha-n$. Thus its code dimension is completely determined by its order and the size of a largest independent set.

**Proof idea.** The proof puts together two parent inequalities. `model_fcf51e36faf8ebb9be9b` gives $k\le2\alpha-n$ for a forest. `model_86d5f85f179c31163952` gives $k\ge2\alpha-n$ for every graph, without a forest assumption. The same real-valued quantity bounds $k$ from both sides, so the two inequalities yield equality. This target does no further graph or matrix construction.

[Lean proof](../../results/proofs/105fa93a9f7af9b15f654b8b733f231d71dec74db0b5489163015ea94f34d17c.lean#L1129) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_7bc785c375fbbdb773ee

**Meaning.** For a regular graph of positive degree with a nonzero adjacency code and $u\ge2$, write $p$ for the parity of its degree. The inequality is $(1+p)(n+1+p)\le2^{n-k}$: $n+1$ for even degree, and $2(n+2)$ for odd degree.

**Proof idea.** The radius premise makes the adjacency columns distinct; positive degree makes them nonzero. Counting these columns and zero gives the even-degree bound. For odd degree, each column has odd coordinate sum, occupying half the image space. Translation arguments show equality in the resulting count would force the regular degree to be even. Thus the count is strict; parity of the order and powers of two strengthen it to $2(n+2)$.

[Lean proof](../../results/proofs/6a2465e1ffe7c9f260e1ba905e0a4f28c86c99b16ec7ca6456728f42e93a4fb6.lean#L1304) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_7da27d5b31f5312db00b

**Meaning.** For a connected graph with minimum degree at least two and a nonzero adjacency code, $k\le2(m-n+1)$. The code dimension is at most twice the number of edges beyond a spanning tree.

**Proof idea.** Starting with an edge, grow a set of vertex coordinates that determine a codeword. At each boundary vertex, record all but one new neighbor value, then use the zero neighbor-sum equation to recover the last. The number of additional recorded coordinates is at most the total degree excess above two. Restriction to the recorded coordinates is injective on the code. The degree-sum identity makes their total at most $2m-2n+2$.

[Lean proof](../../results/proofs/d6466dafb61c813aa4503bdd3dccb2ad48b30c9e82b106e08f13609d793cfbf3.lean#L1223) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_7f5a8625a28664c18ff7

**Meaning.** For a forest with a nonzero adjacency code, $u+1=d$. The minimum number of selected vertices that can lack a unique neighbor equals the smallest nonzero codeword weight.

**Proof idea.** The parent `model_9507736b3513f2c06029` proves $d=u+1$ with precisely these forest and positive-dimension premises. This proof reverses the equality, putting the radius expression on the left. All substantive comparison between stopping sets and codewords has already been supplied by that parent; the target changes only the direction in which the same identity is written.

[Lean proof](../../results/proofs/639387e86d6e956a7c473f20f4b767cec66f8aa0b764ff799b3fc9476de4cc83.lean#L703) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_7f80b6911ecd9dc4c880

**Meaning.** For every finite simple graph, $n-k$ is even. Equivalently, twice the floor of $(n-k)/2$ is exactly $n-k$. This says that the binary adjacency matrix has even rank, including when its kernel is trivial.

**Proof idea.** The proof establishes a more general statement for every symmetric binary matrix with zero diagonal. If it is nonzero, choose a nonzero off-diagonal entry and remove its two coordinates. A corrected matrix on the remaining coordinates is still symmetric with zero diagonal, and restriction gives an equivalence between the two kernels. Induction therefore reduces the size by two without changing nullity. The zero-matrix case starts the induction, proving even rank.

[Lean proof](../../results/proofs/dc4351b61c09866f6e08d6ec1b9e34570ad3c3882152ea7ca9c6c87c17d2043e.lean#L119) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_80d52b930d57ba66abee

**Meaning.** For a connected graph with a nonzero adjacency code, the displayed correction bounds $d$ by $u+1$ when $m\le n$, and by $n$ when $m\ge n+1$. The edge-count factor selects these two cases.

**Proof idea.** In the second case, the parent `nonzero_parity_code_distance_le_order` supplies $d\le n$. In the first, a spanning tree leaves at most one extra edge, so every induced subgraph has at most as many edges as vertices. For a stopping set, this forces its neighbor set to be no larger. A rectangular adjacency matrix then has a nonzero kernel; in the equal-size case every row has two ones. Extending a kernel vector gives $d\le u+1$.

[Lean proof](../../results/proofs/e3730b614eaf40689d490049160378a39e121af4dbb3e8e2b76ebfac3279070e.lean#L393) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_839d3b7a6b536e9e20f2

**Meaning.** For a bipartite graph with code dimension at least three, $k+2(d+\lceil d/2\rceil)\le n+4$. Both the distance and its rounded half consume part of the dimension budget.

**Proof idea.** Split the code into the kernels of the rectangular adjacency matrix and its transpose. Their dimensions sum to at least $k$, so one is at least two. On that side, restrict to selected coordinates to retain two independent words vanishing there. Those words and their sum each weigh at least $d$, but their total coordinate contribution is at most two per remaining vertex. This gives $3d\le2r+4$. Combine rounding with $k+2r\le n$.

[Lean proof](../../results/proofs/1bb6b6aeb21782728e5a4c07ac80bcb0cb3ef4afbd6f426446ae91945a7a0209.lean#L470) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_8507aba979de2b196665

**Meaning.** For every finite simple graph, taking the floor of $(n-k)/2$ leaves it unchanged. Half the binary adjacency rank is already an integer, so rounding downward loses no information.

**Proof idea.** The parent `model_7f80b6911ecd9dc4c880` states $n-k=2\lfloor(n-k)/2\rfloor$, the even-rank identity for the adjacency matrix. The proof applies that parent and rearranges its equality by dividing the two sides by two. No graph hypotheses or additional rank argument are needed: the integral half-rank was established by the parent theorem.

[Lean proof](../../results/proofs/85bf64b63850456cd5947c443d580c38c04e5b24578e8af542a3f28a1f6bd103.lean#L1150) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_86d5f85f179c31163952

**Meaning.** For every finite simple graph, $k\ge2\alpha-n$. A large independent set forces a lower bound on the dimension of the adjacency code; if the right side is negative, the inequality is simply a weak lower bound.

**Proof idea.** Choose a largest independent set $S$ and extend vectors on $S$ by zero. Their adjacency equations on $S$ vanish automatically because no edges lie inside $S$. Only the equations on the complement remain, so their rank is at most $n-|S|$. Rank and nullity leave a kernel of dimension at least $2|S|-n$. Extending these kernel vectors injectively into the full adjacency code gives the claim.

[Lean proof](../../results/proofs/e9155af480461627abdead4be3729328366d04d98bb49e5f3804748c5b26ffea.lean#L49) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_87e1404743f540083555

**Meaning.** For a bipartite graph with no isolated vertices, $\Delta\ge2$, and a nonzero adjacency code, $\Delta k\le(\Delta-1)(n+4-2d)$. This expresses a tradeoff between distance and dimension under a degree bound.

**Proof idea.** The parent `model_f77e93b699329a958881` gives $k+2d+2\lceil k/(2(\Delta-1))\rceil\le n+4$ under the same premises. The ceiling is at least its argument. Because $\Delta-1$ is positive, multiply the parent inequality by that number and replace the ceiling term by its lower bound. The resulting expression is rearranged to the displayed inequality.

[Lean proof](../../results/proofs/e4b2328959872a01a5d1b8f7ad48b56499c8390383cae0914b5a0ec5d10d5dbe.lean#L1009) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_8f47fc4afe05a5ce81a4

**Meaning.** If the maximum degree is at most two and the adjacency code is nonzero, $kd\le n$. Keeping more independent codeword directions therefore forces a proportionately smaller minimum weight.

**Proof idea.** Group vertices according to the coordinate function they define on the entire code. A degree-one equation makes its neighbor’s function zero; a degree-two equation makes the two neighbor functions equal. Consequently each nonzero function class has an indicator that is itself a codeword, so every such class contains at least $d$ vertices. These classes are disjoint. Evaluating codewords on one representative per class is injective, so there are at least $k$ classes, proving the bound.

[Lean proof](../../results/proofs/67fb6c1aa1e6636d3a63187b6459d2965b4828fd9c6b11c83cd41951c79442f8.lean#L143) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_92bb8eaf5887bd185218

**Meaning.** For a graph with $\Delta\ge1$ and a nonzero adjacency code, $k+2\lceil m/\Delta^2\rceil\le n$. The edge count limits code dimension once the maximum degree is fixed.

**Proof idea.** The parent `model_c0b68b8f55a47e0a3735` gives $2m\le(n-k)\Delta^2$. Another parent, `model_8507aba979de2b196665`, shows that $(n-k)/2$ equals its floor and hence is an integer. Divide the edge bound by the positive square $\Delta^2$ to get $m/\Delta^2\le(n-k)/2$. The ceiling of the left side remains below that integer. Doubling and rearranging gives the result.

[Lean proof](../../results/proofs/f07593953bc86aaad10e050bb312d724470be805e1e83b41bbf6c128eb33f0f4.lean#L1102) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_9507736b3513f2c06029

**Meaning.** For a forest with a nonzero adjacency code, $d=u+1$. The smallest obstruction to the unique-neighbor property is exactly the smallest nonzero codeword weight.

**Proof idea.** The parent `parity_code_unique_neighbor_distance` gives $u+1\le d$ for every graph. For the reverse inequality, take a stopping set and its nonempty part in one forest color class. Each neighbor has at least two neighbors in that part. A forest edge count forces fewer neighboring vertices than selected vertices, so the intervening rectangular matrix has a nonzero kernel. Extend a kernel vector by zero: it is a codeword supported within the stopping set. Taking minima proves equality.

[Lean proof](../../results/proofs/4a1115b1dfa3d474acfaab50a20266a85a9a3b656ea503fdf22c6aa9fc1c23ba.lean#L92) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_97ad1eb664d4628498d5

**Meaning.** For a graph with no isolated vertices, a nonzero adjacency code, and $u\ge4$, the larger of $\delta(n-\delta+1)$ and $1+n(n+1)/2-\delta(n-\delta+1)$ is at most $2^{n-k-1}$. These terms count two families of sets of size at most two.

**Proof idea.** Choose a minimum-degree vertex and split those small sets by the parity of their intersection with its neighborhood. Their two family sizes are exactly the displayed terms. The radius premise rules out nonzero codewords supported on at most four vertices. Within either family, combine a codeword, a set indicator, and an optional pulse at a fixed neighbor. This construction is injective; counting its possible binary vectors bounds each family by $2^{n-k-1}$.

[Lean proof](../../results/proofs/70d05d4af6ec0b6f6f9ce28d54576577fd2084256223108f821283cb30867ff0.lean#L1020) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_99552111b1048561a96c

**Meaning.** For a connected graph with maximum degree at most two and a nonzero adjacency code, $d\ge\lceil n/2\rceil$. Every nonzero codeword must occupy at least half the vertices, rounded upward.

**Proof idea.** First bound every nonempty stopping set $S$. A vertex adjacent to $S$ has exactly two neighbors, both in $S$; otherwise it would supply a unique neighbor. Connectivity makes $S$ together with its neighbors cover the graph. Count edges between $S$ and its complement: each complement vertex contributes two, while each vertex of $S$ contributes at most two. Thus $n\le2|S|$. The parent `parity_code_unique_neighbor_distance` gives $u+1\le d$, transferring this stopping-set bound to distance.

[Lean proof](../../results/proofs/7d946c0533bb7967316f6b4a8e2346629ac8963de0f6f57c91694ee5957229f5.lean#L399) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_9d72068d4e2555d140e4

**Meaning.** For a forest with maximum degree at most two and a nonzero adjacency code, $k+m\le n$. The adjacency code dimension and the number of edges together fit within the number of vertices.

**Proof idea.** Induct on graph order. If an edge exists, an endpoint of a longest path is a leaf. Delete that leaf and its neighbor. The leaf equation forces the neighbor’s codeword coordinate to vanish; the neighbor equation then recovers the leaf coordinate from the rest. Restriction therefore injects the old code into the smaller forest’s code. Two vertices and at most two edges have been removed, so the induction bound suffices. An edgeless graph uses $k\le n$.

[Lean proof](../../results/proofs/d83b4b37a951e82de2a810192d16dc86a7cbfdc4505010d3032ea620562a10da.lean#L889) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_a4e25367cbc12335da94

**Meaning.** For a bipartite graph with minimum degree at least two and a nonzero adjacency code, $u+\delta+\Delta\le n+1$. Bipartition adds the maximum degree to the restriction on the unique-neighbor radius.

**Proof idea.** Choose a maximum-degree vertex. Its color class has at least $\delta$ vertices, and the opposite class contains its $\Delta$ neighbors. Remove $\delta-2$ vertices from the first class. The remainder is a nonempty stopping set: a unique neighbor would force some vertex’s whole neighborhood into the removed set plus one vertex, contradicting minimum degree. Its size bounds $u+1$. Combining that bound with the size of the opposite class gives the inequality.

[Lean proof](../../results/proofs/2f0b6282a0acac1980a3ed29e6946bdec1d8b5a5276073e5c11d193308dda37b.lean#L120) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)

## model_a9caf9807603b6709b52

**Meaning.** For a forest with no isolated vertices, $\Delta\ge2$, and a nonzero adjacency code, $k+2d+2\lceil k/(\Delta-1)\rceil\le n+4$. Forest structure strengthens the combined degree, distance, and dimension restriction.

**Proof idea.** The proof shows that all vertices appearing in any codeword together form an independent set. The matrix between this set and its complement has rank $r$, with $k+2r\le n$. Its rows have at most $\Delta$ nonzero entries and no column is zero. A local counting argument chooses independent rows and uses the distance to bound coordinates outside their supports. It produces an integer $t$ with $d+t=r+2$ and $k\le(\Delta-1)t$. Thus the ceiling is at most $t$; substitution finishes the bound.

[Lean proof](../../results/proofs/a477f69ae17eacbd58b65a366600a978ac34d447fde6880a116a44369220fac5.lean#L1356) · [Full statement and frozen assessment](../../results/all-proofs.md#adjacency-codes-and-unique-neighbors)
