# Spectral bounds: explanations 1

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

These are informal explanations of the linked Lean statements, not separately certified proofs. All graphs here are finite simple graphs. Write $n$ for the number of vertices, $m$ for the number of edges, $\delta$ and $\Delta$ for minimum and maximum degree, and $\bar d=2m/n$ for average degree when $n>0$ (zero otherwise).

Let $A$ be the adjacency matrix, $D=\operatorname{diag}(d(v))$ the degree matrix, and $J$ the all-ones matrix. Write $\rho$ for the largest adjacency eigenvalue, $\eta$ for the smallest, $s=\rho-\eta$ for spectral spread, and $E=\sum_i|\lambda_i(A)|$ for graph energy. Write $q$ for the largest eigenvalue of the signless Laplacian $Q=D+A$, and $\mu_{\max}$ for the largest eigenvalue of $L=D-A$. These extreme eigenvalues are defined as zero on the empty graph. The complement $\overline G$ has the same vertices and exactly the missing edges between distinct vertices.

The normalized Laplacian is $\mathcal L=RLR$, where $R_{vv}=1/\sqrt{d(v)}$ for positive degrees and zero for isolated vertices. Write $\nu_{\max}$ for its largest eigenvalue, also zero on the empty graph. The normalized gap is its second-smallest eigenvalue for a connected graph with at least two vertices, and zero otherwise. Edge density is denoted by $p$, to distinguish it from $\rho$.

## chung_normalized_laplacian_gap_upper

**Meaning.** For a graph with $n\ge2$, the normalized Laplacian gap is at most $n/(n-1)$. Here the gap means its second-smallest eigenvalue when the graph is connected; the formal definition returns zero for a disconnected graph. The order assumption makes the denominator positive.

**Proof idea.** The normalized Laplacian is positive semidefinite and has a zero eigenvalue, since its determinant contains the Laplacian determinant. Its diagonal entries are at most one, so its eigenvalues sum to at most $n$. After removing the smallest, zero eigenvalue, each of the remaining $n-1$ eigenvalues is at least the second-smallest. Their sum therefore bounds $(n-1)$ times the gap.

[Lean proof](../../results/proofs/676e7f2d85277cbf931e43edab01cb52de57e6003d5a2065d487b8d98b2f063d.lean#L165) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_0c34eb85bacc4cdc

**Meaning.** The adjacency spectral spread $s=\rho-\eta$ is at most $n\Delta$: the range from the smallest adjacency eigenvalue to the largest is controlled by the vertex count times the maximum degree. This statement applies to every finite simple graph, including the empty graph under the stated zero conventions.

**Proof idea.** The target joins two proved inequalities: $s\le2\rho$ and $2\rho\le n\Delta$. The first compares an eigenvector with its coordinatewise absolute value to obtain $\eta\ge-\rho$. The second passes through energy: zero adjacency trace gives $2\rho\le E$, an orthonormal eigenbasis gives $E\le2m$, and the degree sum gives $2m\le n\Delta$.

[Lean proof](../../results/proofs/ff6cde983e0141a07caf02acfe9745af115f2c0410e14f3547ee3d61b63b5931.lean#L219) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_4f819129e1379926

**Meaning.** Twice the largest adjacency eigenvalue is at most $n\Delta$. Thus the adjacency spectral radius cannot exceed half the total capacity obtained by allowing every vertex to have maximum degree. No connectedness, regularity, or bipartiteness assumption is required.

**Proof idea.** The proof uses $2\rho\le E\le2m\le n\Delta$. Because the adjacency eigenvalues sum to zero, the absolute eigenvalue sum must cover twice the largest eigenvalue. To bound energy by $2m$, the parent expands eigenvalues in unit eigenvectors, applies $2|ab|\le a^2+b^2$ along edges, and sums over the orthonormal basis. Finally, summing degrees bounded by $\Delta$ gives $2m\le n\Delta$.

[Lean proof](../../results/proofs/4bddb53eeedf42c3df48972411061457bdef62c4c23ac52cf3adb4c7c9f0a375.lean#L114) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_5087f3d5606bb1bb

**Meaning.** The largest adjacency eigenvalue satisfies $2\rho\le n(1+\sqrt n)/2$. This bound depends only on the number of vertices and holds for all finite simple graphs. The target obtains it by comparing the spectral radius with the full adjacency energy $E$, rather than by bounding an individual matrix row.

**Proof idea.** Zero adjacency trace gives $2\rho\le E$. The energy parent forms a symmetric orthogonal matrix $S$ whose eigenvalues are their signs, choosing $+1$ at zero, so $E=\operatorname{tr}(AS)$. Writing $A=J/2+B$, every entry of $B$ has squared magnitude $1/4$. Two Cauchy–Schwarz estimates bound the $B$ contribution by $n\sqrt n/2$ and the $J$ contribution by $n/2$.

[Lean proof](../../results/proofs/4d524b11db47f8acd8324f59f56dfdbfaefe134cbbc48e50d2e58be8ad10d03e.lean#L175) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_9760f9b31100c13d

**Meaning.** The average degree $\bar d$ is at most $\rho+\Delta$. The expression combines the largest adjacency eigenvalue with the largest vertex degree, and the statement holds without assumptions on connectedness or regularity. The average degree is zero when there are no vertices.

**Proof idea.** The intermediate quantity is the largest eigenvalue $q$ of $Q=D+A$. Its eigenvalues sum to $\operatorname{tr}(Q)=2m$, so their maximum is at least $2m/n=\bar d$. For a unit eigenvector of $Q$, the adjacency part of its quadratic form is at most $\rho$, while the diagonal degree part is at most $\Delta$. Hence $\bar d\le q\le\rho+\Delta$.

[Lean proof](../../results/proofs/6de43cf7a3773490571489a8854f6a65885161fd9c6d39cc6178a0fa1d202e48.lean#L109) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_a8305e0fa5e3ee71

**Meaning.** The adjacency spectral spread satisfies $s\le\sqrt{2mn}$. It bounds the entire interval between the smallest and largest adjacency eigenvalues using the numbers of edges and vertices. The inequality holds for arbitrary finite simple graphs and becomes zero on the right for an edgeless graph.

**Proof idea.** The target first uses $s\le2\rho$, whose parent obtains $\eta\ge-\rho$ by replacing eigenvector coordinates with their absolute values. It then applies $2\rho\le E\le\sqrt{2mn}$. The energy lower bound uses zero adjacency trace. The upper bound follows from Cauchy–Schwarz and $\sum_i\lambda_i^2=\operatorname{tr}(A^2)=2m$, because each diagonal entry of $A^2$ is a vertex degree.

[Lean proof](../../results/proofs/37a2404eb4fc1f7c68a3a4d7f6a52304ec43118d3ed6af0ef655b724f8d3e8b4.lean#L202) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_b9a7629301cf0891

**Meaning.** Twice the largest adjacency eigenvalue is at most $\sqrt{2mn}$. This estimate uses both the edge count and the vertex count, with no connectedness or structural assumption on the graph. All the quantities are interpreted as real numbers in the comparison.

**Proof idea.** The proof places energy between the two sides: $2\rho\le E\le\sqrt{2mn}$. The first inequality follows from the zero sum of adjacency eigenvalues. For the second, Cauchy–Schwarz gives $E^2\le n\sum_i\lambda_i^2$. The spectral decomposition identifies the square sum with $\operatorname{tr}(A^2)$; its diagonal records vertex degrees, whose sum is $2m$. Taking square roots gives the desired bound.

[Lean proof](../../results/proofs/31c6301564550fde7051b5971092b6f9145c0a1da6b30feaab1bf62514ef3916.lean#L97) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_c07d062305bdb36b

**Meaning.** The adjacency spectral spread satisfies $s\le n(1+\sqrt n)/2$. The smallest eigenvalue $\eta$ enters through $s=\rho-\eta$, so this is a bound on the whole adjacency spectrum rather than only its upper endpoint. It applies to every finite simple graph.

**Proof idea.** The target composes $s\le2\rho$ with the proved order-only bound for $2\rho$. The spread parent uses coordinatewise absolute values of eigenvectors to show $\eta\ge-\rho$. The radius parent uses $2\rho\le E$, then bounds energy using the spectral sign matrix, the decomposition $A=J/2+(A-J/2)$, and Cauchy–Schwarz. These estimates yield the chain $s\le2\rho\le E\le n(1+\sqrt n)/2$.

[Lean proof](../../results/proofs/1cd03338b7922e984e5acf66adb76aa1cacb7370b44352bcb2fdb21d50ad3b54.lean#L282) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## composed_f0d095cf27d0fbe6

**Meaning.** The minimum degree $\delta$ is at most $q$, the largest eigenvalue of the signless Laplacian $Q=D+A$. This is a lower bound on $q$ for every finite simple graph. It does not require the graph to be connected or to have constant degrees.

**Proof idea.** Two degree averages provide the link. Summing the inequalities $\delta\le d(v)$ gives $n\delta\le2m$, hence $\delta\le\bar d$ when $n>0$. The eigenvalues of $Q$ sum to its trace $2m$, so their largest member is at least $2m/n=\bar d$. The target takes the transitive consequence $\delta\le\bar d\le q$; the empty case is handled by the zero conventions.

[Lean proof](../../results/proofs/66c388af2913a91ce98b5e0e748867368165d5185f64e9f1e24d31616cd3bc9a.lean#L74) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## cvetkovic_signless_laplacian_max_deg

**Meaning.** The signless Laplacian radius satisfies $q\le2\Delta$ for every finite simple graph. Here $q$ is the largest eigenvalue of $D+A$, and $\Delta$ is the maximum vertex degree. No regularity hypothesis is needed for this upper bound; regularity is required in the separate lower bound that yields equality.

**Proof idea.** For each eigenvalue, choose a nonzero eigenvector coordinate of greatest absolute magnitude. The eigenvalue equation at that vertex is $\lambda x_v=d(v)x_v+\sum_{w\sim v}x_w$. The triangle inequality and coordinate maximality bound the right-hand side in absolute value by $2d(v)|x_v|$. Cancel the positive magnitude, use $d(v)\le\Delta$, and take the largest eigenvalue.

[Lean proof](../../results/proofs/e089c248e2db5496e4e3b6d46348ca0e58aa19ffba82189b264f0db59fd24865.lean#L247) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## das_signless_laplacian_order_size

**Meaning.** For a graph with $n\ge2$, the signless Laplacian radius obeys $q\le2m/(n-1)+n-2$. The positive denominator makes this an upper bound involving both order and size. Connectedness and regularity are not assumptions of this statement.

**Proof idea.** For a positive eigenvalue of $Q$, choose a vertex maximizing $|x_v|/d(v)$; isolated coordinates vanish. Its eigenvalue equation gives $\lambda d(v)\le d(v)^2+\sum_{w\sim v}d(w)$. A counting argument separates neighbors from nonneighbors and proves that $(n-1)$ times this row quantity is at most $d(v)[2m+(n-1)(n-2)]$. Universal neighbors are treated separately in that count. Cancel the positive degree and divide by $n-1$.

[Lean proof](../../results/proofs/ea050080fea21230d73430e5338e2f33f90a510667df4aeddc10eb338d12113c.lean#L255) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_algebraic_connectivity_le_0_1_min_degree_laplacian_spectral_radius_0_2a2b3957145e

**Meaning.** The algebraic connectivity is at most the largest Laplacian eigenvalue. Here algebraic connectivity means the second-smallest eigenvalue of $L=D-A$ for a connected graph with at least two vertices, and zero otherwise. The theorem requires no graph hypothesis because it includes those zero cases.

**Proof idea.** For a nonempty graph, zero belongs to the Laplacian spectrum, so the largest Laplacian eigenvalue is nonnegative. If the graph is disconnected or has fewer than two vertices, this covers the defined value zero. Otherwise, the selected second-smallest eigenvalue is a member of the finite Laplacian eigenvalue set. Any member of that set is at most its maximum.

[Lean proof](../../results/proofs/7308fe420f0b4a0f287a06c1ab0681482f2ae262c39d6200ea173d08058f8762.lean#L412) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_max_degree_ge_1_-1_order_complement_spectral_radius_-1_c3ce2e082db9

**Meaning.** The maximum degree satisfies $\Delta\ge n-\rho(\overline G)-1$. Equivalently, the complement must have adjacency radius at least $n-1-\Delta$. The statement applies to every finite simple graph, and the complement has the same vertex set as the original graph.

**Proof idea.** Every complement degree is $n-1-d(v)$, hence is at least $n-1-\Delta$. The spectral theorem shows that $\rho(\overline G)I-A(\overline G)$ is positive semidefinite. Testing it on the all-ones vector bounds the complement degree sum above by $n\rho(\overline G)$. The degree lower bounds give the opposite estimate $n(n-1-\Delta)$. For $n>0$, cancel $n$ and rearrange; the empty case is immediate.

[Lean proof](../../results/proofs/65add79c1eef6a2a1eb0a07e359fb9dc095b7aa2a5490fb9c3122a445a121f02.lean#L267) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_max_degree_le_0_1_diameter_nordhaus_gaddum_spectral_sum_0_is_connected_3b0accd8be72

**Meaning.** For a connected graph, $\Delta\le\rho(G)+\rho(\overline G)$. The two adjacency radii are taken for the graph and its complement on the same vertices. Connectedness supplies a nonempty vertex set in the formal argument, including the one-vertex case.

**Proof idea.** For either graph, an eigenbasis expansion bounds the quadratic form of the all-ones vector by its largest eigenvalue times $n$. Consequently, each degree sum is at most $n$ times its corresponding radius. Adding them and using $d_G(v)+d_{\overline G}(v)=n-1$ gives $n-1\le\rho(G)+\rho(\overline G)$. A simple graph has $\Delta\le n-1$, which completes the comparison.

[Lean proof](../../results/proofs/5eb3b95bd94bfaa694531f838fcb261e9436193f5be97185bc40fa10359b77c6.lean#L237) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_max_degree_le_1_-1_nordhaus_gaddum_spectral_sum_spectral_radius_1_is_tree_1113fa47dd29

**Meaning.** For a tree, the displayed spectral-sum expression simplifies to $\Delta\le\rho(\overline G)+1$. The original graph radius cancels from the right-hand side. The tree assumption is substantive in this proof: it makes every neighborhood an independent set in the original graph.

**Proof idea.** Choose a vertex of degree $\Delta$. Its neighbors form a clique in the complement, since an edge among them would make a triangle in the tree. The matrix $\rho(\overline G)I-A(\overline G)$ is positive semidefinite. Restrict it to these neighbors and test on their all-ones vector. This gives $\Delta[\rho(\overline G)+1-\Delta]\ge0$. If $\Delta>0$, cancel it; degree zero is handled separately.

[Lean proof](../../results/proofs/87efc9fc27a7515bdfccb95a82462700c68bbd6a4e727c9c562f29aca4cdd2e3.lean#L554) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_min_degree_le_0.00892857_0.875_size_spectral_spread_0_is_connected_c66b5dc137e5

**Meaning.** For a connected graph, $\delta\le c m+7s/8$, where $c$ is the indexed coefficient just above $1/112$. Here $s=\rho-\eta$ includes the smallest adjacency eigenvalue. The inequality combines edge count with spectral width to control the minimum degree.

**Proof idea.** The all-ones quadratic form gives $\delta\le\rho$, and the degree sum gives $n\delta\le2m$. Zero adjacency trace, together with every eigenvalue being at least $\eta$, yields $n\delta\le(n-1)s$. A quadratic inequality in $n$, obtained from the nonnegativity of $(2n-29)^2$, combines these bounds into the stronger estimate $\delta\le m/112+7s/8$. Increasing the edge coefficient to its indexed value preserves the result.

[Lean proof](../../results/proofs/cdab9b59af30a3d48219a0b45eae4184654541442e0c35811c9340bc7316d1c0.lean#L41) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_min_degree_le_0.0222222_0.8_size_spectral_spread_0_is_connected_98b1a636aa35

**Meaning.** For a connected graph, $\delta\le c m+4s/5$, with $c$ the indexed coefficient just above $1/45$. The spectral spread $s=\rho-\eta$ measures the separation of the largest and smallest adjacency eigenvalues. The exact coefficient remains available in the linked statement.

**Proof idea.** When $\delta>0$, the all-ones Rayleigh quotient gives $\rho\ge\delta$. A vector equal to one and minus one on the endpoints of an edge has quotient $-1$, so $\eta\le-1$ and $s\ge\delta+1$. Degree counting gives $2m\ge\delta(\delta+1)$. Since $\delta$ is an integer, $(\delta-8)(\delta-9)\ge0$. Combining these inequalities proves the bound with $1/45$, then with the slightly larger indexed coefficient.

[Lean proof](../../results/proofs/41cfe1cf203cd6bf4fa0b0d63195604f84df4fdf42965ec5a06b75a04f53401e.lean#L41) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_min_degree_le_0.0277778_0.8_size_spectral_spread_0_is_connected_f7cbf7fc2dc8

**Meaning.** For a connected graph, $\delta\le c m+4s/5$, where the indexed coefficient $c$ is approximately $0.02778$. Both extreme adjacency eigenvalues enter through $s=\rho-\eta$. This entry has the same spread coefficient as the nearby bound, but its source uses a different trace-based argument.

**Proof idea.** The degree sum gives $n\delta\le2m$, and the all-ones Rayleigh quotient gives $\delta\le\rho$. Since the adjacency eigenvalues sum to zero, the remaining $n-1$ eigenvalues force $n\delta\le(n-1)s$. The nonnegative quadratic $n^2-17n+80$ combines these estimates to establish $\delta\le m/40+4s/5$. The target follows because its indexed edge coefficient exceeds $1/40$; zero minimum degree is handled separately.

[Lean proof](../../results/proofs/25cc944657c5fe5474f1081b70bfcbb81b696117d465e64e0c9c17aa0867f156.lean#L41) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_min_degree_le_0.0357143_0.75_size_spectral_spread_0_is_connected_01b2dc2cdaf3

**Meaning.** For a connected graph, $\delta\le c m+3s/4$, where $c$ is the indexed coefficient just above $1/28$. Thus edge count and the interval from $\eta$ to $\rho$ jointly bound the minimum degree. The empty and zero-degree cases are included in the source argument.

**Proof idea.** An eigenbasis expansion bounds every adjacency quadratic form between $\eta\|x\|^2$ and $\rho\|x\|^2$. Testing the all-ones vector gives $\rho\ge\delta$; testing opposite signs on an edge gives $\eta\le-1$. Also $2m\ge\delta(\delta+1)$. Integer degree implies $(\delta-6)(\delta-7)\ge0$, which combines with $s\ge\delta+1$ to give $\delta\le m/28+3s/4$. The indexed coefficient is slightly larger.

[Lean proof](../../results/proofs/4d37c73225236a20557d5f5b3a1cf2cd91cbfe8c61a2037ace91c507c5248b28.lean#L18) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_min_degree_le_0_0.5_nordhaus_gaddum_spectral_product_nordhaus_gaddum_spectral_sum_0.5_is_bipartite_fe51971bfc87

**Meaning.** For a bipartite graph, $\delta\le[\rho(G)+\rho(\overline G)+1]/2$. The factor one-half multiplies the entire spectral sum, and the remaining constant is also one-half. Bipartiteness means a valid coloring with two colors; the theorem does not require connectedness.

**Proof idea.** Testing adjacency quadratic forms on all-ones vectors gives $n-1\le\rho(G)+\rho(\overline G)$. The two-coloring gives $2\delta\le n$: when minimum degree is positive, choose an edge; its endpoint neighborhoods are disjoint, since a common neighbor would require three different colors. Each neighborhood has at least $\delta$ vertices. Combine these inequalities to obtain $2\delta\le\rho(G)+\rho(\overline G)+1$.

[Lean proof](../../results/proofs/10ec3549115349234312c57640c9029c56bc225743adea3744d95ca227f863e2.lean#L142) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_order_ge_0_0.5_laplacian_spectral_radius_signless_laplacian_spectral_radius_1_is_connected_d400e6f639cf

**Meaning.** For a connected graph, $n\ge q/2+1$, or equivalently $q\le2(n-1)$. Here $q$ is the largest eigenvalue of the signless Laplacian. Connectedness ensures that the formal graph has at least one vertex, so the one-vertex case gives $q=0$.

**Proof idea.** For each signless eigenvalue, take an eigenvector coordinate with largest absolute value. Its row equation has a degree term and a neighbor sum, each bounded by $d(v)|x_v|$. This gives $|\lambda|\le2d(v)$. Because the graph is simple, $d(v)\le n-1$, so every signless eigenvalue is at most $2(n-1)$. Taking the maximum and rearranging proves the displayed order bound.

[Lean proof](../../results/proofs/ad04c862036808dc0007cfcc9ac7846d7b226c7f9d83dae0f5d3d90b85ea8bec.lean#L169) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_order_ge_1_0_laplacian_spectral_radius_signless_laplacian_spectral_radius_0_is_connected_88f94a53c8e1

**Meaning.** For a connected graph, the largest Laplacian eigenvalue $\mu_{\max}$ is at most $n$. The Laplacian is $L=D-A$, and this radius differs from both the adjacency radius and the signless Laplacian radius. The connected hypothesis is retained in the theorem statement.

**Proof idea.** For a unit Laplacian eigenvector $x$, the eigenvalue equals the sum of $(x_v-x_w)^2$ over edges. Enlarge this sum to all unordered vertex pairs, since each added square is nonnegative. The corresponding sum over ordered pairs is $2[n\sum_v x_v^2-(\sum_v x_v)^2]$. Unit norm makes this at most $2n$. Dividing the ordered-pair expression by two bounds the eigenvalue by $n$.

[Lean proof](../../results/proofs/bc23b5b5216f474b5211cded652ebdff067556da9a1ee81dc75949735aebb1ac.lean#L169) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_order_ge_1_0_spectral_spread_triangle_count_0_is_regular_282e36142d1e

**Meaning.** For a regular graph, its adjacency spectral spread satisfies $s\le n$. Regularity means that some integer $d$ is the degree of every vertex. For $n>0$, its complement is then regular of degree $n-1-d$; the empty graph has spread zero. The smallest adjacency eigenvalue is included in $s=\rho-\eta$.

**Proof idea.** After handling the empty graph, positive semidefiniteness of $dI-A=L$ bounds every adjacency eigenvalue above by $d$. Applying the same argument to the complement bounds its radius by $n-1-d$. The proved complement comparison gives $s\le\rho(G)+\rho(\overline G)+1$: it follows from $A+A(\overline G)=J-I$ and positivity of $J$. Insert the two regular degree bounds; their sum plus one is exactly $n$.

[Lean proof](../../results/proofs/1b6e4acaa0451269f8a2238564ea16102602e78ddafd413462f511fb0a177ac6.lean#L233) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_signless_laplacian_spectral_radius_ge_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_26c733c31f3e

**Meaning.** For a regular graph, $q\ge2\Delta$. For $n>0$, if every vertex has degree $d$, then $\Delta=d$, so the statement is a lower bound $q\ge2d$. For the empty graph, $q=\Delta=0$. The regularity assumption is essential to this spectral identity; a separate upper bound $q\le2\Delta$ holds for all graphs.

**Proof idea.** The constant vector is an adjacency eigenvector with eigenvalue $d$, as encoded by the regular-graph spectrum lemma. Since the degree matrix is $dI$, adding it shifts that adjacency eigenvalue to $2d$ in $Q=dI+A$. Therefore $2d$ belongs to the signless spectrum and cannot exceed its largest eigenvalue. The empty graph is handled directly before using the regular degree identity.

[Lean proof](../../results/proofs/33ccefcf78c99e5dc68b41c43d41e1e6e94a7095786fae1b15e7de786d3e1504.lean#L170) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_signless_laplacian_spectral_radius_le_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_fd3eb1d598b5

**Meaning.** For a regular graph, $q\le2\Delta$. For $n>0$, writing the common degree as $d$ makes the bound $q\le2d$. Together with the separate regular lower bound, this identifies $q=2\Delta$, including the empty graph where both sides are zero. The upper inequality itself also has a general-graph version elsewhere in this collection.

**Proof idea.** The empty graph is handled first. Otherwise use a unit eigenvector $x$ of $Q=D+A$. Regularity makes its degree quadratic form exactly $x^{\mathsf T}Dx=d$. Positive semidefiniteness of $L=D-A$ gives $x^{\mathsf T}Ax\le d$. Consequently, its signless eigenvalue is $x^{\mathsf T}Qx=d+x^{\mathsf T}Ax\le2d$. The proof applies this comparison to every signless eigenvalue, then takes the maximum and replaces $d$ by $\Delta$.

[Lean proof](../../results/proofs/812ec8d1bdd989fe07dda276c370aefd74ffd7ece004a13f2885981c3e5224f2.lean#L161) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_signless_laplacian_spectral_radius_le_1_0_laplacian_spectral_radius_order_0_is_tree_2b08091466a0

**Meaning.** For a tree, $q\le\mu_{\max}$: the largest signless Laplacian eigenvalue is no greater than the largest Laplacian eigenvalue. The proof actually identifies the two spectra. Its use of the tree hypothesis is to obtain a valid two-coloring.

**Proof idea.** Assign diagonal signs $+1$ and $-1$ according to that coloring, forming a matrix $S$ with $S^2=I$. Adjacent vertices have opposite signs, so conjugating $L=D-A$ by $S$ changes the adjacency signs and gives $SLS=D+A=Q$. This conjugation preserves the characteristic polynomial. The symmetric-matrix eigenvalue lists therefore agree, and their largest values agree as well, proving the requested inequality.

[Lean proof](../../results/proofs/f3b6079e957207a5556df0224917fbc0442aa8acd13899895628f5b7d5b7222f.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_ge_0.5_0_spectral_spread_independence_number_0_is_regular_37cf8d66157a

**Meaning.** For a regular graph, $m\ge s/2$. Equivalently, the adjacency spectral spread is at most twice the number of edges. The indexed statement assumes regularity, while this particular source argument bounds adjacency eigenvalues using degrees without needing the constant-degree property.

**Proof idea.** For an arbitrary adjacency eigenvalue, choose an eigenvector coordinate with greatest absolute magnitude. The eigenvalue equation and the triangle inequality give $|\lambda|\le d(v)$ at that vertex. Its degree is at most $m$, because all incident edges belong to the graph edge set. Thus the largest adjacency eigenvalue is at most $m$, and the smallest is at least $-m$. Subtract these endpoint bounds.

[Lean proof](../../results/proofs/3a5a9e24a76f2032e5cd608cd9cc37a67a78b411a81dd28396d98c10c354ff23.lean#L298) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_ge_0_1_nordhaus_gaddum_spectral_product_spectral_radius_0_is_bipartite_fd5d8dffd858

**Meaning.** For a bipartite graph, $m\ge\rho$. This lower bound on edge count compares it with the largest adjacency eigenvalue. The theorem states a two-colorability assumption; the proof uses only general adjacency and degree facts, so no connectedness is needed.

**Proof idea.** Bound each eigenvalue by choosing a nonzero eigenvector coordinate of maximal absolute value. At that vertex, $\lambda x_v$ equals the sum of neighboring coordinates. Their absolute values are each at most $|x_v|$, so $|\lambda|\le d(v)$. The incidence edge set has size $d(v)$ and lies in the full edge set, giving $d(v)\le m$. Hence every eigenvalue, and therefore their largest value, is at most $m$.

[Lean proof](../../results/proofs/e59dfee9dbbc5ab6704845d98a9f9f388b1664c98a2525f45ba6b7b5bdf63ba7.lean#L576) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_ge_0_5.5_nordhaus_gaddum_spectral_product_spectral_radius_-7.6_is_bipartite_c239cbde8507

**Meaning.** For a bipartite graph, $m\ge(11/2)\rho-38/5$. This is a linear consequence of a squared spectral estimate specific to the two-color structure. It applies even when the graph is disconnected, with the empty graph treated separately.

**Proof idea.** A bipartition shows that the sum of degrees over either side is $m$, so the degree sum over any vertex neighborhood is at most $m$. At a maximal absolute eigenvector coordinate, apply the adjacency eigenvalue equation twice. The resulting sum over walks of length two gives $\lambda^2\le m$. Completing the square at $\lambda=11/4$ yields $m\ge(11/2)\lambda-38/5$. Apply this bound to the largest eigenvalue.

[Lean proof](../../results/proofs/0ff78db875ca775c80dc745b7d2ec8f39c505942d96fb545917f602c9cd7d190.lean#L576) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_ge_1_0_signless_laplacian_spectral_radius_clique_number_-1_is_connected_e56f65d5cb44

**Meaning.** For a connected graph, $m\ge q-1$, equivalently $q\le m+1$. The largest signless Laplacian eigenvalue is therefore controlled by edge count with an additive constant. The formal statement retains the connected hypothesis.

**Proof idea.** For adjacent vertices, their incidence edge sets intersect only in their shared edge, so $d(v)+d(w)\le m+1$. For a positive signless eigenvalue, choose an edge maximizing $|x_v+x_w|$; some such sum is nonzero by the eigenvalue equation. Add the equations at its endpoints, and bound every edge-coordinate sum by the chosen maximum. Cancellation gives $\lambda\le d(v)+d(w)\le m+1$. Nonpositive eigenvalues satisfy the bound immediately.

[Lean proof](../../results/proofs/f377350db1eed79ada8f92d4c7284d771ec540fc45c400bbcd8859cb3b389474.lean#L23) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_ge_6.16667_0_spectral_radius_normalized_laplacian_spectral_gap_-9.51_is_bipartite_d0601a9aa5b8

**Meaning.** For a bipartite graph, $m\ge c\rho-9.51$, where $c$ is the exact indexed coefficient approximately $6.1667$. This compares edge count with adjacency radius through a linear expression. The two-colorability assumption, rather than connectedness, is what provides the spectral estimate used here.

**Proof idea.** Choose the largest adjacency eigenvalue and a maximal absolute coordinate of its eigenvector. Applying its eigenvalue equation twice bounds its square by the sum of neighbor degrees. In a bipartite graph, those neighbors lie on one side, whose degree sum is $m$, so $\rho^2\le m$. Completing the square gives $\rho^2\ge c\rho-c^2/4$, and the indexed numbers satisfy $c^2/4\le9.51$.

[Lean proof](../../results/proofs/6048d4f7d1e85e89a20978978361724e3d40f6b920b4cfab1855861bc95a2249.lean#L576) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_size_le_1_1_nordhaus_gaddum_spectral_product_spectral_radius_0_is_bipartite_26b594df331a

**Meaning.** For a bipartite graph, $m\le\rho(G)[\rho(\overline G)+1]$. Thus the graph and complement radii jointly give an upper bound on the edge count. A two-coloring partitions the entire vertex set, including isolated vertices, into independent color classes.

**Proof idea.** The all-ones adjacency quadratic form gives $2m\le n\rho(G)$. Each color class is a clique in the complement. Testing its indicator vector in the complement bounds its size $a$ through $a(a-1)\le a\rho(\overline G)$. Add the two class bounds and use their squared size difference to obtain $n\le2[\rho(\overline G)+1]$. Multiply this by the nonnegative $\rho(G)$ and combine with the edge estimate.

[Lean proof](../../results/proofs/0f0ef81236fe1d8f8d3d9f1f7053da74787cf1e066715f9cb48da4dcca79d92b.lean#L410) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull3d_spectral_radius_le_0.5_0_signless_laplacian_spectral_radius_clique_number_0_is_connected_616dd0147311

**Meaning.** For a connected graph, $\rho\le q/2$. Here $\rho$ is the largest adjacency eigenvalue and $q$ is the largest eigenvalue of the signless Laplacian. The statement gives a lower bound $q\ge2\rho$ while retaining connectedness as its formal hypothesis.

**Proof idea.** The spectral theorem gives the quadratic-form bound $x^{\mathsf T}Qx\le q\|x\|^2$. Positive semidefiniteness of $L=D-A$ gives $x^{\mathsf T}Dx\ge x^{\mathsf T}Ax$, hence $x^{\mathsf T}Qx\ge2x^{\mathsf T}Ax$. Apply both comparisons to a unit adjacency eigenvector. Its adjacency quadratic form is its eigenvalue, so each adjacency eigenvalue is at most $q/2$. Taking their maximum proves the result.

[Lean proof](../../results/proofs/c04fec88afb8b5d3f4f62a67ced025f1a9ab2c37ed18ab4e902b48be3cbece50.lean#L302) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7

**Meaning.** The average degree obeys $\bar d\le\rho$ for every finite simple graph. For $n>0$, this means $2m/n$ is no greater than the largest adjacency eigenvalue. It relates a direct degree average to a spectral quantity without assumptions on connectedness or regularity.

**Proof idea.** Expand any vector in an orthonormal adjacency eigenbasis. Its quadratic form is a sum of eigenvalues weighted by squared coefficients, so it is at most $\rho$ times its squared norm. For the all-ones vector, the squared norm is $n$, and the adjacency quadratic form is the degree sum $2m$. Divide $2m\le n\rho$ by positive $n$; the empty case uses zeros.

[Lean proof](../../results/proofs/3b28d209599323ceed58241f53c798e2ed2985b75823888e47a29f6f3e4f7263.lean#L426) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_density_le_0_spectral_radius_1_b85814518e6b

**Meaning.** The edge density $p$ is at most one. Here $p=2m/[n(n-1)]$ for $n\ge2$, and $p=0$ for smaller graphs. This density is distinct from the adjacency spectral radius $\rho$; the coefficient of the spectral quantity on the right-hand side of the indexed statement is zero.

**Proof idea.** For $n<2$, the definition gives zero immediately. Otherwise, the denominator is positive. Each vertex has degree at most $n-1$, so the degree sum is at most $n(n-1)$. The handshake identity identifies that sum with $2m$. Divide the resulting inequality by the positive denominator to obtain $p\le1$. No eigenvalue comparison is needed after the zero coefficient is simplified.

[Lean proof](../../results/proofs/d55822738a8ecd07fe5da5f171107ec8ac7827deb6f99c06d054c031d23d4e1b.lean#L97) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_laplacian_spectral_radius_le_1_signless_laplacian_spectral_radius_0_e1c0af0e1150

**Meaning.** The largest Laplacian eigenvalue satisfies $\mu_{\max}\le q$ for every finite simple graph. The two matrices are $L=D-A$ and $Q=D+A$. The comparison requires no bipartiteness; for trees, a separate argument proves that their spectra are equal.

**Proof idea.** Take a unit Laplacian eigenvector $x$ and replace every coordinate by its absolute value, producing $y$. This preserves norm and the diagonal degree quadratic form. Along each edge, $-x_vx_w\le|x_v||x_w|$, so $x^{\mathsf T}Lx\le y^{\mathsf T}Qy$. The spectral theorem bounds the latter by $q\|y\|^2=q$. Each Laplacian eigenvalue is therefore at most $q$, and the same holds for their largest value.

[Lean proof](../../results/proofs/51d8b21751aceb94f082c4deee63677a6b885ed0bb832421932c32eea46dd629.lean#L24) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_laplacian_spectral_radius_le_2_max_degree_0_3b14564974f2

**Meaning.** The largest Laplacian eigenvalue obeys $\mu_{\max}\le2\Delta$ for every finite simple graph. This upper bound uses the maximum vertex degree and places no connectedness or regularity assumption on the graph. The empty graph has zero Laplacian radius by definition.

**Proof idea.** Choose a nonzero eigenvector coordinate of maximal absolute magnitude for each Laplacian eigenvalue. The row equation is $\lambda x_v=d(v)x_v-\sum_{w\sim v}x_w$. The triangle inequality bounds its absolute right-hand side by $2d(v)|x_v|$. Since $|x_v|>0$, cancel it to obtain $|\lambda|\le2d(v)\le2\Delta$. The inequality holds for every eigenvalue and hence for the maximum.

[Lean proof](../../results/proofs/d34720d3e33a9f0a92ba33d28cfadc3d44561f73583832112a17e08ca18e93ab.lean#L282) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_normalized_laplacian_spectral_radius_le_0_complement_spectral_radius_2_b7beb0d09a33

**Meaning.** The largest normalized Laplacian eigenvalue $\nu_{\max}$ is at most two. The normalization uses inverse square roots of degrees, assigning zero weight to isolated vertices. The complement radius appearing with coefficient zero in the indexed expression has no effect on the bound.

**Proof idea.** For any vector $y$, sum $(y_v-y_w)^2\le2y_v^2+2y_w^2$ over edges to get $y^{\mathsf T}Ly\le2\sum_v d(v)y_v^2$. For a unit eigenvector $x$ of the normalized matrix, set $y=Rx$. At a positive-degree vertex, $d(v)y_v^2=x_v^2$; isolated vertices contribute zero. The weighted sum is therefore at most one. Its normalized eigenvalue is $y^{\mathsf T}Ly\le2$.

[Lean proof](../../results/proofs/b6703921d114648a2e09f85e63aa8ca69c3a63cbaefb62282eb0a22bf69b65c4.lean#L10) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_normalized_laplacian_spectral_radius_le_1_signless_laplacian_spectral_radius_0_b12e09e7aec2

**Meaning.** The largest normalized Laplacian eigenvalue satisfies $\nu_{\max}\le q$, the signless Laplacian radius. This comparison is valid for every finite simple graph, with the normalization setting isolated-vertex inverse degree weights to zero. The edgeless graph is a separate zero case.

**Proof idea.** The proved normalized bound gives $\nu_{\max}\le2$. If an edge exists, test $Q$ on the vector equal to one at its two endpoints and zero elsewhere. Its squared norm is two, and its quadratic form is $d(v)+d(w)+2\ge4$, so the spectral quadratic-form bound gives $q\ge2$. Thus $\nu_{\max}\le2\le q$. With no edges, both matrices are zero and both radii are zero.

[Lean proof](../../results/proofs/492f5e9582680d06ccca92d3b271ed94d6b2bc3a6361d1d1ba93c7443052b1f6.lean#L314) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_normalized_laplacian_spectral_radius_le_1_spectral_spread_0_fd06095fa69d

**Meaning.** The largest normalized Laplacian eigenvalue satisfies $\nu_{\max}\le s$, the adjacency spectral spread. The smallest adjacency eigenvalue $\eta$ matters here because $s=\rho-\eta$. The theorem holds for all finite simple graphs, including the edgeless and empty cases.

**Proof idea.** The normalized bound gives $\nu_{\max}\le2$. If there is an edge, the vectors supported on its endpoints with signs $(1,1)$ and $(1,-1)$ have adjacency Rayleigh quotients $1$ and $-1$. Using the spectral quadratic-form bounds yields $\rho\ge1$ and $\eta\le-1$, so $s\ge2$. Combine these inequalities. If the graph is edgeless, the adjacency and normalized Laplacian matrices both vanish, giving the required zero comparison.

[Lean proof](../../results/proofs/2ad14104e79832bef1b7ee77b7d723daa1c11e9162accdc663a9a42984caa43f.lean#L596) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_order_le_1_nordhaus_gaddum_spectral_sum_1_914963b7a9e6

**Meaning.** The order satisfies $n\le\rho(G)+\rho(\overline G)+1$. Equivalently, the graph and complement adjacency radii have sum at least $n-1$. Both graphs use the same vertex set. This statement has no connectedness or regularity assumption.

**Proof idea.** For either adjacency matrix, the spectral theorem makes its largest eigenvalue times $I$ minus the matrix positive semidefinite. Add these two matrices and use $A(G)+A(\overline G)+I=J$. The result is $[\rho(G)+\rho(\overline G)+1]I-J$. Test it on the all-ones vector, for which $J$ acts by multiplication by $n$. Nonnegativity gives $n[\rho(G)+\rho(\overline G)+1-n]\ge0$; cancel positive $n$, treating the empty graph separately.

[Lean proof](../../results/proofs/5dd3e110f4a32c9c97bf4394b9b4aea011db7cbd5d64e050cfa0cafb3a381841.lean#L161) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_signless_laplacian_spectral_radius_le_1_size_1_9b51f8e6875e

**Meaning.** The signless Laplacian radius satisfies $q\le m+1$ for every finite simple graph. This upper bound differs from the nearby connected edge-count form only in the stated hypotheses and rearrangement. Here connectedness is not required.

**Proof idea.** For an edge $vw$, the two incidence sets overlap in exactly that edge, so $d(v)+d(w)\le m+1$. Summing these inequalities over the neighbors of $v$ gives $d(v)^2+\sum_{w\sim v}d(w)\le(m+1)d(v)$. For a positive signless eigenvalue, maximize $|x_v|/d(v)$; isolated coordinates vanish. Its row equation bounds $\lambda d(v)$ by the left-hand side. Cancel the positive degree. Nonpositive eigenvalues already satisfy the bound.

[Lean proof](../../results/proofs/32c8fa66984e5fbe7c4b63ad8b3debffc04ada11fdc3d6673bae8dd28cb0d442.lean#L24) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_signless_laplacian_spectral_radius_le_2_size_0_ffad05ac8dd4

**Meaning.** The signless Laplacian radius obeys $q\le2m$. Thus twice the edge count is a universal upper bound on the largest eigenvalue of $Q=D+A$. No connectedness or regularity is required, and the bound is zero for an edgeless graph.

**Proof idea.** The parent signless degree theorem gives $q\le2\Delta$ by using a maximal absolute eigenvector coordinate in the row equation. Separately, every degree is at most $m$, since the incident edges at a vertex form a subset of all edges. Taking the maximum degree gives $\Delta\le m$. Multiply this inequality by two and use transitivity to obtain $q\le2\Delta\le2m$.

[Lean proof](../../results/proofs/bccaef6f91b50d2b7691d61b68fca2f621048be149cd4951e76a1f80557a3b91.lean#L84) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_radius_le_0.25_size_1.5_fafb16939177

**Meaning.** The adjacency radius satisfies $\rho\le m/4+3/2$ for every finite simple graph. This is a linear bound in the edge count. Its proof treats small edge counts and certain small vertex degrees separately, rather than relying on a single uniform estimate.

**Proof idea.** For $m\le4$, use $\rho\le(m+1)/2$. Otherwise, at a maximal absolute eigenvector coordinate, the row equation gives $\lambda\le d(v)$ and its two-step version gives $\lambda^2\le2m-d(v)$. For $d(v)\ge4$, a completed square in $m$ proves the target. Degrees at most three are immediate when $m\ge6$; at $m=5$, split degrees at two and use the squared estimate for degree three.

[Lean proof](../../results/proofs/b8ea172b892f0c689ca3eea6fbb994c51c84f0057e4f63109e66551801179daf.lean#L135) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_radius_le_0.5_size_0.5_bf1d5973d871

**Meaning.** The adjacency radius satisfies $\rho\le(m+1)/2$ for every finite simple graph. The statement controls the largest adjacency eigenvalue using only edge count and an additive constant. Neither connectedness nor a bipartite structure is assumed.

**Proof idea.** For each edge $vw$, incidence counting gives $d(v)+d(w)\le m+1$. Hence the degree sum over the neighbors of $v$ is at most $d(v)[m+1-d(v)]$. For any adjacency eigenvalue, apply its eigenvector equation twice at a coordinate of maximal absolute magnitude. Cancellation gives $\lambda^2\le d(v)[m+1-d(v)]\le[(m+1)/2]^2$, where the last step completes the square in $d(v)$. Taking the nonnegative square root bounds every eigenvalue and therefore $\rho$.

[Lean proof](../../results/proofs/9d4be82856c1860fe513069ffee747bff5c0dd1c90866c1336df9eb0547d093a.lean#L410) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)
