# Energy and Estrada index

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

These are informal explanations of the linked Lean statements and proofs.

For a finite simple graph, let $n$ be its number of vertices, $m$ its number of edges, and $A$ its real adjacency matrix. Its real eigenvalues, counted with multiplicity, are $\lambda_i$. The graph energy is $E=\sum_i|\lambda_i|$ and the Estrada index is $EE=\sum_i e^{\lambda_i}$. Write $\rho=\max_i\lambda_i$, $\ell=\min_i\lambda_i$, and $s=\rho-\ell$ for the spectral spread; the code sets both extrema to zero when $n=0$. Write $\rho_c$ for the corresponding largest eigenvalue of the complement graph. The maximum and minimum degrees are $\Delta$ and $\delta$, and $\bar d=2m/n$, with $\bar d=0$ for the empty graph.

The normalized Laplacian is $DLD$, where $L$ is the ordinary Laplacian and $D$ has diagonal entries $1/\sqrt{\deg(v)}$, with the inverse of zero interpreted as zero. The code's normalized gap $\eta$ is its second-smallest eigenvalue for a connected graph with $n\ge2$, and zero otherwise. A regular graph has a common integer degree $d$, equal to $\bar d$ when nonempty. For the repeated exponential comparisons below, set $a=\sqrt{\bar d}$ and $C=\frac n2(e^a+e^{-a})$.

## composed_1f7e49d87d42f727

**Meaning.** The energy is at most the number of vertices times the maximum degree: $E\le n\Delta$. This applies to every finite simple graph, including an empty graph or one with isolated vertices. It gives an upper bound on the total absolute size of the adjacency eigenvalues using only the vertex count and the largest local degree.

**Proof idea.** The proof chains two established inequalities. The energy–edge bound gives $E\le2m$. The degree-sum bound gives $2m\le n\Delta$, because the sum of all degrees is $2m$ and each vertex degree is at most $\Delta$. Transitivity supplies the stated result.

[Lean proof](../../results/proofs/51fdcfb08400b6850b861e8a8f7556c4c2cb7a45422ead4b9e64003423d9f8e7.lean#L85) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## composed_35ca49dcc0267544

**Meaning.** Twice the largest adjacency eigenvalue is at most the Estrada index: $2\rho\le EE$. There is no regularity or connectivity premise. With the source’s empty-graph convention, both the eigenvalue term and the empty Estrada sum are zero, so that case is included as well.

**Proof idea.** The proof uses the energy as an intermediate quantity. The spectral-radius energy bound says $2\rho\le E$, using the zero sum of adjacency eigenvalues. The Estrada–energy comparison says $E\le EE$, obtained by summing $|x|+x\le e^x$. Joining these two parent inequalities proves the conclusion.

[Lean proof](../../results/proofs/3f702c15148dd5c57b52e6d8a5b420bbdd31a8c98f5ba118200cc0bf0aa39869.lean#L57) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## composed_845382c1cbed672e

**Meaning.** The difference between the largest and smallest adjacency eigenvalues is bounded by the Estrada index: $s\le EE$. This is a comparison between the width of the adjacency spectrum and its exponential sum. No connectedness, regularity, or nonempty-vertex assumption is imposed; the empty graph has spread zero by definition.

**Proof idea.** The first parent bounds the spread by $2\rho$. It proves every eigenvalue is at least $-\rho$ by comparing an eigenvector with its coordinatewise absolute value in the adjacency quadratic form. The second parent, $2\rho\le EE$, follows through energy. Their composition gives the desired spread bound.

[Lean proof](../../results/proofs/5670c4e679adb5f8daf3584dcfabba53fd2188d220113a3f142384ecde51ef7f.lean#L159) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## composed_e72ee9accef18103

**Meaning.** The graph energy is at least the adjacency spectral spread: $s\le E$. In other words, the sum of the absolute values of all eigenvalues is large enough to cover the distance between the two spectral extremes. The statement holds for every finite simple graph, with spread and energy both zero on the empty graph.

**Proof idea.** The proof composes the spread estimate $s\le2\rho$ with the energy estimate $2\rho\le E$. The first uses nonnegative adjacency entries to control negative eigenvalues by the largest one. The second uses the zero trace: summing the nonnegative quantities $|\lambda_i|+\lambda_i$ gives exactly $E$.

[Lean proof](../../results/proofs/92db60324563ce832c038361736c2b250e2f0fcbf8a63b6ea68964ca98428054.lean#L134) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## estrada_ge_energy

**Meaning.** For every finite simple graph, the Estrada index dominates graph energy: $EE\ge E$. This compares two different summaries of the same adjacency spectrum, one using exponentials and the other absolute values. It includes disconnected graphs, isolated vertices, and the empty graph without an additional premise.

**Proof idea.** The proof first establishes $|x|+x\le e^x$ for every real $x$. For nonnegative $x$, the quadratic exponential lower bound and $(x-1)^2\ge0$ suffice; for negative $x$, the left side is zero. Summing over eigenvalues leaves $E+\sum_i\lambda_i$. The adjacency trace is zero, so the linear sum disappears.

[Lean proof](../../results/proofs/d7f613f116fd40183412a09c15bcbafc255307fafd3063047bd087e5b3cdb595.lean#L57) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## estrada_index_quadratic_lower_bound

**Meaning.** The Estrada index is at least the vertex count plus half the square of the largest adjacency eigenvalue: $EE\ge n+\rho^2/2$. The result needs no connectivity or regularity assumption. It strengthens the baseline $EE\ge n$ by keeping a contribution from the largest eigenvalue.

**Proof idea.** For a nonempty graph, the proof chooses an eigenvalue attaining the maximum and shows it is nonnegative using the zero eigenvalue sum. Every remainder $e^x-1-x$ is nonnegative. Its sum is therefore at least the selected remainder, which is at least $\rho^2/2$ by the quadratic exponential bound. Zero trace turns the total remainder into $EE-n$; the empty case is immediate.

[Lean proof](../../results/proofs/dbf2454f07dd8a53777690ca03b3badc71d80274467b1c08a3b72f77748c167a.lean#L50) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## graph_energy_spectral_radius_lower

**Meaning.** The energy is at least twice the largest adjacency eigenvalue: $E\ge2\rho$. The source defines $\rho=0$ when the vertex set is empty, so no nonempty-graph premise is needed. The factor two reflects the balancing of positive and negative eigenvalues forced by the zero adjacency trace.

**Proof idea.** In the nonempty case, the largest eigenvalue is attained. Each term $|\lambda_i|+\lambda_i$ is nonnegative, so their sum dominates the term at that maximum. Their total is $E$, since the eigenvalues sum to zero. Finally, $|\rho|\ge\rho$ makes the selected term at least $2\rho$. The empty case simplifies to zero.

[Lean proof](../../results/proofs/f3a825484b21395e4acb3b20fea78f1effa9cdcd688f8bf0f33c50fd3b60e9b9.lean#L112) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## gutman_energy_avg_deg_lower

**Meaning.** Every finite simple graph satisfies $E\ge2\bar d$. Thus the average vertex degree gives a lower bound on half the graph energy, even when the graph is irregular or disconnected. The average degree is explicitly zero for an empty vertex set, where nonnegativity of energy handles the statement.

**Proof idea.** The all-ones vector has squared norm $n$ and adjacency quadratic form $2m$. Expanding it in an orthonormal eigenbasis shows that quadratic form is at most $\rho n$, hence $\bar d\le\rho$ for $n>0$. The parent bound $2\rho\le E$ then yields $2\bar d\le E$. The proof checks the positive denominator before dividing.

[Lean proof](../../results/proofs/9c7df49b86dfb00918dc73114a6622bf329bb06a1891323d889d536fc9b5516a.lean#L84) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## gutman_energy_size_bound

**Meaning.** The energy is bounded above by twice the edge count: $E\le2m$. This bound applies to all finite simple graphs without a degree or connectivity condition. It measures how much total absolute spectral size can be contributed by the graph’s edges.

**Proof idea.** For each normalized eigenvector, its eigenvalue is a sum of products of coordinates over ordered adjacent pairs. Taking absolute values and using $|uv|\le(u^2+v^2)/2$ bounds that eigenvalue. The proof sums over the orthonormal eigenbasis; the squared coordinates at every fixed vertex sum to one. Each ordered adjacent pair then contributes one, and their count is the degree sum $2m$.

[Lean proof](../../results/proofs/5b8704e696ef6c268b5a5cef4c0d2d1f987f6de487466c2c22f28cf737049c97.lean#L55) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_average_degree_le_0.5_0_graph_energy_diameter_0_is_regular_634736df2435

**Meaning.** For a regular finite simple graph, the average degree is at most half the energy: $\bar d\le E/2$. The statement retains regularity as an explicit premise and allows an empty graph. On a nonempty regular graph, it says that the common degree is at most half the total absolute adjacency spectrum.

**Proof idea.** The proof brings in three parent bounds: $\delta\le E/2$ for regular graphs, $E\ge2\bar d$ for regular graphs, and $EE\ge E$ for all graphs. The average-degree parent already gives the desired conclusion after dividing by two. The remaining parent inequalities and basic nonnegativity facts are supplied to the same algebraic conclusion.

[Lean proof](../../results/proofs/b6ca253b19db2f4019d85ac9568ee77905cfdba3bbaa7ec28222576e9b77c283.lean#L104) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_estrada_index_ge_1_0.5_order_normalized_laplacian_spectral_gap_0_2c41656b4d7c

**Meaning.** The Estrada index satisfies $EE\ge n+\eta/2$, where $\eta$ is the source’s normalized Laplacian gap. The definition sets that gap to zero when the graph is disconnected or has fewer than two vertices, so the theorem has no extra premise. In those cases it reduces to $EE\ge n$.

**Proof idea.** The parent estimate is $EE\ge n+m+\Delta^2/12$. For a connected graph with at least two vertices, every degree is positive, so the normalized Laplacian has diagonal entries one and trace $n$. Its eigenvalues are nonnegative, hence $\eta\le n$. The degree sum also gives $n\le2m$. Therefore $\eta/2\le m$, and the parent bound proves the result.

[Lean proof](../../results/proofs/1ceadb0a6164355e8727744b0c0bc236e3a781d5bd0e00b5f8d755b203ad557c.lean#L194) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_graph_energy_ge_2_0_average_degree_size_0_is_regular_479d55ae89c3

**Meaning.** A regular graph has energy at least twice its average degree: $E\ge2\bar d$. This indexed theorem includes regularity even though a separate theorem establishes the same inequality for arbitrary graphs. The empty graph is handled with average degree zero; on a nonempty graph the common degree is the relevant quantity.

**Proof idea.** Writing the common degree as $d$, the handshake identity gives $nd=2m$, so $\bar d=d$. The parent regular minimum-degree estimate says $\delta\le E/2$. Since every degree equals $d$, the minimum degree also equals $d$. Replacing both degree quantities by $d$ and rearranging gives $E\ge2\bar d$.

[Lean proof](../../results/proofs/592f26bc3ceb53069813b28bbc3f3d496e1cf70372266e671c2fa14e866c6304.lean#L77) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_graph_energy_le_-2_2_average_degree_size_2_is_regular_96b3eade117f

**Meaning.** For a regular graph, $E\le2m-2\bar d+2$. Relative to the energy–edge bound, this subtracts a degree-dependent term and adds a fixed allowance. The premise is regularity alone; disconnected and empty regular graphs remain included.

**Proof idea.** The main parent gives $E\le2\bar d+\rho\rho_c$. For a nonempty $d$-regular graph, the proof bounds the two largest eigenvalues by $d$ and $n-1-d$, using a largest eigenvector coordinate. It substitutes $\bar d=d$ and $nd=2m$. The integer-degree fact $(d-1)(d-2)\ge0$ then converts that parent bound to the stated one. The empty case uses $E\le2m$ directly.

[Lean proof](../../results/proofs/e84b18d3c884e2adb0c21e200e75d913b45065ef463e4b0402298e1ca04e8865.lean#L429) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_graph_energy_le_0_2_average_degree_size_0_is_regular_99710b2e7422

**Meaning.** For a regular finite simple graph, energy is at most twice the edge count: $E\le2m$. Regularity is an explicit premise of this indexed version. It includes regular graphs with zero degree and an empty vertex set, and its conclusion has the same form as the general energy–edge bound.

**Proof idea.** The proof uses regularity directly. In each eigenvector, choose a coordinate of maximal absolute value. The eigenvalue equation at that vertex is a sum of exactly $d$ neighboring coordinates, so the triangle inequality gives $|\lambda_i|\le d$. Summing over all eigenvalues yields $E\le nd$. The sum-of-degrees identity turns $nd$ into $2m$.

[Lean proof](../../results/proofs/fd122dfe67c7c18fa7ff7003185ef4f585ed0f7e333d3afe0928d14dedab24a6.lean#L83) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_graph_energy_le_2_1_average_degree_nordhaus_gaddum_spectral_product_0_is_regular_7a6a403379a0

**Meaning.** For a regular graph, energy is at most $2\bar d+\rho\rho_c$. The second term couples the largest adjacency eigenvalue of the graph with that of its complement. The statement includes empty graphs, and otherwise the common degree $d$ equals $\bar d$.

**Proof idea.** The proof singles out the regular eigenvalue $d$ and uses $\sum\lambda_i^2=nd$ for the remainder. Summing $2|x|\le x^2+1$, with $1\le d\le n-1$ when $d>0$, gives $E\le d(n+1-d)$. The complement is regular of degree $n-1-d$, and each common degree is an eigenvalue. Thus $\rho\rho_c\ge d(n-1-d)$, completing the comparison; degree zero uses the regular parent $E\le2m$.

[Lean proof](../../results/proofs/ad79c4c6be53bfa4f401da2c854bae70aeded5813c0c72c4906edefa84ee668c.lean#L172) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_-0.5_1_graph_energy_size_1_is_regular_27c4eb6febfd

**Meaning.** For a regular graph, the maximum degree is bounded by $m-E/2+1$. Equivalently, $E\le2m-2\Delta+2$. Since the maximum degree of a nonempty regular graph is its common degree, this is a degree-sensitive refinement of an edge-count upper bound on energy.

**Proof idea.** The proof separates the eigenvalue equal to the common degree $d$, and uses $\sum\lambda_i^2=nd$. For the other eigenvalues, $2|x|\le x^2+1$ bounds their total energy. The handshake identity replaces $nd$ by $2m$. Integer cases $d=0$, $d=1$, and $d\ge2$, together with $n\ge d+1$, supply the polynomial inequality needed to rearrange the bound; the empty case is checked separately.

[Lean proof](../../results/proofs/4756d8590bcc8712122cfeda05478a8cf118a9c355fc4181bf5d1e634f88c185.lean#L116) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.125_1.125_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_ef5c51f5edcb

**Meaning.** For a tree, the maximum degree is bounded by the stated weighted sum of $\rho\rho_c$ and $E$, with weights $1/8$ and $9/8$. The tree premise ensures a nonempty connected graph and the edge relation $m=n-1$. The bound combines local branching with spectra of both the graph and its complement.

**Proof idea.** The proof establishes the Rayleigh bound $x^TAx\le\rho\|x\|^2$. A vector supported at a maximum-degree vertex and its neighbors gives $\Delta\le\rho^2$. Applying the all-ones vector to the complement, and using $m=n-1$, gives $\rho_c\ge\Delta-2$. A scalar square inequality then yields $8\Delta\le\rho(\Delta+16)$. Combining these estimates with the parent $2\rho\le E$ gives the claimed weights.

[Lean proof](../../results/proofs/fe50c8be74474a25af765edfa59c93a1b0d10745b5dffcea536afda0b5c0a428.lean#L45) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.1_1.5_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_77fd0cb3acfa

**Meaning.** For a tree, the maximum degree is at most the stated combination of the complement spectral product and energy, with weights $1/10$ and $3/2$. Trees with a single vertex are included. The product term uses the largest adjacency eigenvalues of the tree and its complement.

**Proof idea.** The proof obtains a Rayleigh estimate from the positive semidefinite matrix $\rho I-A$. At a maximum-degree vertex, a test vector with center weight five and neighbor weights one gives $10\Delta\le\rho(25+\Delta)$. The tree edge count and complement degree sum give $\rho_c\ge\Delta-2$. Finally the parent $E\ge2\rho$ absorbs the remaining linear term in $\rho$, producing the stated inequality.

[Lean proof](../../results/proofs/adf59e80301f76bd0f5a7674d532377c8fed2e2c96797a502e0daf3926d750c8.lean#L45) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.1_1.7_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_72e0a77a8d94

**Meaning.** For a tree, $\Delta$ is bounded by a weighted combination of $\rho\rho_c$ and energy, using the stated $1/10$ and $17/10$ coefficients. Regularity is not assumed. The tree condition supplies connectedness and the exact relation between vertices and edges that controls the complement spectrum.

**Proof idea.** A maximum-degree vertex and its neighbor indicator give $\Delta\le\rho^2$ through the Rayleigh bound. The complement’s all-ones vector gives $\rho_c\ge n-3\ge\Delta-2$. The parent energy estimate supplies $E\ge2\rho$. The proof then splits at $\rho=10$; nonnegative products and the square $(\rho-5)^2$ combine these bounds into the displayed coefficient choice.

[Lean proof](../../results/proofs/1fc270ee1d71d21d3d851b4cd45d62471ea592587995b9f7f411ba4593ce9e07.lean#L45) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.1_1.9_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_0fa9a5235ce2

**Meaning.** For a tree, the maximum degree is bounded by the given combination of the spectral product and energy, with weights $1/10$ and $19/10$. The source allows every finite tree, including the one-vertex case. The complement need not itself be connected.

**Proof idea.** The complement degree sum and $m=n-1$ give $\rho_c\ge n-3$. A Rayleigh test vector taking value five at a maximum-degree vertex and one on its neighbors gives $10\Delta\le\rho(\Delta+25)$. Since $\Delta+1\le n$, the proof weakens the latter factor to $\rho_c+38$. Expanding that product and applying the parent $2\rho\le E$ to its remaining linear term proves the result.

[Lean proof](../../results/proofs/d1e8923d3c5197a28e9f4b26a2ff2fe8f8d10152e1a6665a72ee1a5df43baa9a.lean#L45) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.1_8.1_estrada_index_average_degree_-0.1_is_connected_fb870a62c3a4

**Meaning.** For a connected graph, the maximum degree is bounded by the stated affine combination of the Estrada index and average degree. The negative constant is part of the bound. A connected one-vertex graph is included, so the theorem does not require at least two vertices.

**Proof idea.** The proof uses the parent $EE\ge n+\Delta^2/6$ and the edge–degree bound $\Delta\le m$. Connectedness supplies $m\ge n-1$, while $\Delta+1\le n$. For fewer than six vertices, these imply $\bar d\ge\Delta/3$. For at least six, they imply $\bar d\ge5/3$. In each case, arithmetic with the quadratic Estrada estimate establishes the stated coefficients and constant.

[Lean proof](../../results/proofs/356fff6c9917f162352004c557d89d90e6b13780bf884aa346fe038bf6117652.lean#L632) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_max_degree_le_0.5_0_graph_energy_size_0_is_regular_a94c88da369c

**Meaning.** For a regular finite simple graph, the maximum degree is at most half the energy: $\Delta\le E/2$. The graph can be empty or disconnected. On a nonempty regular graph, this compares the common degree directly with the total absolute size of its adjacency eigenvalues.

**Proof idea.** The proof chains two regular-graph parents. The first gives $\Delta\le\delta$: both extrema equal the common degree in the nonempty case, while both are zero in the empty case. The second gives $\delta\le E/2$, using the regular degree as an adjacency eigenvalue and the bound $E\ge2\rho$. Transitivity gives the required maximum-degree estimate.

[Lean proof](../../results/proofs/3900b60bbe9416532bf4cf610709112f5e172b98ddd4aab066f084db68d493d5.lean#L193) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull3d_min_degree_le_0_0.5_girth_graph_energy_0_is_regular_344494166939

**Meaning.** For a regular graph, the minimum degree is bounded by half its energy: $\delta\le E/2$. No connectivity premise is needed. The empty graph is included by a separate simplification, while for a nonempty regular graph the minimum degree equals the common degree $d$.

**Proof idea.** The constant vector shows that $d$ is an adjacency eigenvalue of a nonempty $d$-regular graph. Hence $d\le\rho$, since $\rho$ is the largest eigenvalue. The parent spectral-radius energy bound gives $2\rho\le E$. Replacing $\delta$ by $d$ and rearranging these two inequalities gives the conclusion.

[Lean proof](../../results/proofs/268affd5c49c1de3f1a097cd27cbc90f0c9fc35336494e5ef3359a360d3fd8ae.lean#L99) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## hull_max_degree_le_0.375_estrada_index_0.1_67202976fe25

**Meaning.** Every finite simple graph satisfies the stated affine upper bound on maximum degree in terms of the Estrada index, $\Delta\le3EE/8+1/10$. No connectedness or regularity restriction is present. The fixed allowance also covers the empty graph, which has maximum degree zero.

**Proof idea.** The proof expands $EE$ as the sum of nonnegative closed-walk traces divided by factorials. A maximum-degree vertex and its neighbors provide $\operatorname{tr}(A^{2k})\ge2\Delta^k$ for positive $k$. Keeping orders zero, two, four, and six gives $EE\ge n+\Delta+\Delta^2/12+\Delta^3/360$. The bound $n\ge\Delta+1$ and a nonnegative factored cubic then imply the requested affine estimate.

[Lean proof](../../results/proofs/f2d5a73e7815a3919af03fc048f3a67ed1623d9685a4000d24af0ed8d73d8fba.lean#L302) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## koolen_moulton_order_2003

**Meaning.** The energy is at most $\frac n2(1+\sqrt n)$ for every finite simple graph. This bound uses only the vertex count, so it is independent of the edge count, regularity, and connectivity. The empty graph is included without requiring a separate nonempty-vertex premise.

**Proof idea.** The proof builds a symmetric matrix $S$ with eigenvalues given by the signs of those of $A$, choosing $+1$ at zero. Then $S^2=I$ and $E=\operatorname{tr}(AS)$. Splitting $A=(A-J/2)+J/2$, where $J$ is the all-ones matrix, gives two terms. Cauchy–Schwarz bounds the first by $n\sqrt n/2$, since every centered adjacency entry has square $1/4$. Orthogonality bounds the sum of all entries of $S$ by $n$, giving the remaining $n/2$.

[Lean proof](../../results/proofs/0eb3ce80f1f89462d95171f2a8f4c3829810038c6eebbfffe66922499e87b753.lean#L159) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## mcclelland_graph_energy_upper

**Meaning.** Every finite simple graph satisfies $E\le\sqrt{2mn}$. The bound combines the number of vertices with the number of edges and needs no regularity or connectivity hypothesis. If either count is zero, the right side is zero, consistent with the absence of a nonzero adjacency spectrum.

**Proof idea.** The parent squared-energy estimate gives $E^2\le2nm$. The proof rearranges the product to the displayed order $2mn$, then applies monotonicity of the real square root. It uses $\sqrt{E^2}=|E|$ and $E\le|E|$ to pass from the squared inequality to the required energy bound. No further spectral argument is needed.

[Lean proof](../../results/proofs/2715a679aa18d9420bab1ba6ef86b952f310fe3d03220cb80fd858b89667a2fc.lean#L232) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_081bc55d24f66b98c45d

**Meaning.** The square of the graph energy is at most twice the product of vertex and edge counts: $E^2\le2nm$. This applies to every finite simple graph. It is the squared form of the energy upper bound involving $\sqrt{2mn}$, but this proof establishes the square estimate directly.

**Proof idea.** Diagonalizing the real symmetric adjacency matrix shows $\sum_i\lambda_i^2=\operatorname{tr}(A^2)$. Each diagonal entry of $A^2$ is the corresponding degree, so the trace equals $2m$ by the handshake identity. Cauchy–Schwarz, applied to the lists of ones and absolute eigenvalues, gives $(\sum_i|\lambda_i|)^2\le n\sum_i\lambda_i^2$. Substituting the trace identity proves the bound.

[Lean proof](../../results/proofs/31d56b124a4b6a1f293248edb4697660628eba54920978ab3ea2bed9e61c09ee.lean#L285) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_116b5eaad944a7e29fed

**Meaning.** For a connected graph with at least two vertices and maximum degree at most two, the Estrada index is bounded below by the stated linear combination of $n$ and $m$. The restrictions ensure every degree is either one or two; both the vertex term and edge term contribute to the estimate.

**Proof idea.** The proof writes $EE$ as a factorial-weighted series of closed-walk traces. Degree positivity gives $\sum_v\deg(v)^2\ge6m-2n$. Integer two-step walk counts then yield $\operatorname{tr}(A^4)\ge10m-4n$. Three-step counts along edges, together with the degree upper bound, yield $\operatorname{tr}(A^6)\ge44m-24n$. Keeping terms through order six and discarding nonnegative odd traces gives the displayed coefficients.

[Lean proof](../../results/proofs/f42f27782648d97bb700555accf977f9d7abd26591174d6f4563267879407ea7.lean#L23) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_1ea93541073a670fffde

**Meaning.** For a connected graph with at least two vertices and minimum degree at least three, the gap between Estrada index and energy satisfies $EE-E\ge n+m/3$. Thus this premise forces a quantitative separation between the two spectral sums, beyond the unrestricted comparison $EE\ge E$.

**Proof idea.** The degree sum implies $\bar d\ge3$. The proof applies the parent gap bound with the symmetric exponential term and correction $n\bar d(\bar d-1)/14$. A separate scalar estimate, proved from the exponential’s Taylor terms through degree six and tangent bounds on powers at $1.73$, shows that expression is at least $n(1+\bar d/6)$. Finally $n\bar d=2m$ converts it to $n+m/3$.

[Lean proof](../../results/proofs/b1c643181f7fb76ea03f335941f442b8c35a141221c275a08a0577ddb7476490.lean#L412) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_236269be9669ccb9e88c

**Meaning.** The Estrada index satisfies $EE\ge n+\Delta^2/6$ for every finite simple graph. This gives a quadratic contribution from the maximum degree without requiring connectedness or regularity. The proof includes the empty graph, where both the degree contribution and the Estrada sum vanish.

**Proof idea.** A maximum-degree vertex and its neighbors give $\operatorname{tr}(A^4)\ge2\Delta^2$ and $\operatorname{tr}(A^6)\ge2\Delta^3$, by counting walks through that vertex. The second-power trace is $\operatorname{tr}(A^2)=2m$, and $m\ge\Delta$. Keeping these even terms in the nonnegative trace series gives $EE\ge n+m+\Delta^2/12+\Delta^3/360$. A scalar inequality obtained from $\Delta(\Delta-15)^2\ge0$ turns the last three terms into at least $\Delta^2/6$.

[Lean proof](../../results/proofs/006adaf6f7f8d46160131e14c05616cb4636e18e76dea78e80b5b7877b686f89.lean#L448) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_24baa9bb5c5a3c6be85d

**Meaning.** Under the source’s exact guard $\rho\ge9999999/10000000$, this lower bound keeps the full contribution $e^\rho$ and estimates the remaining eigenvalues using their residual squared sum $2m-\rho^2$. The remaining linear contribution is $n-1-\rho$; its quadratic coefficient is determined by the exponential at $-\rho$.

**Proof idea.** Nonnegative odd walk traces rule out any eigenvalue below $-\rho$: such an eigenvalue would dominate sufficiently high odd powers. The proof then shows $(e^x-1-x)/x^2$ is increasing away from zero, using exponential secants and repeated halving. Hence every remaining eigenvalue satisfies a quadratic lower bound with coefficient $(e^{-\rho}+\rho-1)/\rho^2$. Separating one maximum eigenvalue and using zero trace and $\sum\lambda_i^2=2m$ finishes the sum.

[Lean proof](../../results/proofs/2572ff9fbce9a9ab46b58c132da07db8189d9031ea7ffea9945efe05c9591eed.lean#L22) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_2649c493de46c591f981

**Meaning.** If the maximum degree is at most two, then $E\le2(n+m)/3$. The graph may be disconnected and may contain isolated vertices. The source’s slightly larger rational upper guard is equivalent to this degree condition because maximum degree is an integer.

**Proof idea.** A largest eigenvector coordinate gives $|\lambda_i|\le2$. For $0\le t\le2$, the nonnegative product $(t-1)^2(2-t)(t+4)$ proves a quartic upper bound on $18t$. The proof sums that bound over absolute eigenvalues. Integer two-step walk counts and degree values zero, one, or two give $\sum\lambda_i^4\ge10m-4n$, while $\sum\lambda_i^2=2m$. Substitution yields the stated energy estimate.

[Lean proof](../../results/proofs/99c699dc4321fa05d012b2990fc87397b27c074905749382ce469c096bd41353.lean#L604) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_380f64eac06a6c296479

**Meaning.** For every finite simple graph, $EE$ is at least the symmetric exponential quantity $C$, plus the displayed fourth-moment correction $n\bar d(\bar d-1)/24$. The correction is positive when $\bar d>1$ and need not be positive for sparse graphs. No regularity or connectivity premise is imposed.

**Proof idea.** Convexity of powers applied to squared eigenvalues gives $\operatorname{tr}(A^{2k})\ge n\bar d^k$; odd traces are nonnegative walk counts. These compare the exponential series with $C$ term by term. Integer entries of $A^2$, its degree-valued diagonal, and the degree square-mean inequality strengthen the fourth trace to $n(2\bar d^2-\bar d)$. Keeping that extra fourth coefficient produces the correction after taking the series limit.

[Lean proof](../../results/proofs/827771ede66823007430689a1ae3e13571153a34d97f2308009b7a2309285873.lean#L877) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_5fd1e4b087f7c2ab56ec

**Meaning.** For a connected graph with at least two vertices and maximum degree at most two, $EE-E\ge C-n\sqrt{\bar d}$. Equivalently, the displayed symmetric exponential expression controls the gap. These are the indexed premises, although the proof’s main moment comparison does not require the degree upper bound.

**Proof idea.** The second spectral moment is $n\bar d$. Convexity of powers of the squared eigenvalues gives each even moment at least $n\bar d^k$, and adjacency powers have nonnegative traces. Comparing exponential coefficients therefore gives $EE\ge C$. Cauchy–Schwarz gives $E\le n\sqrt{\bar d}$. Subtracting the energy upper bound from the Estrada lower bound proves the gap estimate.

[Lean proof](../../results/proofs/371b690f64efb9842acdfffb7209f28708b92c1796a076bdb134fe04976e470c.lean#L796) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_63aaabca8d79723937de

**Meaning.** For a connected graph with at least two vertices, this energy bound subtracts the displayed correction from $n\sqrt{\bar d}$. The denominator is the maximum of one and a degree-dependent expression, so it is always positive. The correction measures a departure from the basic square-mean energy estimate.

**Proof idea.** Let $T=\sum_i(\lambda_i^2-\bar d)^2$. Integer two-step walk counts and the degree square-mean inequality give $T\ge n\bar d(\bar d-1)$. A maximal eigenvector coordinate gives $|\lambda_i|\le\Delta$. Factoring $\lambda_i^2-\bar d=(|\lambda_i|-a)(|\lambda_i|+a)$ bounds $T$ by $2a(\Delta+a)^2(na-E)$. The parent squared-energy bound ensures $na-E\ge0$, allowing replacement of that factor by the displayed positive denominator and division.

[Lean proof](../../results/proofs/ae91bfb5e2966642b943b32de1634415b087a4c7869fbe518b7e2fbae0ae68d0.lean#L1069) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_6bde2f687ba9b3e6e8a5

**Meaning.** For a connected regular graph with at least two vertices, energy is at least the maximum of the two displayed lower bounds involving the normalized gap and spectral spread. Taking the maximum keeps whichever estimate is larger. The denominator in the second estimate is protected by a maximum with one.

**Proof idea.** The first bound is supplied by the parent estimate using the two largest adjacency eigenvalues. For the second, regularity gives adjacency eigenvalues $d(1-\mu_i)$ from normalized Laplacian eigenvalues. Apart from one eigenvalue $d$, positive eigenvalues are capped by $\alpha=d\max(0,1-\eta)$; negative magnitudes are capped by $-\ell$. Bounding their squares with these caps, then using zero trace and squared sum $nd$, produces the second fraction.

[Lean proof](../../results/proofs/930ce1cd21ef61e13ae3a98cbc5baff95347a3070ada7851dbc3948872bc7972.lean#L631) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_858f11e4042b2a0e80d8

**Meaning.** If the maximum degree is at most two, energy is bounded by $n\sqrt{\bar d}$ minus the displayed correction with denominator $48$. This allows disconnected graphs and isolated vertices. When $\bar d\le1$ the correction is nonpositive, so the basic square-mean bound already implies the statement.

**Proof idea.** The parent squared-energy bound gives $E\le n\sqrt{\bar d}$. For $\bar d>1$, the degree-sum parent gives $\bar d\le2$, and maximal eigenvector coordinates give $|\lambda_i|\le2$; hence $a\le3/2$. The variance $T=\sum_i(\lambda_i^2-\bar d)^2$ is at least $n\bar d(\bar d-1)$ by two-step walk integrality and degree squares. A factored scalar inequality on this bounded interval gives $E\le na-T/48$. Substituting the variance lower bound completes the correction.

[Lean proof](../../results/proofs/9e5d9bb27b319b038fe8ad28178f6c91fb9611abd7241512a2c36a8370488a7f.lean#L847) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_97775ef52738c74004cd

**Meaning.** Every finite simple graph satisfies $EE\ge n+m+\Delta^2/12$. The vertex and edge terms are supplemented by a quadratic maximum-degree term. No connectedness or regularity is required, and the empty graph is explicitly included.

**Proof idea.** The proof uses $EE=\sum_{k\ge0}\operatorname{tr}(A^k)/k!$, whose terms are nonnegative because adjacency powers count walks. The zeroth trace is $n$, the first is zero, and the second is $2m$. At a maximum-degree vertex, the diagonal of $A^2$ contributes $\Delta^2$ to the fourth trace. Its neighbors contribute at least another $\Delta^2$, since they share that vertex. Retaining the fourth term gives $\Delta^2/12$.

[Lean proof](../../results/proofs/759e9ee6217e60406aefd1eaf58c434ba116a5a375ec52ff1c35070b76c243fb.lean#L216) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_a256bd085bb7ac490e7c

**Meaning.** The Estrada index is at least $n+m$ plus the stated quadratic and cubic terms in maximum degree. This strengthens the estimate that retains only the quadratic term. The statement covers every finite simple graph, including disconnected and empty graphs.

**Proof idea.** The proof retains orders zero, two, four, and six in the nonnegative closed-walk trace series. A maximum-degree vertex and its neighbors provide $\operatorname{tr}(A^4)\ge2\Delta^2$. Three-step walks from the center to each neighbor number at least $\Delta$; symmetry then gives contributions totaling at least $2\Delta^3$ to the sixth trace. Dividing these moments by their factorials produces the quadratic and cubic coefficients.

[Lean proof](../../results/proofs/97dfd5286c0c8f1a422fa0c70c874d9e4f65b4f3d934327b52c0a0d61d5edfd2.lean#L379) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_a8dbf81d1cb58f023c39

**Meaning.** Under the exact source guard $s\ge9999999/10000000$, this is an upper bound on $EE$ using the largest and smallest adjacency eigenvalues. The displayed expression uses $\ell=\rho-s$ and divides by the positive spread. It is an endpoint interpolation estimate for the exponential sum.

**Proof idea.** Convexity of $e^x$ places its value at each eigenvalue below the chord joining $\ell$ and $\rho$. Multiplying by $s=\rho-\ell$ gives $s e^{\lambda_i}\le(\rho-\lambda_i)e^\ell+(\lambda_i-\ell)e^\rho$. Summing cancels the eigenvalue terms because the adjacency trace is zero. The proof divides by the positive spread and rewrites $\ell$ in terms of $\rho$ and $s$.

[Lean proof](../../results/proofs/ba163ac43dba3a218eabfb56fe09e16bd2db79c562fba3e667977f6bfba15c75.lean#L903) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_ab71923bd68f658bd3e6

**Meaning.** For a connected graph with at least two vertices, the stated lower bound on $EE-E$ replaces energy by an upper estimate involving the two spectral extremes and a square root. The same $EE$ appears on both sides; the mathematical content is the associated energy upper bound.

**Proof idea.** The proof chooses eigenvalues attaining $\rho$ and $\ell$, and zero trace shows $\rho\ge0\ge\ell$. Removing those two terms leaves $n-2$ eigenvalues with squared sum $2m-\rho^2-\ell^2$. Cauchy–Schwarz bounds their absolute sum by the displayed square root. Adding the two extreme magnitudes contributes $s$. If both selected indices coincide, all eigenvalues are zero. Finally subtracting this energy bound from $EE$ proves the statement.

[Lean proof](../../results/proofs/1440142866ae83c99630eb81dda2b377b61fa6cf2f49146f3220fbac41bdc31d.lean#L23) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_be27f4e8aad2bd34983e

**Meaning.** For a connected graph with at least two vertices and maximum degree at most two, the gap $EE-E$ exceeds $C-na$ by the displayed correction $n\bar d(\bar d-1)/16$. The correction becomes a nonnegative improvement when average degree is at least one.

**Proof idea.** For $\bar d\le1$, the parent gap estimate $EE-E\ge C-na$ suffices because the correction is nonpositive. Otherwise define $T=\sum_i(\lambda_i^2-\bar d)^2$. Walk integrality gives $T\ge n\bar d(\bar d-1)$. The degree-sum parent gives $\bar d\le2$; the spectral cap then yields $E+T/48\le na$. Comparing exponential coefficients and retaining the excess fourth moment gives $EE\ge C+T/24$. Subtracting combines the two contributions into $T/16$, yielding the claimed correction.

[Lean proof](../../results/proofs/07b90a7e06f1754d9806db7a7681b4c2addf45b4f0f339f0dcb81295e723f95f.lean#L902) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_c71b19aef6e373b1bdc9

**Meaning.** If the graph has at least one edge, the gap in the energy–edge upper bound satisfies $2m-E\ge(s-2)^2/2$. The edge premise guarantees a nonzero adjacency spectrum, including a positive maximum and a negative minimum. No connectivity or regularity condition is needed.

**Proof idea.** The product of the nonzero eigenvalues, up to sign, is a nonzero integer characteristic-polynomial coefficient, so its absolute value is at least one. Using $t\le e^{t-1}$ gives $E$ at least the number of nonzero eigenvalues. Consequently $\sum_{\lambda_i\ne0}(|\lambda_i|-1)^2\le2m-E$. Keeping the maximum and minimum terms and applying the two-term square inequality gives $(s-2)^2/2\le2m-E$.

[Lean proof](../../results/proofs/a3d239c146cb660bdeef1d8d1e7b810e0545c712f086d0953a9470c0d9c5622f.lean#L22) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_db893752e0181a616e22

**Meaning.** For $n\ge2$ and the exact source guard $\bar d\ge9999999/10000000$, this lower bound on $EE-E$ adds the displayed correction with denominator $14$ to $C-na$. Connectedness and a maximum-degree cap are not assumed. The precise real-valued threshold is slightly below one.

**Proof idea.** Write $T=\sum(\lambda_i^2-\bar d)^2$ and $W=\sum(\lambda_i^2-\bar d)^2(\lambda_i^2+2\bar d)$. Walk and degree estimates give $T\ge n\bar d(\bar d-1)$. The exponential moment comparison retains $T/24+W/720$ beyond $C$. A separate polynomial inequality, proved by factoring nonnegative squares and bounding a univariate polynomial, gives $E+5T/168\le na+W/720$. Subtraction cancels $W$ and leaves $T/14$, giving the result.

[Lean proof](../../results/proofs/707e24796b5b599c02b50acec4f59af4ba2aedaac2c7cd2ad51f695f5b9d72c0.lean#L22) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_e994aba553207072b689

**Meaning.** For a connected graph with at least two vertices, the Estrada index is at least $n+m$ plus the displayed correction $(5m-2n)/12$. The correction comes from fourth-order closed walks. No upper or lower degree restriction beyond what connectedness supplies is imposed.

**Proof idea.** Every vertex has positive integer degree, so $\deg(v)^2\ge3\deg(v)-2$. Summing gives $\sum_v\deg(v)^2\ge6m-2n$. Integer two-step walk counts, with the diagonal of $A^2$ kept exactly, give $\operatorname{tr}(A^4)\ge2\sum_v\deg(v)^2-2m\ge10m-4n$. The nonnegative exponential trace series contributes $n+m$ at orders zero and two, and the fourth term supplies the stated correction.

[Lean proof](../../results/proofs/0f40cb529482155360c8326e24add94ffcd26bff96e6bc423f92a4675f7a8bd7.lean#L23) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_ec4f3d91aaed60f3f436

**Meaning.** For a connected graph with at least two vertices and maximum degree at most two, energy satisfies $E\le\frac23(n+m)$. This indexed statement keeps all three premises. Its value agrees with the separate estimate for arbitrary graphs whose maximum degree is at most two.

**Proof idea.** The proof invokes that broader parent estimate, $E\le2(n+m)/3$, using only the degree component of the stated guard. The parent uses a quartic bound for absolute eigenvalues in the interval $[0,2]$, together with a fourth-moment lower bound. Here the remaining step is just the identity $2(n+m)/3=(2/3)(n+m)$; connectivity and the vertex-count premise are retained in the statement.

[Lean proof](../../results/proofs/8e151998d30bd64d00db4b8c6efd864066fcd5e371a9a8d35521cca89a117ea6.lean#L223) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_ef33481da37040865734

**Meaning.** With the exact source guard $\rho\ge9999999/10000000$, this Estrada lower bound singles out $e^\rho$ and adds a quadratic estimate for the remaining spectrum. Their squared sum is $2m-\rho^2$, and the coefficient used for that contribution is $e^{-\rho}/2$.

**Proof idea.** The proof compares an eigenvector with its coordinatewise absolute value to show every eigenvalue lies in $[-\rho,\rho]$. It proves $e^x\ge1+x+e^{-\rho}x^2/2$ for $x\ge-\rho$, treating positive and negative $x$ separately. The resulting remainders are nonnegative, so their total dominates the remainder at a maximum eigenvalue. Zero trace and squared sum $2m$ then isolate that eigenvalue and produce the displayed bound.

[Lean proof](../../results/proofs/a2095b3fa8601001c9a3e4cac425741ce11a1c23f92c0a96d14bac1994af0262.lean#L22) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_f1abeb346d4f50c57240

**Meaning.** For a connected regular graph with at least two vertices, $E\ge2\bar d(1+\max(0,1-\eta))$. The normalized gap therefore strengthens the basic $2\bar d$ lower bound whenever it is below one. The maximum with zero keeps the extra contribution from becoming negative.

**Proof idea.** Regularity gives $\bar d=d$ and $A=d(I-N)$ for normalized Laplacian $N$. The proof identifies the adjacency spectrum with $d(1-\mu_i)$ through characteristic polynomials. The smallest normalized eigenvalue is zero, giving an adjacency eigenvalue $d$; the second-smallest gives $d(1-\eta)$. These are distinct positions. Summing their nonnegative quantities $|x|+x$, and using the zero total eigenvalue sum, gives twice their positive contributions, which is the claimed energy bound.

[Lean proof](../../results/proofs/faf6e3eb77951df83cee3254191f889390722f1d9dde37c18bce10295d345023.lean#L174) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)

## model_f8f2b4afb071e2a10817

**Meaning.** For a connected regular graph with at least two vertices, $EE$ is at least $C$ plus the displayed correction involving $n$, the common degree $\bar d$, and $\bar d+7$. This correction incorporates both fourth and sixth moments. Regularity is retained as an explicit premise.

**Proof idea.** The proof uses regular row sums to establish $\operatorname{tr}(A^4)\ge n(2d^2-d)$. Three-step walk counts along each edge are at least $2d-1$, yielding $\operatorname{tr}(A^6)\ge n(5d^3-6d^2+2d)$. Convexity supplies the baseline even moments $nd^k$, and odd traces are nonnegative. The excess fourth and sixth factorial-weighted terms above the symmetric exponential series combine into $nd(d-1)(d+7)/180$. The handshake identity replaces $d$ by $\bar d$.

[Lean proof](../../results/proofs/c5a34f7d911ec60d44eca18f2084bdf6c9487b789c2237709a86c3e46d229e65.lean#L1064) · [Full statement and frozen assessment](../../results/all-proofs.md#energy-and-estrada-index)
