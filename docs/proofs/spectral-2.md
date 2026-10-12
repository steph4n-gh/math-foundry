# Spectral bounds: explanations, part 2

[Back to the proof index](../../results/all-proofs.md) · [All explanations](README.md)

All graphs in these notes are finite and simple. Write n for the number of vertices, m for the number of edges, Δ and δ for maximum and minimum degree, and d = 2m/n for average degree, with d = 0 when n = 0. A is the adjacency matrix and D is the diagonal degree matrix. The number r (often denoted ρ) is the largest eigenvalue of A, and q is the largest eigenvalue of the signless Laplacian Q = D + A. The adjacency spread s is its largest eigenvalue minus its smallest. Empty-graph spectral extrema are defined as zero.

The ordinary Laplacian is L = D − A; μmax is its largest eigenvalue. The normalized Laplacian is RLR, where R has diagonal entries 1/√deg(v), using zero at degree zero. Its largest eigenvalue is νmax. In the statements below, μ₂ and ν₂ are the second-smallest eigenvalues of their respective matrices when G is connected and n ≥ 2, and are defined as zero otherwise. These notes describe the arguments informally; the linked source gives each exact statement.

## hull_spectral_radius_le_1_max_degree_0_e423c6789900

**Meaning.** The largest adjacency eigenvalue r is at most the maximum degree Δ. Thus the strongest adjacency eigenvalue cannot exceed the largest number of neighbors of a vertex. There are no connectivity or regularity assumptions, and the empty graph has r = 0.

**Proof idea.** For each eigenvalue, choose a nonzero eigenvector and a coordinate with largest absolute value. The eigenvector equation at that vertex expresses the eigenvalue times this coordinate as a sum over neighbors. The triangle inequality bounds the sum by the degree times the same absolute value. Cancel the positive coordinate magnitude, then bound the degree by Δ.

[Lean proof](../../results/proofs/7fe3b9100e346ebd5b676b2f6827d6666435855004f679ea73fa56a5cbbcc2a4.lean#L509) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_radius_le_1_size_0_0f3ad4f640d7

**Meaning.** The largest adjacency eigenvalue r is at most the number m of edges. The statement applies to every finite simple graph, including disconnected graphs and the empty graph. It bounds a spectral quantity using only the total number of edges.

**Proof idea.** Take an eigenvector and a coordinate of maximal absolute value. The neighbor sum in the eigenvector equation is bounded by the vertex degree times that coordinate magnitude. Cancelling gives an upper bound by the degree. Every edge incident to the chosen vertex belongs to the graph’s edge set, so that degree is at most m. Apply the argument to all eigenvalues.

[Lean proof](../../results/proofs/fc91c7c2106f32904f4dda599e5253e243208f588f32d8f7e30e14027cfe518d.lean#L576) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_0.625_size_1.6_23b23e65e937

**Meaning.** The adjacency spectral spread s, the largest eigenvalue minus the smallest, satisfies s ≤ 5m/8 + 8/5. This is a linear upper bound in the number of edges, valid without any connectivity assumption and with spread zero for the empty graph.

**Proof idea.** Diagonalizing the adjacency matrix and taking the trace of its square gives the identity ∑λ² = 2m. The two extreme eigenvalues contribute at most this sum, so their squared difference is at most 4m. The square of 5m/8 + 8/5 is at least 4m, as follows by expanding a nonnegative square. Its nonnegativity then permits comparison of the unsquared quantities.

[Lean proof](../../results/proofs/782a3d40cbadab28bb2f166d1f2bdf905ec54cc9bac139f3cd9770e25fce133a.lean#L666) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_0.833333_size_1.16667_7a01f96f9ef4

**Meaning.** The adjacency spectral spread is bounded by a linear expression with slope approximately 0.833333 and intercept approximately 1.166667. The exact rational coefficients in the linked statement are slightly larger than 5/6 and 7/6. The assertion covers every finite simple graph.

**Proof idea.** The trace identity ∑λ² = 2m bounds the squared spread by 4m. The proof first establishes 4m ≤ (5m/6 + 7/6)²: it checks m = 0 and m = 1 separately, then uses the nonnegative product (m − 1)(25m − 49) for integer m ≥ 2. Taking the nonnegative square comparison gives the simpler linear bound; enlarging its coefficients yields the exact statement.

[Lean proof](../../results/proofs/9da42ad14bc8a9d350674449998dd0cfb9f27690546e4583a5cd060724758c38.lean#L666) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_1_nordhaus_gaddum_spectral_sum_1_1136dbf5ed1c

**Meaning.** Let S = r(G) + r(Gᶜ), where Gᶜ is the complement on the same vertices. The adjacency spread of G is at most S + 1. This controls the lower end of G’s spectrum using the largest eigenvalue of its complement, without requiring either graph to be connected.

**Proof idea.** Write A and B for the two adjacency matrices and J for the all-ones matrix. The complement identity is A + B + I = J. If b is B’s largest eigenvalue, bI − B is positive semidefinite, as is J. Their sum is A + (b + 1)I. Evaluating it on each unit eigenvector of A proves every adjacency eigenvalue is at least −b − 1, which gives the spread bound.

[Lean proof](../../results/proofs/0a130fdbb45d6914c1e54f3f76e6c4c66c92dae06970d948c14d058a6ef7ea30.lean#L10) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_2_nordhaus_gaddum_spectral_sum_0_24c7f07054c7

**Meaning.** For S = r(G) + r(Gᶜ), the adjacency spread satisfies s(G) ≤ 2S. The result applies to arbitrary finite simple graphs. In particular, it combines a spread bound for G with the nonnegativity of the complement’s largest adjacency eigenvalue.

**Proof idea.** An eigenbasis expansion bounds every adjacency quadratic form by r times the squared norm. Replacing a unit eigenvector’s coordinates by their absolute values preserves its norm and makes the quadratic form at least the negative of the original one. Hence every eigenvalue is at least −r, giving s ≤ 2r. Applying the same comparison to the complement also gives r(Gᶜ) ≥ 0; adding its contribution proves the stated bound.

[Lean proof](../../results/proofs/ff76be81e3fff0305bfaa5f5cab4a467f90b8f49aebc7b80ce3c190055edec0b.lean#L10) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_2_size_0_fde49a23163f

**Meaning.** The adjacency spectral spread s is at most twice the number m of edges. No assumptions about connectivity or degrees are needed. The intermediate quantity in this proof is the graph energy E, the sum of the absolute values of all adjacency eigenvalues.

**Proof idea.** The proof chains s ≤ E with E ≤ 2m. The first parent combines s ≤ 2r with E ≥ 2r, the latter following from the zero sum of adjacency eigenvalues. The energy upper bound expands eigenvalues along an orthonormal eigenbasis and uses |ab| ≤ (a² + b²)/2 on each adjacent pair. Summing over the basis gives one per directed edge, hence 2m.

[Lean proof](../../results/proofs/c94ff193d96a8e87ec7dce561d778f143c71aae9219b599ab261903eadb7990e.lean#L482) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## hull_spectral_spread_le_2_sqrt_size_0_fe80d135635b

**Meaning.** The adjacency spectral spread satisfies s ≤ 2√m for every finite simple graph. The spread is the difference between the largest and smallest adjacency eigenvalues. An empty graph has spread zero, so it is included in this bound.

**Proof idea.** The spectral decomposition identifies ∑λ² with the trace of A². Its diagonal entries are the vertex degrees, whose sum is 2m. If the extreme eigenvalues are distinct entries, their squares sum to at most 2m; adding the nonnegative square of their sum bounds their squared difference by 4m. Compare this with (2√m)² and use the nonnegativity of 2√m. Coincident extreme entries give spread zero directly.

[Lean proof](../../results/proofs/8dee79deeed18ef63bd9cb9a7731767dfdbd625ce391cf78601ff418793b6f19.lean#L666) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_00c10ac49d00184b94a2

**Meaning.** For a connected, nonregular graph with n ≥ 3, put t = Δ − δ and a = δν₂. Here ν₂ is the second-smallest eigenvalue of the normalized Laplacian. The bound is q ≤ 2Δ − 2at/[n max(1, a + 2t)], giving a quantified reduction from twice the maximum degree.

**Proof idea.** The checked comparison a ≤ μ₂ supplies a Laplacian energy bound after removing the constant part of a unit signless eigenvector. At a minimum-degree vertex, the degree deficit contributes 2t times the squared coordinate. Cauchy–Schwarz controls the remaining coordinate differences. A weighted square inequality combines these contributions to bound 2Δ minus each signless eigenvalue from below; the maximum in the denominator ensures positive division.

[Lean proof](../../results/proofs/be265ad090efd9a357b2fc1a1056a5e9c9591389e3547ebd3c94cc2621c0533e.lean#L239) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_058cec8793b79911021d

**Meaning.** For n ≥ 2, let S = r(G) + r(Gᶜ) and d = 2m/n. Then (n − 1)(S² − (n − 1)²) is at least four times the larger of (Δ − d)² and (d − δ)². Thus extreme degree deviations force the spectral sum above its basic complement bound.

**Proof idea.** The shifts r(G)I − A and r(Gᶜ)I − B are positive semidefinite. On the all-ones vector and the centered vector neᵥ − 1, their mixed products are opposite degree deviations. Quadratic-form Cauchy–Schwarz bounds their squared size by the combined diagonal terms. The identity A + B + I = J and S ≥ n − 1 simplify these terms. Apply the resulting vertex inequality at maximum- and minimum-degree vertices.

[Lean proof](../../results/proofs/3e4b6c58f49c2bb6f90bf663d0b1cb349bd2df9ec20b3f10203babd52c71c4d0.lean#L246) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_05bc265566a122307820

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, the excess q − 2r is at least δν₂(Δ − δ)² divided by 8nΔ² + (Δ − δ)². The normalized gap ν₂ therefore gives a lower bound on this excess when the vertex degrees vary.

**Proof idea.** The proof establishes δν₂ ≤ μ₂ using a degree-weighting map: it preserves Laplacian energy and increases squared norm by at least a factor δ. A nonzero vector chosen from the two lowest Laplacian eigenspaces becomes orthogonal to the lowest normalized eigenspace after weighting. The checked parent bounds μ₂(Δ − δ)² by the denominator times q − 2r. Substitute the comparison and divide by the positive denominator.

[Lean proof](../../results/proofs/a985d9f2e0d3cecfef3eb76ff72cd62b1b4276a2424da24412192c3b7b2d1afb.lean#L790) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_19a4636366d151f7cbf8

**Meaning.** For n ≥ 2, the signless largest eigenvalue q satisfies (q − Δ)((n − 1)q − 4m + 3Δ) ≥ Δ². This relates q simultaneously to the largest degree and the total edge count. Connectivity and regularity are not assumed.

**Proof idea.** The matrix qI − Q is positive semidefinite. Evaluate its quadratic form on teᵥ + 1, where v has maximum degree and t is any real number. The coefficients are q − Δ, twice q − 2Δ, and nq − 4m, because Q1 is twice the degree vector. A quadratic polynomial nonnegative for every t has nonpositive discriminant. Expanding that discriminant and rearranging yields the claimed product inequality.

[Lean proof](../../results/proofs/9d866b6aa62e29cd38dfe5d46facd91580dc4ca82c456c32b8cba922c68adb40.lean#L24) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_1a6c4802c53ac6e934ab

**Meaning.** For n ≥ 2, the squared adjacency eigenvalue r² exceeds the squared average degree d² by at least (Δ − δ)²/(2n). Equivalently, 2n(r² − d²) ≥ (Δ − δ)². The bound measures the effect of the range of vertex degrees.

**Proof idea.** Absolute-coordinate comparison puts every adjacency eigenvalue between −r and r. Expanding vectors in the eigenbasis therefore gives ‖A1‖² ≤ r²‖1‖², or ∑deg(v)² ≤ nr². Subtracting nd² bounds the sum of squared degree deviations by n(r² − d²). The maximum and minimum degree deviations alone show that this sum is at least half the squared degree range. Combining the two estimates proves the result.

[Lean proof](../../results/proofs/2427eb31323796871649f1f41f5b2ce060eea05442346c9b7941c400d0dd48db.lean#L225) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_2b5ad0c361dc68282aa2

**Meaning.** For a connected graph with n ≥ 2, the largest Laplacian eigenvalue μmax and the second-smallest μ₂ satisfy μmax + (n − 2)μ₂ ≤ 2m. Thus the edge count limits the simultaneous size of these two ends of the Laplacian spectrum.

**Proof idea.** The proof orders the Laplacian eigenvalues from largest to smallest and computes their sum from the trace of L, obtaining 2m. Remove the largest and smallest entries. Each of the remaining n − 2 entries is at least the second-smallest eigenvalue; the removed smallest entry is nonnegative because L is positive semidefinite. Add these estimates to the largest entry and compare with the full eigenvalue sum.

[Lean proof](../../results/proofs/b8af3d59dc5584beb8384843eb0be17dead9e58e8c587391fbc6d76414b9f781.lean#L261) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_2cc243ec07f2570b6bd7

**Meaning.** For a connected, nonregular graph with n ≥ 3, the signless largest eigenvalue is strictly less than 2Δ. The connectedness assumption ties together the coordinates needed to exclude equality, while nonregularity says that some vertex degrees differ.

**Proof idea.** The parent gives q ≤ 2Δ. Suppose equality holds and choose a unit eigenvector for q. The degree bound and nonnegative Laplacian quadratic form force its Laplacian energy to vanish. It therefore lies in the Laplacian kernel, so connectedness makes every coordinate the same nonzero value. The signless eigenvector equation then forces every degree to equal Δ. This contradicts nonregularity and makes the inequality strict.

[Lean proof](../../results/proofs/7f05636b9c8ef02c628956bfac12eeb8174d91c253736f5cddb31fec2f732155.lean#L78) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_2ef8a5ad6dd5bc992535

**Meaning.** For every graph with n ≥ 2, 2n(r² − d²) ≥ (Δ − δ)², where d is the average degree and r is the largest adjacency eigenvalue. Larger variation between the maximum and minimum degrees therefore requires a larger difference of these squared quantities.

**Proof idea.** For each unit eigenvector, taking absolute values of its coordinates shows that the absolute eigenvalue is at most r. The eigenbasis then gives an operator norm bound, applied to the all-ones vector to obtain ∑deg(v)² ≤ nr². Center the degrees at their average to turn this into a variance bound. Keeping only maximum- and minimum-degree terms and using a nonnegative square bounds the squared range by twice that variance.

[Lean proof](../../results/proofs/0d7c5f6da7bf8fe93fb780162da4d77b31dee6c8f073914b434c6342d4215b2a.lean#L174) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_480476520e017d731b8e

**Meaning.** For a connected graph with n ≥ 2, 2Δ(q − 2r) ≥ μ₂(r − d). It connects the signless excess q − 2r with how far the largest adjacency eigenvalue lies above the average degree, scaled by the Laplacian gap.

**Proof idea.** The proof uses the checked parent (q − 2r)(r + Δ) ≥ μ₂(r − d), together with d ≤ r ≤ Δ and μ₂ ≥ 0. If Δ = 0, then r and d are both zero and the claim is immediate. Otherwise the parent implies q − 2r ≥ 0. Since r + Δ ≤ 2Δ, increasing this factor preserves the inequality and gives the stated result.

[Lean proof](../../results/proofs/e3334c7eaffe0ead397b58b6075cba41e1a9ada722f9b8d47915443b07ca40cc.lean#L555) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_58d23cdf98e2b9057748

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, q − 2r is at least μ₂(Δ − δ)²/[8nΔ² + (Δ − δ)²]. This expresses a lower bound for the signless excess in terms of the ordinary Laplacian gap and degree range.

**Proof idea.** The checked parent already proves the same inequality after multiplication by 8nΔ² + (Δ − δ)². Its proof relates degree variance to r − d and then uses the gap estimate 2Δ(q − 2r) ≥ μ₂(r − d). Here the only remaining step is division: n and Δ are positive, so the denominator’s first summand is positive and its squared-range summand is nonnegative.

[Lean proof](../../results/proofs/5376d8f358cc898a924bd3e232d00b7221b50e0ec828b26427141ea7e13dc95a.lean#L790) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_60716014e2e559489a74

**Meaning.** For n ≥ 2, (n − 1)μ₂ ≤ nδ. The quantity μ₂ is the second-smallest Laplacian eigenvalue on connected graphs and is defined as zero on disconnected graphs in this statement. Consequently, the disconnected case follows from degree nonnegativity.

**Proof idea.** In the connected case, select a minimum-degree vertex v and use the centered vector neᵥ − 1. Its squared norm is n(n − 1), and its Laplacian energy is n²deg(v). Connectedness makes the Laplacian zero eigenvector constant, so this trial vector is orthogonal to it. Expansion in the ordered eigenbasis bounds its energy below by μ₂ times its squared norm. Substitute deg(v) = δ and cancel n.

[Lean proof](../../results/proofs/b20694cf2c7ab1d0554a91d2c52afaafc6db9f4d012b5f745003851e2ce9381c.lean#L973) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_61856b7405177b7972cd

**Meaning.** For every finite simple graph, nq ≥ 4m. When n is positive, this says that the largest signless Laplacian eigenvalue is at least twice the average degree. The version without division also includes the empty graph.

**Proof idea.** The eigenbasis of Q bounds its quadratic form on any vector by q times the squared norm. Apply this to the all-ones vector, whose squared norm is n. Each row of Q sums to twice its vertex degree, so the quadratic form is twice the degree sum, namely 4m. Comparing the two expressions proves the bound. The empty case has no edges and reduces to equality.

[Lean proof](../../results/proofs/a79d6b4118c6e32df9186bfc90963673d5b84a4ee902d10837302809ff468857.lean#L694) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_6248b9040d61e70779fc

**Meaning.** For a connected, nonregular graph with n ≥ 3, n(μ₂ + 2)(2Δ − q) ≥ 2μ₂. This quantifies the distance of the signless largest eigenvalue below 2Δ using the ordinary Laplacian gap, without a degree-range factor in the final expression.

**Proof idea.** Nonregularity supplies a vertex whose degree is at least one below Δ. For a unit eigenvector of q, write 2Δ − q as its Laplacian energy plus twice its weighted degree deficits. Remove its constant component; the gap bounds the remaining squared norm, while the chosen deficit contributes at least twice the chosen squared coordinate. Cauchy–Schwarz controls coordinate differences. Summing a weighted square inequality combines the two lower bounds into the stated estimate.

[Lean proof](../../results/proofs/64e2ed64f0ec32aa095a26b4a38a55d56dfee04134cb4c202932c7f9b3428bc9.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_6915c570cfc511f1f88f

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, (q − 2r)(r + Δ) ≥ μ₂(r − d). This compares the signless excess with the adjacency eigenvalue’s excess above average degree, using the ordinary Laplacian spectral gap.

**Proof idea.** Choose unit vectors x for the largest adjacency eigenvalue and u for the constant direction, and let t be their inner product. Projecting x off u gives Laplacian energy at least μ₂(1 − t²); Q = L + 2A bounds that energy above by q − 2r. Conversely, the adjacency lower bound −Δ applied to u − tx gives r − d ≤ (r + Δ)(1 − t²). Multiply and combine the estimates.

[Lean proof](../../results/proofs/d73b15dcd3e81341878ee8ece422f8c0292f7bcbc1eb6f2dce3d3aa5f3008aab.lean#L291) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_69d93273dcefb22a5491

**Meaning.** For a connected regular graph with n ≥ 2 and common degree Δ, ((n − 1)μmax − nΔ)(nΔ − (n − 1)μ₂) ≥ nΔ(n − Δ − 1). It constrains the positions of the largest and second-smallest Laplacian eigenvalues around their mean.

**Proof idea.** Regularity makes L = ΔI − A. Taking traces gives ∑μ = nΔ and ∑μ² = nΔ(Δ + 1). Remove the smallest eigenvalue, which is zero. Each remaining eigenvalue lies between μ₂ and μmax, so (μmax − μ)(μ − μ₂) is nonnegative. Sum and expand these products using the two trace identities and the n − 1 remaining entries. Multiplication by n − 1 and rearrangement produce the bound.

[Lean proof](../../results/proofs/13d92e55531b78e29ee43cf17d2cc182ee632ee52bc3c2aab713d77a170343bb.lean#L568) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_6c16976d1304a3bdb83a

**Meaning.** The largest adjacency eigenvalues of a graph and its complement obey r(G)² + r(Gᶜ)² ≤ (n − 1)². No connectivity or regularity assumptions are needed. The empty graph is covered separately by the adopted zero spectral values.

**Proof idea.** For either nonempty graph H, its adjacency eigenvalues sum to zero and their squares sum to the degree total. Remove an entry realizing the largest eigenvalue. Cauchy–Schwarz on the other n − 1 entries gives nr(H)² ≤ (n − 1)∑degH(v). Add the inequalities for G and its complement. Their degree totals add to n(n − 1), because every vertex has complementary degrees summing to n − 1; cancel the positive n.

[Lean proof](../../results/proofs/212020d92dc5de628f7c846dbe7e67b02dbb707d52ac09457c293b633946d545.lean#L268) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_73adc8d60ed10eeee215

**Meaning.** A connected graph with n ≥ 2 has a strictly positive normalized Laplacian gap ν₂. Here the normalized matrix is obtained by multiplying L on both sides by the diagonal matrix with entries 1/√deg(v). The conclusion concerns its second-smallest eigenvalue.

**Proof idea.** Positive semidefiniteness first makes the normalized eigenvalues nonnegative. Connectedness and n ≥ 2 ensure that every degree is positive, so the diagonal scaling is invertible. A vector in the normalized kernel becomes constant after that scaling, by the description of the ordinary Laplacian kernel. If the second-smallest eigenvalue were zero, the two lowest orthonormal eigenvectors would both have this form and would be linearly dependent. Their independence excludes that possibility.

[Lean proof](../../results/proofs/234bfe14938110efdc5d4a87106d8f644af5b4d2b98fb470c6f376d5703c72a6.lean#L664) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_8381b1d261739251d279

**Meaning.** For a connected graph with n ≥ 2, put k = n − 1 and d = 2m/n. Then 2(kμmax − nd)(nd − kμ₂) ≥ 2nd(k − d) + k(Δ − δ)². The degree-range term strengthens the constraint coming from the Laplacian eigenvalue moments.

**Proof idea.** Trace computations give ∑μ = nd and ∑μ² = ∑deg(v)² + nd. After removing a zero eigenvalue, every remaining entry lies between μ₂ and μmax. Summing the nonnegative products (μmax − μ)(μ − μ₂) bounds the second moment. Separately, the maximum and minimum degree deviations show that degree variance is at least half the squared degree range. Substitute this lower bound into the moment inequality and rearrange.

[Lean proof](../../results/proofs/c07d5eda3b0afd24711d7a7d922ffb592f906d56a119503e8ed5f51fbb7b1cae.lean#L154) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_83f7fb63f03a8baa2809

**Meaning.** For a connected graph with n ≥ 2, νmax + (n − 2)ν₂ ≤ n, where νmax is the largest normalized Laplacian eigenvalue and ν₂ is the second-smallest. The result limits their combined size using only the number of vertices.

**Proof idea.** The normalized Laplacian is positive semidefinite. Each diagonal entry is zero at a zero-degree vertex and otherwise one, so its trace is at most n. Order the eigenvalues, remove the largest and smallest entries, and bound each of the n − 2 middle entries below by ν₂. The smallest entry is nonnegative. Adding these contributions bounds the displayed combination by the complete eigenvalue sum, which equals the trace.

[Lean proof](../../results/proofs/50cba2604a6ecceec42f7a591ac8465efbc55f6dae0bc228dd9b97a3ef585899.lean#L166) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_9ae0b93b805c7fc209a2

**Meaning.** For a connected, nonregular graph with n ≥ 3, let H = (Δ − d)(d − δ) and B = H + (r − d)². Then (q − 2r)B ≥ μ₂(r − d)². This compares the signless excess to adjacency irregularity while retaining both extreme-degree deviations from the average.

**Proof idea.** The unit top adjacency eigenvector has Laplacian energy at most q − 2r. The centered degree vector has squared norm at most nH, by the degree bounds. Cauchy–Schwarz against the eigenvector’s component orthogonal to constants links (r − d)² to that component’s size. The Laplacian gap bounds its energy below; combining the estimates gives the product. The zero-gap branch follows directly from nonnegativity.

[Lean proof](../../results/proofs/f7e5e7da44272a932cf07b632486aa97b4a53ffc9684d1143c8cb8ddbaf11c77.lean#L156) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_9f2fa017715afdaf1190

**Meaning.** For graphs with n ≥ 2, the largest adjacency eigenvalue satisfies r² + r ≤ 2m. This gives an upper bound stronger than using the square term alone, expressed entirely through the edge count. There is no connectivity assumption.

**Proof idea.** Choose a top eigenvector and a vertex with maximal absolute coordinate. Apply the eigenvector equation twice to express (r² + r) times that coordinate through neighbors and their neighbors. Triangle inequalities bound its magnitude by the coordinate magnitude times deg(v) plus the sum of the neighbors’ degrees. Since v is not its own neighbor, these degrees form a subset of the total degree sum, which is 2m. Cancel the positive coordinate magnitude.

[Lean proof](../../results/proofs/474abe218459f500e4b394735cc438c9a82d10b02a26f30b2d3ee8db4c4ab2f6.lean#L24) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_a9b32b4443158507d765

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, δν₂ ≤ μ₂. The normalized Laplacian gap, multiplied by minimum degree, is therefore at most the ordinary Laplacian gap. The assumptions ensure the relevant eigenspaces and positive degree scaling are available.

**Proof idea.** Multiply coordinates by √deg(v). This map preserves energy when transferring from L to its normalized matrix, and its squared norm is at least δ times the original squared norm. In the span of the two lowest ordinary Laplacian eigenvectors, choose a nonzero vector whose scaled image is orthogonal to the lowest normalized eigenvector. Its original energy is at most μ₂ times its squared norm; the normalized gap supplies the opposite estimate. Cancel the positive norm.

[Lean proof](../../results/proofs/f4b7dc95506f7d77859f672d6a0b130ba69d9ee3d7a6e270b0e4e35d3feb137e.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_ada25b6f9351360a7b0f

**Meaning.** For n ≥ 2, the average degree d is at most the largest adjacency eigenvalue r. The statement supplies a lower spectral bound from a simple count of edges and vertices; no connectedness or regularity requirement is imposed.

**Proof idea.** The target invokes the checked parent proving d ≤ r for all finite simple graphs. That parent expands the adjacency quadratic form in an orthonormal eigenbasis, replacing every eigenvalue by the largest one. On the all-ones vector, the quadratic form is the degree sum 2m and the squared norm is n. Dividing by positive n yields 2m/n ≤ r. The target’s size guard is stronger than the parent needs.

[Lean proof](../../results/proofs/5425c8dc654c020128e04abbc5d9c7d5c6c03a8659947bb90649d9d2ed0d8bf5.lean#L83) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_b0cf9d1e2a8965e241a4

**Meaning.** For a connected graph with n ≥ 2, μ₂ ≥ δν₂. Thus the ordinary Laplacian gap controls the normalized gap after multiplication by the minimum degree. The normalized matrix uses the inverse square roots of the actual vertex degrees.

**Proof idea.** The degree-square-root map preserves Laplacian energy and gives a norm increase of at least δ. Choose a vector in the span of the two lowest ordinary Laplacian eigenvectors whose image is orthogonal to the lowest normalized eigenvector. The proof first tries the lowest, zero-eigenvalue vector; if its image is not orthogonal, it subtracts a suitable multiple of that vector from the second-lowest eigenvector. Ordinary and normalized eigenbasis bounds trap its energy between the two gap expressions. Cancel its positive squared norm.

[Lean proof](../../results/proofs/e8dfb9a4b8d0011ca2849f3e9e939d7b79a8c179306607eb7735563ad951a807.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_b2848857e600ffe393f5

**Meaning.** For n ≥ 2, (n − 1)μ₂ ≤ 2m. In the formal statement μ₂ is zero for disconnected graphs, so that case follows immediately from m ≥ 0. For connected graphs, it is the second-smallest Laplacian eigenvalue.

**Proof idea.** Positive semidefiniteness and the existence of a zero eigenvalue identify the last entry of the descending Laplacian spectrum as zero. Every other entry is at least the second-smallest eigenvalue. Sum this inequality over the n − 1 entries after removing the last one. Their sum equals the full trace, because the removed entry is zero, and the trace is the degree sum 2m. This proves the bound.

[Lean proof](../../results/proofs/ab3b5cfbfd1bc7a8d4e2c406c76fd05f887ea71ddd760db42efd3cc258e282e0.lean#L259) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_b375e7fc1da184309dae

**Meaning.** For a connected regular graph with n ≥ 2 and common degree d, the normalized extremes obey d[n(νmax + ν₂ − 1) − (n − 1)νmaxν₂] ≥ n. Here d is also the average degree; connectedness ensures it is positive.

**Proof idea.** Regularity makes the normalized Laplacian L/d = I − A/d. Its trace is n and the trace of its square is n + n/d. The smallest eigenvalue is zero. Each of the other n − 1 eigenvalues lies between ν₂ and νmax, so its square plus νmaxν₂ is at most (νmax + ν₂) times the eigenvalue. Sum using the trace identities, rearrange, and multiply by positive d.

[Lean proof](../../results/proofs/588638f5e2d3702103829fa95bbad8eb7950fa2b5b01f8f4dacc4c276317f517.lean#L25) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_bd1be5306bec4c1ad48f

**Meaning.** For any regular finite simple graph, q = 2Δ. Connectedness is not required: the common degree determines the largest signless Laplacian eigenvalue even if the graph has several components. The empty case agrees with the zero convention.

**Proof idea.** If the common degree is d, then Q = dI + A and L = dI − A. On a unit Q-eigenvector with eigenvalue λ, nonnegative Laplacian energy gives 2d − λ ≥ 0, proving q ≤ 2d. The checked lower-bound parent uses the regular adjacency eigenvalue d to show that 2d belongs to Q’s spectrum. Therefore q ≥ 2d as well. Since d = Δ, the two bounds give equality.

[Lean proof](../../results/proofs/674538aa6757d17c132131da96c49c4fbd390e346ad50548da9f577c04deabbc.lean#L161) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_bde7d8e48dd145e3a003

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, (q − 2r)[8nΔ² + (Δ − δ)²] ≥ μ₂(Δ − δ)². It ties the signless excess to the ordinary Laplacian gap and the squared degree range.

**Proof idea.** Adjacency eigenvalues lie between −Δ and r. Their eigenbasis expansion on the all-ones vector bounds degree variance by n(r − d)(d + Δ). The extreme degree terms then give (Δ − δ)² ≤ 4nΔ(r − d). Combine this with the checked parent 2Δ(q − 2r) ≥ μ₂(r − d). This already gives the bound with 8nΔ²; adding the nonnegative squared-range term on the left yields the stated denominator factor.

[Lean proof](../../results/proofs/b7bdfef973c060847eaf447a3ffc606358f6031f7a1b3680fdca9cdaf4c40828.lean#L528) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_c411c8365954f60ffdad

**Meaning.** For a connected graph with n ≥ 2 and Δ ≥ 1, 4Δ²(q − 2r) ≥ μ₂(r² − d²). This replaces the linear adjacency excess above average degree by the difference of squares, with a corresponding maximum-degree factor.

**Proof idea.** Choose a unit top adjacency eigenvector x and a unit constant vector u. Let t = 1 − ⟨u,x⟩², the squared size outside the constant direction. The Laplacian gap and Q = L + 2A give μ₂t ≤ q − 2r. The adjacency lower bound −Δ gives r − d ≤ 2Δt. Since r + d ≤ 2Δ, multiplication yields r² − d² ≤ 4Δ²t. Combining the inequalities proves the result.

[Lean proof](../../results/proofs/b75453fcec64058646f7976f033bc16591127cf37c82f0deb138ebd5de4ce3b6.lean#L291) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_df1156dc814ca602e6d4

**Meaning.** Assume G is connected, n ≥ 3, and its average degree is below 1.9999999. For S = r(G) + r(Gᶜ), n(S − (n − 1))(S + 1) ≥ 3(Δ − δ)². The strict average-degree threshold is part of the linked hypothesis.

**Proof idea.** The edge-count assumptions force m = n − 1, so G is a tree and δ = 1. Quadratic-form bounds on the vectors (S + 1)1 ± 2(deg − d) give an upper bound for four times the degree variance. For n ≥ 4, integer degrees and the tree degree sum bound that variance below by three quarters of (Δ − 1)². The n = 3 case is handled separately using a complement edge and elementary spectral bounds.

[Lean proof](../../results/proofs/b07a274c52d38a5e6bec239d3056e1ad9a60f403cbf0e07f60e9c1f6ebdeb0c7.lean#L97) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_e1bd2d98ab50c3dcff7c

**Meaning.** For every finite simple graph, (n − 1)q² ≥ 4[(n − 1)d² + (Δ − d)²]. The largest signless eigenvalue must therefore reflect both the average degree and the maximum degree’s deviation from it. The empty graph is included.

**Proof idea.** Expressing the signless quadratic form as a sum of (xᵤ + xᵥ)² over edges proves Q is positive semidefinite. Its eigenvalues then lie between zero and q, so q²I − Q² is positive semidefinite. On the all-ones vector this gives 4∑deg(v)² ≤ nq². Center the degrees and apply Cauchy–Schwarz to all vertices except a maximum-degree vertex. Their deviations sum to the negative of its deviation, supplying the needed variance lower bound.

[Lean proof](../../results/proofs/92b4c41e30559b0913f28245cefc5a2cd9813394b36e03fe2d1491fb20be66b9.lean#L266) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_e23944a6e66f4e3a45c2

**Meaning.** For a connected, nonregular graph with n ≥ 3, n(Δ − r)(μ₂ + Δ − δ) ≥ μ₂(Δ − δ). This provides a quantitative relation between the gap below maximum degree and the combination of Laplacian connectivity and degree range.

**Proof idea.** On a unit top adjacency eigenvector, Δ − r equals its Laplacian energy plus weighted degree deficits. At a minimum-degree vertex the deficit contributes (Δ − δ) times the squared coordinate. Subtract the vector’s mean: its Laplacian energy stays unchanged and is bounded below by μ₂ times the centered squared norm. Cauchy–Schwarz controls the chosen centered coordinate. A sum-of-squares identity combines these facts with the unit norm to give the product inequality.

[Lean proof](../../results/proofs/7754d0f6ae11e1f28faa9b81f5fdbba14c1c6fea37269b5cd101d56b6233ace8.lean#L23) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_f360875414013a6cbad5

**Meaning.** For a connected graph with n ≥ 2, let k = n − 1. Then (kμmax − 2m)(2m − kμ₂) ≥ 2m(k − d) + k(Δ − δ)²/2. It bounds a product of the extreme Laplacian deviations using the degree range and average degree.

**Proof idea.** The trace identities give ∑μ = 2m and ∑μ² = ∑deg(v)² + 2m. Remove a zero eigenvalue and bound each remaining square by (μmax + μ₂)μ − μmaxμ₂, using its position between the two extremes. Summation yields the product bound in terms of degree variance. The maximum and minimum degree deviations contribute at least half the squared range. Substitute that estimate and rearrange.

[Lean proof](../../results/proofs/4943925458a4946c59308285520a53a214e47f563eefb05bc7d5e54204117f14.lean#L151) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## model_f507aec4f80c30fd2faa

**Meaning.** For n ≥ 2, (n − 1)(μmax − μ₂) ≥ n(Δ − δ). Here μ₂ is defined as zero when G is disconnected. The Laplacian spectral spread in this convention must therefore be large enough to account for the range of vertex degrees.

**Proof idea.** The centered vertex vector neᵥ − 1 has squared norm n(n − 1) and Laplacian energy n²deg(v). The upper eigenvalue bound gives nΔ ≤ (n − 1)μmax at a maximum-degree vertex. In a connected graph, the kernel consists of constants; the same trial vector at a minimum-degree vertex therefore gives (n − 1)μ₂ ≤ nδ. Subtract these estimates. In the disconnected case μ₂ = 0 and degree nonnegativity suffices.

[Lean proof](../../results/proofs/ad529e24626f38c867f32e5a049bbb6db8a9a99ff09ce9a1bd63a8f0dd7ba483.lean#L24) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## signless_laplacian_avg_deg_lower

**Meaning.** The largest signless Laplacian eigenvalue q is at least the average degree d. Both quantities are defined as zero for an empty graph. The statement holds for every finite simple graph and requires no connectedness or regularity assumption.

**Proof idea.** The trace of Q is the sum of vertex degrees, because its adjacency part has zero diagonal. Hence the signless eigenvalues sum to 2m. Each eigenvalue is at most q, so their sum is at most nq. When n > 0, divide this comparison by n to obtain d ≤ q. The proof treats n = 0 separately, where both sides are zero.

[Lean proof](../../results/proofs/a1876c2076724b07ecdc0705d953a27a88ebca5df56b0b75a1feed11c950ca66.lean#L222) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## signless_laplacian_spectral_plus_max_deg

**Meaning.** For every finite simple graph, q ≤ r + Δ. The largest signless Laplacian eigenvalue is bounded by the sum of the largest adjacency eigenvalue and the maximum degree. The zero conventions also cover the empty graph.

**Proof idea.** The spectral decomposition makes rI − A positive semidefinite. The diagonal matrix ΔI − D is also positive semidefinite, since each degree is at most Δ. Evaluate both inequalities on a unit eigenvector of Q = D + A. They bound its adjacency contribution by r and its degree contribution by Δ. Adding gives the bound for every signless eigenvalue, hence for their maximum.

[Lean proof](../../results/proofs/24efc4713f2abf73c2bf0d21b324c03c473fe22e578b890090fbf86396e12f8d.lean#L247) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## spectral_spread_le_two_max_degree

**Meaning.** The adjacency spectral spread s is at most 2Δ for every finite simple graph. The proof obtains this by placing the full adjacency spectrum inside the interval from −Δ to Δ. This conclusion does not require connectivity or regularity.

**Proof idea.** For each eigenvalue choose a nonzero eigenvector and a coordinate with maximal absolute value. The eigenvector equation and triangle inequality bound the eigenvalue’s absolute value by the degree at that vertex. Cancelling the positive coordinate magnitude and using the maximum-degree bound gives |λ| ≤ Δ. Consequently the largest eigenvalue is at most Δ and the smallest is at least −Δ. Subtract to bound the spread; the empty graph has spread zero.

[Lean proof](../../results/proofs/268f783629637e4cb58c9e79c9ce7a8ca8dd683dc10ad9fc87dfe9d149becb6f.lean#L285) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)

## spectral_spread_le_two_spectral_radius

**Meaning.** The adjacency spectral spread is at most twice the largest adjacency eigenvalue: s ≤ 2r. Thus the negative end of a graph’s adjacency spectrum has magnitude no larger than its positive end. The assertion holds for all finite simple graphs, including the empty graph.

**Proof idea.** Expanding a quadratic form in an adjacency eigenbasis bounds it above by r times the squared norm. For any unit eigenvector, take absolute values of its coordinates. This preserves the norm, and every edge product in the new quadratic form is at least the negative of its original product. The original eigenvalue is therefore at least −r. The smallest eigenvalue has the same lower bound, so subtracting it from r gives s ≤ 2r.

[Lean proof](../../results/proofs/36c88938110e50f4f03f2f305c182b83c191ce7d3a65aabc31c02651b3368672.lean#L345) · [Full statement and frozen assessment](../../results/all-proofs.md#spectral-bounds)
