# Understand a proof, then reuse it

Every one of the [341 frozen proof artifacts](../../results/all-proofs.md) has a
plain-English explanation. Each entry describes **what the statement means** and
**how its actual Lean proof works**, then links directly to the target declaration.
The [four supplemental generated sources](supplemental.md) have explanations too;
they remain a separate historical corpus, not extra library exports.

Start with the [five longer walkthroughs](../proof-walkthroughs.md) if you are new
to graph coloring, spectral bounds or binary adjacency codes. For a specific
result, use the **Meaning & proof idea** link in its proof-index row.

## Choose a subject

| Subject | Explanations | Indexed artifacts |
| --- | --- | --- |
| Coloring, cliques and independence | [Read](coloring.md) | 72 |
| Spectral bounds | [Part 1](spectral-1.md) · [Part 2](spectral-2.md) | 91 |
| Energy and Estrada index | [Read](energy.md) | 49 |
| Adjacency codes and unique neighbors | [Part 1](adjacency-codes-1.md) · [Part 2](adjacency-codes-2.md) · [Part 3](adjacency-codes-3.md) | 107 |
| Degree, density and triangles | [Read](degree.md) | 22 |

The parts follow the index order. Subjects describe the quantities involved,
not the campaign that generated a proof. An explanation can cover a combination
of subjects; the artifact appears once in the main index.

## Try a generated argument

- [How needing many colors forces many edges](coloring.md#model_e679ce9c7fa60e2c7bfd): turn an optimal coloring into a complete graph on its color classes, then count edges.
- [How edges outside a spanning tree limit triangles](degree.md#model_a1f6745517cbad451a6c): every triangle must use one of those extra edges, each of which can support only so many triangles.
- [How degree variation enters a triangle bound](degree.md#model_8371fb8fc2bcba3921ce): isolate a maximum-degree vertex and account for the remaining degrees with Cauchy–Schwarz.
- [How irregularity affects a signless spectral bound](spectral-2.md#model_00c10ac49d00184b94a2): combine a Laplacian gap estimate with a vertex’s degree deficit.

These are reading suggestions, not originality endorsements. The index keeps
each artifact’s frozen assessment; expert review is pending and no original
mathematical result is established by this collection.

## Read the notation and premises carefully

All targets concern finite simple undirected graphs. **n** counts vertices,
**m** edges, **Δ** is maximum degree and **δ** minimum degree. Subject pages define
their other quantities and special conventions. Density is written **p** here;
it is the fraction of available vertex pairs occupied by edges, distinct from
an adjacency eigenvalue. The human index disambiguates density and keeps
spectral sums grouped, while the frozen JSON catalog retains its original
historical display strings.

Some generated statements have connectedness, regularity, bipartiteness,
nonzero-code or numerical premises. Keep those when using the theorem. The
translator applies an exact 10⁻⁷ tolerance to numerical guards. The index shows
the enforced rational threshold, or an equivalent integer comparison, and the
explanations preserve substantive restrictions. The Lean declaration gives the
exact formal statement.

A retained source often contains several checked prerequisites. That does not
mean its target uses every theorem in the file. The explanations identify the
argument actually used, including short rearrangements, discarded nonnegative
terms and applications of a parent theorem to a transformed graph.

These explanations are informal reading aids; they are not extra assumptions,
proof certificates or mathematical priority reviews. For formal reuse, follow
[the import guide](../using-proofs.md) and [practical examples](../lean-examples.md).
