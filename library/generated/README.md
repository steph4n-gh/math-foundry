# Supplemental generated proof corpus

These four model-synthesized proofs were accepted by the Lean kernel and independently replayed against Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. They are **known mathematics**, retained as concrete evidence of constructive proof generation, guarded translation, and reuse of certified results. They are not mathematical discoveries.

[catalog.json](catalog.json) records the exact conjecture ASTs, source and challenge SHA-256 hashes, accepted axioms, and model provenance. All four used the configured `gpt-6-astra` model with `xhigh` reasoning. The coloring-degree proof required a second model round after the first source was rejected; the other three were accepted in their first model round. Each source is copied byte for byte, including any embedded checked helper theorems.

This directory supplements the frozen seven-proof portfolio in `library/catalog.json` and `library/proofs/`; it does not alter that portfolio or automatically register proofs in a research run. Runtime receipts bind local paths, workspace state, and the Lean binary, so they remain separate. After cloning, follow [verification setup](../../docs/verification.md) and freshly replay the retained proof source through the verifier before creating a trusted runtime receipt. Historical replay results recorded in the catalog do not substitute for that step. The matching `.challenge.lean` files are statement templates with an intentional `sorry`, not checked proofs. Accepted proof sources depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Chromatic number at most maximum degree plus one (χ ≤ Δ + 1)

[Read the plain-English explanation](../../docs/proofs/supplemental.md#generative_chromatic_degree_pilot)

Every finite simple graph can be colored with at most its maximum degree plus one colors. The proof constructs a coloring by induction on finite vertex sets: at most Delta neighbor colors are forbidden, so one of Delta + 1 colors remains available. This classical guarantee is useful when reasoning about coloring and scheduling constraints. In this corpus it also demonstrates model-generated constructive proof synthesis and a successful repair after Lean rejected the first proposal; it is known mathematics, not a new discovery.

[Exact proof source](proofs/f2e50fbabed138112f1e02070ee1a304c5f3f3015b3e059b0456f9216b824fc1.lean#L5) · [Exact challenge](proofs/f2e50fbabed138112f1e02070ee1a304c5f3f3015b3e059b0456f9216b824fc1.challenge.lean)

## Bipartite graphs use at most two colors (bipartite ⇒ χ ≤ 2)

[Read the plain-English explanation](../../docs/proofs/supplemental.md#pilot_bipartite_two_colors)

A bipartite graph needs at most two colors: its two vertex classes supply a proper coloring. The recorded bipartite guard is translated to Mathlib's G.Colorable 2, and the checked proof converts that colorability witness into the stated chromatic-number bound. This elementary result is useful for recognizing tractable coloring cases and, here, verifies that a structural guard survives translation into the formal theorem. It is known mathematics, not a new discovery.

[Exact proof source](proofs/3111cf7351031dcd8aa1a48d1bdae9cc10dc1c4d24f96975d6336708bbe900e0.lean#L20) · [Exact challenge](proofs/3111cf7351031dcd8aa1a48d1bdae9cc10dc1c4d24f96975d6336708bbe900e0.challenge.lean)

## Independence number at most graph order (α ≤ n)

[Read the plain-English explanation](../../docs/proofs/supplemental.md#pilot_independence_le_order)

An independent set cannot contain more vertices than the graph itself, so the independence number is at most the graph order. The checked source represents independence as clique number in the complement graph and applies the existing certified clique-number bound to that complement. The bound is elementary; its value here is demonstrating correct complement semantics and reuse of a checked theorem on a transformed graph, rather than another arithmetic combination of facts about the same graph. It is known mathematics, not a new discovery.

[Exact proof source](proofs/e3febcf8bf907c8a0294447029cbcea16e0db1e3a2ef8b5a5a4da59fbea37af8.lean#L94) · [Exact challenge](proofs/e3febcf8bf907c8a0294447029cbcea16e0db1e3a2ef8b5a5a4da59fbea37af8.challenge.lean)

## Chromatic number constrained by edge count (χ(χ − 1) ≤ 2m)

[Read the plain-English explanation](../../docs/proofs/supplemental.md#model_e679ce9c7fa60e2c7bfd)

This known graph-coloring bound says that a finite graph requiring k colors must contain at least k(k−1)/2 edges. The checked proof forms the graph on the color classes of an optimal coloring, shows that graph is complete, and maps the original directed edges onto its directed edges. It then applies the previously checked clique–edge bound to that color graph. The result gives an edge-count upper bound on chromatic number and demonstrates substantive reuse: a clique theorem becomes a coloring theorem through a new graph construction. This is a verified proof of a known result, with no novelty or solver-speed claim.

This proof came from the normal live research loop and was preserved after the parent committed iteration 16 and an independent kernel replay passed. Its coloring quotient argument applies `clique_edges_density_bound` to a new graph; the preceding greedy coloring theorem is not used in the target proof body.

[Exact proof source](proofs/5062e8b1c67dc97af3397ffffc6edb836e619942d83f240398f014cff6f3f831.lean#L145) · [Exact challenge](proofs/5062e8b1c67dc97af3397ffffc6edb836e619942d83f240398f014cff6f3f831.challenge.lean)
