# Binary adjacency codes and unique neighbors

The `expander_codes` campaign studies a specific graph-derived binary code. For a finite simple undirected graph `G` with `n` vertices, make a variable copy and a check copy of its vertex set. An edge of the original graph gives the corresponding incidences between those copies. The check matrix is the square adjacency matrix `A(G)` over `GF(2)`, and the code is `C(G) = ker A(G)`. Codewords are binary vertex vectors whose adjacent entries sum to zero at every check.

| Quantity | Exact meaning |
| --- | --- |
| `parity_code_dimension` (`k₂`) | Dimension of `ker A(G)` over `GF(2)`, computed by binary rank and nullity. Real matrix nullity is a different quantity. |
| `parity_code_distance` (`d₂`) | Minimum Hamming weight of a nonzero codeword. The zero code uses the finite sentinel `n+1`. |
| `unique_neighbor_radius` (`u`) | Largest `k ≤ n` such that every nonempty variable set of size at most `k` has a check adjacent to exactly one member. Equivalently, minimum nonempty stopping-set size minus one; no stopping set gives `u=n`. |

A nonzero codeword support cannot have a unique neighboring check: that check would have odd parity. This yields the familiar bridge `u+1 ≤ d₂`. The other initial targets are `k₂ ≤ n`, `u ≥ 0`, and `d₂ ≤ n` under the explicit premise `k₂ ≥ 1`. Dropping that premise is false for the zero code. These are known foundational mechanisms for the campaign; their usefulness here is exact, reusable formal statements, rather than a claim of mathematical discovery.

The existing catalog contains nonzero codes on even-degree regular graphs, including `C₄`, `C₆`, and `K₅`. For example, `C₄` has dimension `2`, distance `2`, and unique-neighbor radius `1`; `K₂` has dimension `0` and sentinel distance `3`. The dashboard reports positive-dimension and zero-code sample counts separately, so a vacuous distance cannot be mistaken for a useful coding construction.

The numerical evaluator is exact only for `n ≤ 16`. It enumerates binary supports and uses GF(2) elimination; larger graphs raise a domain error and are counted as undefined, including when a code-valued guard cannot be evaluated. A mixed catalog can still produce an empirical survivor from its defined samples. That status is not a universal proof. The trusted Lean definitions have all-finite-graph scope and do not inherit the numerical order limit; certification still requires the actual kernel and axiom checks.

The numerical `peel_erasures` function performs check-based erasure peeling and retains its steps. It returns `DECODED`, `BLOCKED`, or `INCONSISTENT`; a blocked decoder does not imply that no completion exists. Unique-neighbor structure supplies a mathematical route to recovery bounds. This campaign does not establish cryptographic security, asymptotic goodness, general error correction, or a performance advantage.

## Running the focus

From a prepared checkout, use a dedicated output directory for an independent campaign:

```sh
python -B run_research.py --continuous --campaign expander_codes \
  --workers 8 --max-lean-targets 16 --model gpt-6-astra --reasoning-effort xhigh \
  --model-rounds 2 --model-request-timeout 150 --model-candidates 2 \
  --output-dir expander_research_outputs

python -B dashboard.py --output-dir expander_research_outputs --port 8051
```

Add `--max-iterations 1 --timeout-sec 900` for a bounded run. Eight workers can issue eight model requests concurrently. Choose a smaller worker and target budget when desired. `--proof-backend none --model-candidates 0` removes model requests; `--max-lean-targets 0` additionally removes Lean attempts.

An explicit continuous `--campaign` selects that campaign on every round. Without the flag, continuous research retains the all-campaign rotation. The code campaign restricts generated candidates, proposals, adaptive pairs, and proof admission to statements involving a code quantity or unique-neighbor radius. Existing unrelated atlas records and the checked proof context remain available. To resume, keep the same output directory; an unfinished round still rolls back to its last complete checkpoint.

`--model` and `--reasoning-effort` select the research backend for a new invocation. Omitting either preserves that setting from the authenticated CLI configuration. Settings take effect on restart, and the dashboard shows the selected model and effort separately from the saved worker configuration. No dashboard button mutates the running process.

## Relation to expander and Tanner codes

[Sipser and Spielman's expander-code work](https://www.cs.yale.edu/homes/spielman/Research/expanders.html) establishes asymptotically good code families and efficient decoding for its particular constructions. The [Cheng–Ouyang–Shangguan–Shen unique-neighbor Tanner-code study](https://arxiv.org/abs/2312.16087) uses a bipartite graph and an inner code, and connects unique neighbors to code distance and decoding guarantees. Those are broader constructions and results. Our square-adjacency kernel is a restricted graph-derived instance; those literature claims are not automatic properties of every graph in this campaign.
