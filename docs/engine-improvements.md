# Proof efficiency, focused research, and measured reuse

The preserved `generative-2026-10-07` tag is the comparison baseline. The next implementation keeps the exact structured theorem renderer, genuine pinned Mathlib, independent counterexample screening, and permitted-axiom acceptance gate.

## Spend proof requests where they help

A composed candidate records the two certified inequalities that generated it. Before ordinary search, the prover checks their receipts, orientations, premises, intermediate expression and target endpoints, then constructs a direct transitivity proof. Metadata is a hint, not evidence: an invalid parent binding cannot establish a theorem.

General proof context selects a small relevant set of checked lemmas and includes the source dependencies needed to compile them. It does not inject every older theorem that shares an invariant. Accepted receipts record the context and observed direct/transitive source references. These references describe the proof text; they do not establish that a lemma was necessary for discovery or causally improved search.

A model-generated candidate that reaches the compiler time limit gets one retry of the identical bytes, with up to 30 seconds clipped to the original target deadline. The first fixed candidate also gets one such retry when its initial compiler limit is below 30 seconds; later fixed candidates do not. This recovers a useful checked-lemma attempt that can otherwise time out before model search. It can consume up to 30 seconds of the same target budget, leaving less time for subsequent search. Compiler errors still go to ordinary fallback or model repair. Timeout and retry diagnostics are retained separately. This policy never increases the target's total deadline or treats a timeout as a refutation.

Generated proof bodies are dedented as a whole before insertion, including after an optional `by` wrapper, so removing outer whitespace preserves nested Lean blocks. Real trial diagnostics exposed the previous first-line-only trimming bug. That interrupted trial is retained separately; corrected comparisons use a fresh source freeze and do not overwrite its failures or request costs.

## Use the available workers

Proof jobs contain one admitted target each. A bounded FIFO queue dispatches the next target when a worker finishes. The worker limit, global target limit, frozen batch library, deterministic parent merge, atomic checkpoint and cancellation rules remain binding. Sieve chunks remain separate. Worker occupancy records leased process-slot wall time, including startup and cleanup; it is not CPU utilization.

## Give proposals a mathematical focus

The proposal context rotates deterministically through supported mathematical families using the committed iteration. It reserves separate space for relevant receipt-validated bounds, supported unresolved targets and related counterexamples, instead of letting a large checked library crowd out open questions. Exact compatible constant bounds may be ranked by strength; this does not establish general mathematical dominance.

A bounded lookup reads declaration signatures from the pinned local Mathlib sources and retains file, line and hash provenance. It supplies search hints, not theorem certification or a novelty decision. The model is asked to explain what a target improves, useful intermediate lemmas, and sharpness or equality examples without claiming unperformed checks. The ordinary decoder, independent sieve and Lean acceptance gate still decide its outcome.

The dashboard shows the latest research focus, measured proof-worker occupancy, and observed references to earlier lemmas. Older receipts without reference accounting remain explicitly untracked.

## Compare learning under a frozen protocol

The original four-target experiment remains available as the `legacy` profile. The `focused` profile contains five known statements:

| Phase | Family | Target | Role |
|---|---|---|---|
| Training | Coloring | χ + α ≤ n + 1 | Learn a color-class/independent-set bound |
| Training | Spectral | E² ≤ 2nm | Learn the graph-energy/edge bound |
| Evaluation | Coloring | ω + α ≤ n + 1 | Predeclared composition with the baseline ω ≤ χ |
| Evaluation | Spectral | E² ≤ n²(n−1) | Transfer needing an additional simple-graph edge bound |
| Evaluation | Extremal | Triangle-free ⇒ 4m ≤ n² | Unrelated-family control |

Here E denotes graph energy and m denotes the number of edges. Training proofs enter only the learning arm's own library. Evaluation proofs never enter any library. Every repetition starts afresh from the same seven checked foundations. The fixed arm remains a separate baseline; the two model arms have identical per-target budgets. Model-arm order alternates across repetitions. A repetition is a separate stochastic trial, not a controlled model seed.

The focused budget is four fixed tactics at 10 seconds each, at most one model request at 150 seconds, and a shared 220-second target deadline including generation and compiler retries. Two repetitions admit at most 20 model requests across the entire experiment. The completed October 8 comparison predates the first-fixed-candidate retry; its measured prover source and original outcomes are preserved in the evidence archive. New experiments include that retry within the same shared deadline. All timeouts, failures and incomplete usage are retained. Complete token cost remains unknown if any request lacks usage.

```sh
python3 evaluate_generative.py prepare \
  --output-dir runs/focused_learning \
  --profile focused --repetitions 2
python3 evaluate_generative.py run --output-dir runs/focused_learning
python3 evaluate_generative.py summarize --output-dir runs/focused_learning
```

Preparation binds source, model configuration, compiler dependencies, target statements, screening and initial proof receipts. Its `prior_live_exposure` field compares exact raw ASTs and can miss mathematically equivalent forms: in the saved iteration-19 atlas, the energy training bound was already live Lean-certified with different squaring syntax and multiplication association, and the triangle-free control was equivalent to the existing Mantel empirical survivor. The coloring training bound was also already live certified. The supplemental `runs/engine_improvements/prior_exposure_audit.json` binds these checks without changing the frozen manifest. Held out means excluded from this experiment's training and registration paths, not mathematically unseen. Preparation copies only the seven baseline proofs. `run` may continue past previously completed validated arms; it refuses to overwrite an incomplete arm or selectively retry its failures. Independent experiments require fresh directories and their own frozen manifests.

Comparison reports pair the held-out outcomes by exact statement in each repetition. They retain both learning-only and frozen-only successes, report time/request differences only on jointly certified targets, and keep training costs visible. Aggregate counts are target runs, not distinct discoveries. Source references and a positive paired difference are evidence to inspect, not by themselves a general learning claim. The filesystem and model's prior knowledge are not sealed; held out means excluded from this experiment's training and proof-registration paths.
