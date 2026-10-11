# Verification and reproduction

For a first Python-only check, run the [adjacency-code example](adjacency-code-example.md); it requires no account, AI or Lean. To validate the public proof catalogue without compiling it, run `python scripts/replay_results.py --check-only --output runs/catalog-check.json` from the checkout root. Use a fresh report path on repeat. Kernel replay additionally requires the pinned Lean workspace; the public [README](../README.md) provides the short setup and full-corpus replay command.

Run the full test suite after installing Python dependencies and preparing the pinned Lean workspace:

```sh
python -B -m pytest -q
```

Tests generate their own temporary graphs, proof targets, export fixtures, checkpoints, and failure cases. They do not require historical proof artifacts or a fake Mathlib workspace. End-to-end tests derive the checkout path from their own location so that a fresh copy cannot silently exercise the previous project.

The retained `seed/counterexamples.json` is an explicit source-controlled mathematical fixture. Fresh output directories may start with its 23 validated refutations. Those examples carry no previous run counters, campaign history, or fertility state.

## Fresh checkout and foundation replay

Clone the frozen committed checkout into a separate directory. Replace the source path below with that checkout, or with the selected repository URL after publication:

```sh
git clone https://github.com/steph4n-gh/math-foundry.git math-foundry-replay
cd math-foundry-replay
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e '.[dev]'
export PATH="$HOME/.elan/bin:$PATH"
test -x "$HOME/.elan/bin/elan"
elan toolchain install leanprover/lean4:v4.34.1
cd certified_lean
lake exe cache get
lake env lean --version
```

Run on macOS or Linux. The current toolchain setup expects Elan at `~/.elan/bin/elan`. Keep the editable checkout: the separate pinned workspace and mathematical seed are required alongside the Python modules.

Replay the seven preserved proof sources in the prepared workspace. Skip the companion challenge files, which intentionally contain unproved target placeholders:

```sh
# Still in certified_lean:
for proof in ../library/proofs/*.lean; do
  case "$proof" in *.challenge.lean) continue ;; esac
  lake env lean "$proof" || exit 1
done
cd ..
```

The supplemental generated corpus has four additional known proof sources with writeups and replay provenance. Replay those exact sources as well when qualifying the complete preserved corpus:

```sh
for proof in library/generated/proofs/*.lean; do
  case "$proof" in *.challenge.lean) continue ;; esac
  (cd certified_lean && lake env lean "../$proof") || exit 1
done
```

Those commands check compilation. To audit the exact target's transitive axioms for all eleven preserved sources, run this from the checkout root:

```sh
python -B - <<'PY'
import hashlib, json, subprocess, tempfile
from pathlib import Path
from autonomous_math.prover.lean_prover import _target_axiom_report

root = Path.cwd()
allowed = {"propext", "Classical.choice", "Quot.sound"}
with tempfile.TemporaryDirectory(prefix="math-foundry-replay-") as directory:
    for catalog in ("library/catalog.json", "library/generated/catalog.json"):
        for item in json.loads((root / catalog).read_text())["theorems"]:
            source = (root / item["source"]).read_bytes()
            assert hashlib.sha256(source).hexdigest() == item["source_sha256"]
            target = item.get("theorem_name", item["id"])
            replay = Path(directory) / "Replay.lean"
            replay.write_text(source.decode() + f"\n#print axioms {target}\n")
            result = subprocess.run(
                [str(Path.home() / ".elan/bin/lake"), "env", "lean", str(replay)],
                cwd=root / "certified_lean", capture_output=True, text=True, timeout=60)
            axioms, error = _target_axiom_report(result.stdout, target)
            assert result.returncode == 0 and not error and set(axioms) <= allowed, (
                target, result.stdout, result.stderr, error)
            print(target, axioms)
PY
```

This fresh replay does not automatically register machine-bound runtime receipts. The seven-proof bootstrap remains separate from the supplemental corpus and the frozen comparison's seven-proof starting library.

Compiling preserved sources does not regenerate their machine-specific receipts. Rebuild the seven foundations using the actual runner in a new output directory:

```sh
# Choose another name if this output directory already exists.
test ! -e runs/foundation-replay
python -B run_research.py --continuous --max-iterations 2 \
  --limit-per-pair 3 --limit-per-triad 3 --max-lean-targets 6 \
  --proof-backend none --model-candidates 0 \
  --timeout-sec 300 --output-dir runs/foundation-replay

python -B dashboard.py --output-dir runs/foundation-replay --port 8050
```

This two-cycle recipe has been qualified to rebuild the seven foundations. The runner validates the retained boundary examples, generates checked foundational targets and compositions, and writes fresh source-bound receipts with the permitted-axiom check. The dashboard's Lean-certified library shows the resulting records; a stopped run or empirical survivor is not evidence that all seven checks completed. Use a different port when 8050 is occupied. Machine speed and global deadlines can limit completion; resume the same output directory if a batch was interrupted.

To evaluate proof transfer from those freshly checked common bounds, use `--seed-dir runs/foundation-replay` with `evaluate_self_improvement.py` and a fresh experiment destination. The evaluator selects its common three-proof starting library automatically.

## Proof evidence

A valid receipt identifies the exact theorem and structured AST, records the real Lean version and timings, and binds the proof, challenge, compiler binary, and dependency contents by hash. Replaying a proof means running its actual source against the pinned workspace and inspecting `#print axioms` for the target declaration. Content verification of a saved receipt is not a fresh kernel replay.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. `sorryAx`, custom axioms, unsupported guards, and unsupported definitions cannot promote a result. After moving artifacts to a new directory or machine, restore and verify their exact sources and dependencies and produce current path-consistent receipts before reseeding the authoritative atlas.

## Model search and parallel execution

Deterministic tests select `proof_backend="none"` and do not consume model requests. A real generative qualification must retain the authenticated CLI request, returned proof body, actual compiler diagnostics, repair response when needed, checked receipt, and an independent kernel replay. A mocked model response tests orchestration only. Known results are appropriate integration targets, but their certification does not establish new mathematical priority.

Parallel qualification compares a common candidate set and committed library with one and multiple workers. Compare structured outcomes, graph witnesses, proof targets, global budgets, and the resumed random state rather than wall-clock fields or artifact paths. Verify that a rejected delta and an interrupted round cannot alter the last committed atlas. Model and Lean subprocesses use bounded deadlines and process cleanup; interrupted work remains diagnostic output, not reusable proof evidence.

## Refutations and coverage

Counterexamples retain vertex count, edges, adjacency matrix, guard, and refutation witness. Certificate replay reconstructs the graph and recomputes the relation. The current spectral comparisons use floating-point arithmetic and tolerance; they are numerical refutations, not rigorous interval enclosures.

Model proof search can return a proof body, a graph counterexample, or an explicit unknown outcome. A counterexample contains only a vertex count and simple undirected edges, bounded to 64 vertices. The host checks the graph, the exact candidate and its premise, and finite evaluated values before constructing a certificate. The checkpoint owner independently replays that certificate before recording `REFUTED`; it creates no Lean receipt and adds no lemma. Invalid witnesses receive bounded repair feedback, while an explicit unknown ends that search without an identical second request. Model explanations alone cannot establish a refutation.

Exact coloring, clique and independence checks use per-solver budgets; graphs above 32 vertices requiring those invariants are accepted only when the existing exact shortcuts apply. Solver timeouts and unsupported cases remain unresolved, never refutations. Serialized model certificates use this same bounded host check during later replay. An infinite value is rejected on this model-witness path, even where legacy catalog screening supports extended-value semantics.

Committed graph witnesses enter the next round's existing counterexample catalog. Refuted targets are excluded from proof scheduling on resume. The challenger also includes 22 disjoint edges and 16 disjoint four-cycles, which expose affine spectral/edge fits that survived the previous small-graph suite. Changing its revision rechecks saved survivors before further learning; a contradiction of a certified theorem aborts the batch for investigation.

Catalog and challenger results distinguish visited graphs from applicable, defined comparisons. No applicable comparison is inconclusive. Infinite girth and disconnected diameter remain valid extended values; undefined arithmetic is counted and excluded. Surviving a finite suite does not prove a universal relation.

## Frozen generative comparison

The original runtime `research_outputs` directory is excluded from the public snapshot. First complete the foundation-replay recipe above to create current receipts in `runs/foundation-replay`. These evaluator recipes consume that locally generated seed, not an archival atlas supplied by the release. The generative model arms require your own authenticated Codex CLI account.

Prepare a fresh destination using an atlas containing valid receipts for exactly the seven catalog foundations. The evaluator selects those foundations even when the live atlas contains additional proofs. Run the arms sequentially against the same frozen sources and model configuration:

```sh
python -B evaluate_generative.py prepare \
  --seed-dir runs/foundation-replay --output-dir runs/generative-comparison
python -B evaluate_generative.py run-arm \
  --output-dir runs/generative-comparison --arm fixed
python -B evaluate_generative.py run-arm \
  --output-dir runs/generative-comparison --arm model_frozen
python -B evaluate_generative.py run-arm \
  --output-dir runs/generative-comparison --arm model_learning
python -B evaluate_generative.py summarize --output-dir runs/generative-comparison
```

The targets are known greedy coloring and spectral-energy bounds for training, an independent-set capacity bound and a predeclared energy/degree composition for evaluation. Each target has a 360-second ceiling and four fixed attempts of at most ten seconds. Model arms additionally allow two requests of at most 150 seconds each within that same ceiling; each generated body's compiler invocation also has a ten-second limit. Retain negative attempts, compiler diagnostics, raw request traces, missing usage, the separate false control, and independent replays of accepted sources. Missing usage is unknown rather than zero; cached and reasoning counts are already included in input and output totals.

Only successful training proofs from the current learning arm can expand its library. No evaluation proof can affect a later evaluation target. Models can inspect pinned Mathlib, and this small known-result comparison is not a sealed novel-premise benchmark. Inspect actual tool-read traces before attributing a result to library learning. One stochastic trial per arm cannot establish a general improvement rate.

## Controlled proof transfer

Use the locally rebuilt foundation receipts described above. A fresh public checkout does not include the historical `research_outputs` seed.

```sh
python -B evaluate_self_improvement.py \
  --seed-dir runs/foundation-replay \
  --output-dir runs/proof-transfer --trials 2 \
  --max-attempts 4 --timeout-per-attempt 10 --budget-per-arm 240
```

The evaluator selects only the common three bounds `χ ≤ n`, `ω ≤ χ`, and `ω ≤ n` by their structured statements and valid receipts. Other live-library results, including the training answers, are excluded. A separate three-proof snapshot can also be supplied. Both arms use the same initial checked library and train/test statements. Only the learning arm retains new training proofs. Held-out proofs cannot train later test targets. A manifest freezes source hashes before execution; source changes invalidate the comparison. Retain failures, budgets, actual timings, reversed arm order, and both arms' receipts. The selected portfolio measures known-bound proof transfer, not general research discovery.

## Clique correctness and performance

```sh
python -B -m spectral_pruning.certified_bounds_benchmark \
  --oracle-only --output-dir runs/clique-oracle

python -B -m spectral_pruning.certified_bounds_benchmark \
  --benchmark-only \
  --receipt /path/to/clique-degree-bound.receipt.json \
  --receipt /path/to/clique-edge-bound.receipt.json \
  --output-dir runs/clique-comparison --timeout 2 --trials 3 \
  --load-context 'Describe the actual concurrent workload or quiet window'
```

Oracle qualification checks all graph-atlas isomorphism representatives through order seven, every candidate vertex subset, every prune budget, and all returned clique witnesses. The paired benchmark uses authentic hashed inputs, identical search and ordering, alternating enabled/disabled order, equal budgets, and repeated timings. Completed pairs alone enter speedup summaries. Retain unfinished searches and slowdowns. The degree and edge bound switch defaults off following its negative performance qualification.

These checks establish the behavior and mathematical statements exercised. They do not guarantee flawless operation, numerical rigor for unsupported invariants, novel discoveries, or speedups on untested input distributions.
