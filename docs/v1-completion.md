# V1 completion and release qualification

This is an unfinished historical gate plan. The current public snapshot is a research preview. Its prior 24-hour qualification was cancelled and remains paused; publication does not claim this contract has passed. See [publication scope](publication.md).

This release closes the loop from checked results to mathematical evidence and
back to conjecture generation. It does not promise original mathematics or
exhaustive publication-priority review.

## Scope and acceptance

1. **Source-backed review:** bounded retrieval of relevant primary theorem text
   and pinned Mathlib declarations. Every quote identifies its source, location,
   and content hash. Missing or unreadable evidence remains explicit. Titles and
   abstracts alone cannot support a contribution claim.
2. **Completed comparisons:** statements, definitions, complete premises, and
   edge cases remain distinct. Known results, routine consequences, unresolved
   comparisons, and provisional possible extensions are inspectable. AI cannot
   confer expert endorsement or change Lean certification.
3. **Feedback into generation:** completed, current, source-bound reviews enter
   the existing proposal context. Evidence can guide the next question; it cannot
   certify a statement, fabricate a refutation, or permanently blacklist a target.
4. **Measured evaluation:** two paired frozen/review-informed trials, reversed
   execution order, identical model/effort and bounded request/proof allowances.
   Preserve failures, missing usage, and negative results. Accepted proofs receive
   independent kernel replay. Evaluation outputs do not train subsequent arms.
5. **Reproducible release:** complete research packets, clean-clone installation,
   real-source/model/Lean integration, failure and restart checks, then an actual
   24-hour unattended run on the frozen release candidate.

## Evidence locations

During implementation, isolated artifacts live under `runs/v1_qualification/`:

- `seed/`: immutable starting atlas and review sidecar; original proof receipts
  remain at their validated locations.
- `source_review/`: source preparation and real review qualification.
- `packets/`: exported proof and contribution packets.
- The paired evaluation, fresh-install checks, test results, and independent
  proof replays have their own immutable subdirectories and manifests.

Freeze the desired model and effort when preparing the paired experiment; every arm reuses those exact overrides:

```sh
python -B evaluate_review_feedback.py prepare --seed-dir runs/v1_qualification/seed \
  --review-dir runs/v1_qualification/source_review --output-dir runs/v1_qualification/paired \
  --model gpt-6.1-sol --reasoning-effort xhigh
```

Preparation requires current completed source-backed reviews for both tested families. Run the arms in the manifest's order; do not regenerate the seed or reviews between arms.

The deployed release records these artifacts under its own `runs/` directory.
Only portable reports, selected source excerpts, exact theorem statements, and
replayable proof sources belong in source control. Private runtime logs and
machine-specific source caches remain outside the publication snapshot.

## Unattended qualification

After all other checks pass and the release candidate is deployed, run:

```sh
python -B qualify_release.py --research-dir research_outputs \
  --output-dir runs/v1-soak --hours 24 --interval-sec 60
```

The observer writes a manifest, timestamped samples, and `status.json`. It does
not modify the research atlas or control the runner. A successful result requires
the full elapsed period, continuous observations, healthy research/review
heartbeats, an unchanged tracked source revision, continued checkpoint progress,
and current valid proof receipts. The research model and effort are recorded in the manifest and must stay fixed. A persistent AI backlog must complete a source-validated review within the 4,500-second retry/request allowance; heartbeats or repeated failures do not count as progress. A source change, missing observation window,
stopped process, or failed check fails the qualification; starting another attempt
requires a new output directory. Model unknowns, properly rejected model answers,
and bounded retries are retained research outcomes rather than false successes.

Until `status.json` reports `passed`, the release remains a candidate. A shorter
smoke run cannot satisfy the 24-hour gate. Final release evidence must identify
the tested source revision, actual times, all measured limitations, and the
paired evaluation outcome even when it shows no advantage.

## Publication boundary

Prepare a clean source snapshot and check it for secrets and runtime artifacts
before GitHub publication. Publishing, external expert contact, and choosing an
open-source license are separate actions. Existing copyright and license terms
for cited papers remain in force; export bounded excerpts and source references,
not an unrestricted paper mirror.
