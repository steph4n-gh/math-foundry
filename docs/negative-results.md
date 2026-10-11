# Negative results and experimental limits

The project has produced replayable proofs of known mathematics and routine consequences. Its bounded experiments have **not established a general advantage in proof yield, learning or original discovery**. The following historical results remain negative or inconclusive. They are not superseded by a larger count of certified artifacts.

These summaries come from retained local experiment records. Raw model requests, traces and failed-run archives remain in the private research archive and are excluded from this public snapshot. The published proof corpus is therefore not a complete reproduction dataset for those model experiments. Counts below refer to their fixed historical target sets, not the current public corpus.

## Learning and proof generation

An initial four-target portfolio used two training targets, two held-out targets and seven starting foundations. The fixed engine, frozen model arm and learning model arm proved **0/4, 2/4 and 1/4** respectively; on the two held-out targets they proved **0/2, 1/2 and 0/2**. These were known statements, and one stochastic comparison does not establish causality.

The frozen arm made six model requests and lacked usage for three. Its recorded input-plus-output subtotal was **389,120 tokens**. The learning arm made seven requests and lacked usage for one, with **845,880 recorded tokens**. Complete costs are unknown. Across the thirteen requests, six compiler attempts ended with exit 124 and empty output, and four model requests timed out. Those outcomes do not disprove the mathematical targets.

A later corrected focused comparison proved **2/6 held-out targets in each arm** and **5/10 targets overall in each arm**. One success was learning-only and one frozen-only. It made nineteen requests, with five missing usage records and **1,932,862 recorded tokens** in total; complete cost is unknown. Training statements were already certified locally, and a Mantel control had appeared as an earlier empirical survivor. “Held out” did not mean mathematically unseen. The measured comparison established no net learning benefit.

One interrupted comparison was invalidated by a host indentation bug that malformed submitted proof bodies. Compiler controls also showed that some apparent rejections were timeouts. These implementation and resource failures are retained as such, rather than counted as mathematical failure or improvement.

## Literature guidance

A fixed-input, proposal-only pair produced **one nonduplicate finite survivor per arm**, with no proof requests. The earlier-context arm used **35,235 tokens**, and the literature-guided arm **43,226**, with usage available for both. A finite survivor is not a proof, and this single pair showed no generation-yield advantage.

An earlier pair certified the same predeclared target in both arms. Recorded costs were **1,151,859 tokens** for the current arm and **1,701,493** for the guided arm. The requests accessed additional live atlas/source or web context, so the experiment did not isolate the effect of cached guidance. The fixed proof prompts also had no direct literature treatment. These are per-arm operational outcomes and costs, not evidence of a proof speedup.

## Proof enhancements

A two-target comparison proved **1/2 targets in the baseline arm and 0/2 in the enhanced arm**. The enhanced arm proposed two auxiliary lemmas that remained unproved. The baseline used three requests and **826,423 tokens**; the enhanced arm used two and **445,635**, with complete recorded usage. Lower token use accompanied lower success. The targets had been attempted previously, and source files changed after imports in the enhanced workspace, limiting attribution. No proof-yield benefit was established.

## Spectral integration and tool controls

The first native spectral integration pair failed because of its provider schema; usage was unknown. A repaired pair produced six finite survivors but failed its predeclared zero-tool boundary, with **293,670 recorded tokens**. Successful generation did not turn that protocol failure into a passing experiment.

A separate pair was authorized under a new boundary declared before requests: only exact empty built-in resource inventories were allowed. It passed that narrower integration boundary, produced **eight screened admissions across the two arms**, consumed **391,602 recorded tokens**, and made **zero proof requests**. Cross-arm overlap prevents treating eight admissions as eight distinct mathematical ideas. Empty inventory calls were observed; hard removal of every tool was not established. This demonstrated integration, not improved proof yield or originality, and preserved the prior failures.

## Reading the numbers

Token figures are recorded input plus output totals or explicitly marked partial subtotals. Cached and reasoning-token subsets are not added a second time. They are not dollar charges or subscription-billing measurements. Missing usage remains unknown rather than zero.

A timeout, an unproved helper, a source-binding failure and an incorrect statement are different outcomes. Finite graph checks can refute candidates, but cannot certify universality. Kernel replay can validate a precise formal statement, but cannot establish priority. Current catalogue assessment states and the [investigated originality comparisons](../results/originality-notes.md) must be read with those distinctions intact.
