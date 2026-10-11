# Continuous campaign rotation

This describes the implementation and historical local deployment. Run settings below describe that deployment, not an automatic start command or a public performance qualification. Its raw private run evidence is not redistributed; see [negative results](negative-results.md).

Run the seven existing graph research campaigns through one coordinator:

```sh
.venv/bin/python -u -B run_research.py --continuous --workers 16 --proof-backend codex --model gpt-6.1-sol --reasoning-effort xhigh --model-rounds 3 --model-request-timeout 1200 --model-candidates 4 --max-lean-targets 16 --output-dir research_outputs
```

Omitting `--campaign` selects the rotation. Supplying `--campaign expander_codes` (or another campaign name) restricts the coordinator to that campaign. `--all-campaigns` is the existing bounded sweep mode, rather than the continuous rotation.

The rotation covers spectral graph bounds, advanced spectral invariants, extremal coloring, independence and cliques, metric and topological graph quantities, graph energy and Estrada index, and binary adjacency-kernel codes. These are seven campaigns in graph mathematics and coding theory; this mode does not add arbitrary number theory or a general finite-field polynomial engine.

Each completed batch advances the saved campaign cursor. A restart continues from the next saved campaign; a changed campaign selection begins a new accounting period. One writer commits the shared library and checkpoint. Sixteen proof workers are a shared capacity, not sixteen workers for every campaign. The shared library allows a certified lemma from one campaign to help another.

Local generation, AI proposal context, screened proof targets and dashboard labels use the same campaign selection. Independent exploration varies mathematical statements inside that selection. Campaign counts describe completed batches and newly certified artifacts attributed to a batch, not original mathematical discoveries. Historical certificates and requests lacking campaign provenance remain unattributed.

Proposal and proof requests keep finite 1200-second limits and a 3770-second shared proof-target limit. A third proof request requires measured compiler progress. The model remains gpt-6.1-sol with xhigh effort and requested Standard service; actual service tier is unknown unless explicitly reported by the provider. Originality assessment and skeptical-challenge requests retain separate accounting. Failed attempts and missing usage remain visible.

Metric and topological research can empirically investigate diameter, radius and girth. The current trusted Lean translator explicitly rejects those quantities because their infinite cases do not have a reviewed scalar translation. Supported triangle-count and density statements can enter Lean proof search. Unsupported candidates remain visible and never become certified through a fabricated axiom. Configured campaign breadth is therefore larger than uniformly supported formal breadth.

Use a completed checkpoint boundary for live transitions. Preserve existing exact receipts, source bindings and independent replay reports; do not run multiple coordinators against `research_outputs`. The dashboard is available at http://127.0.0.1:8050/ and reports the active campaign, upcoming rotation and campaign accounting.
