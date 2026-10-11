# Contributing

Issues and pull requests are welcome. Begin with the smallest reproducible example and describe the behavior or mathematical statement being changed. Preserve refutations, timeouts, failed attempts and negative results.

For implementation changes, install `.[dev]`, run focused tests for the affected behavior, then the applicable full suite. Tests use local fixtures and the pinned Lean workspace. Keep credentials, personal request logs, downloaded papers, dependency trees and runtime checkpoints out of commits. Do not change the Lean/Mathlib pin without separately replaying the affected corpus.

For proof changes, provide the exact structured statement and complete guard, source and challenge hashes, parent dependencies, fresh compiler result and target `#print axioms` report. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. Hash validation is separate from compiler replay. An unsupported definition, an added hypothesis or a local axiom cannot establish the published target.

For a counterexample, provide vertex count, simple undirected edges, the exact conjecture/guard and recomputable invariant values. State numerical tolerances and undefined cases. Finite testing is evidence about those graphs, not a universal theorem.

For an originality claim, identify readable primary statements with their assumptions, compare the strongest applicable bounds in the accessed corpus, and check restatement, specialization and routine consequence. Keep inaccessible sources and unresolved priority visible. A model assessment or a new Lean certificate alone is insufficient. Attribute model-assisted material and verify any generated explanation independently.

Model-assisted experiments are optional and use your own credentials and allowance. Keep them bounded and separate from deterministic tests. Report actual request counts and recorded input/output usage; missing usage is unknown. Do not add cached-input or reasoning subsets twice.

Contributions intentionally submitted for inclusion are offered under Apache-2.0 unless explicitly stated otherwise. Submit only material you are entitled to contribute, retain applicable upstream notices, and cite or link literature instead of copying an unlicensed paper or dataset. See [publication scope](docs/publication.md) and [third-party notices](THIRD_PARTY_NOTICES.md).
