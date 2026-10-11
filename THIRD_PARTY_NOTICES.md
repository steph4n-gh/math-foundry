# Third-party software, literature and data

The [Apache-2.0 project license](LICENSE) covers original Math Foundry code, documentation and newly authored proof scripts. It does not change upstream terms. This source snapshot does not bundle Python environments, Lean binaries, Mathlib/dependency trees or downloaded papers.

## Formal dependencies

Proof replay uses Lean **4.34.1** and Mathlib commit **d13f23b723b8a846827a245b89c10fc7d3f11612**. The exact additional Lean package revisions are in [certified_lean/lake-manifest.json](certified_lean/lake-manifest.json).

| Component | Observed source license | Upstream |
| --- | --- | --- |
| Lean 4 | Apache-2.0 | [License at the pinned release](https://github.com/leanprover/lean4/blob/v4.34.1/LICENSE) |
| Mathlib | Apache-2.0 | [License at the pinned commit](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/LICENSE) |
| Batteries, Aesop, Qq, ProofWidgets, importGraph, LeanSearchClient, Plausible | Apache-2.0 | Package URLs and exact revisions in the manifest |
| Lean4 CLI library (`Cli`) | MIT | [License at the pinned commit](https://github.com/leanprover/lean4-cli/blob/e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204/LICENSE) |

These libraries supply imported definitions, results and tactics. Their authors retain credit for that work. Lean binary distributions and compiled dependencies also carry third-party notices, including native runtime libraries; retain the licenses supplied with any binaries you redistribute. A binary bundle needs its own notice review, beyond this source-only snapshot.

## Python and browser dependencies

The dependency list is in [pyproject.toml](pyproject.toml). The following licenses were observed in the audited upstream packages; an installation may resolve different versions, whose own license files remain authoritative.

| Component | Observed license | Project |
| --- | --- | --- |
| NetworkX | BSD-3-Clause | [NetworkX license](https://github.com/networkx/networkx/blob/main/LICENSE.txt) |
| NumPy | BSD-3-Clause | [NumPy](https://github.com/numpy/numpy) |
| SciPy | BSD-3-Clause, with additional bundled-library terms | [SciPy](https://github.com/scipy/scipy) |
| pandas | BSD-3-Clause | [pandas](https://github.com/pandas-dev/pandas) |
| SymPy | BSD-3-Clause | [SymPy](https://github.com/sympy/sympy) |
| Jinja2 | BSD-3-Clause | [Jinja](https://github.com/pallets/jinja) |
| pypdf | BSD-3-Clause | [pypdf](https://github.com/py-pdf/pypdf) |
| Pydantic | MIT | [Pydantic](https://github.com/pydantic/pydantic) |
| Z3 | MIT | [Z3](https://github.com/Z3Prover/z3) |
| pytest / pytest-cov / coverage.py, optional development tools | MIT / MIT / Apache-2.0 | [pytest](https://github.com/pytest-dev/pytest), [pytest-cov](https://github.com/pytest-dev/pytest-cov), [coverage.py](https://github.com/nedbat/coveragepy) |
| Plotly.js 2.35.2, loaded by the optional dashboard from its CDN | MIT | [Versioned license](https://github.com/plotly/plotly.js/blob/v2.35.2/LICENSE) |

NetworkX supplies the small graph atlas used by some finite checks. Its data and algorithms are upstream resources, not newly discovered graphs attributed to this project. SciPy and other binary wheels can include additional native libraries with separate license and notice requirements. None of those wheel or runtime bytes are included here. The optional Codex CLI is an external service/client dependency, not part of the project license.

## Literature and benchmarks

Mathematical sources are credited through bibliographic metadata, primary links and independently written comparisons. Full papers, extracted paper text, page images and cached source packs are omitted. A paper's public accessibility, DOI or content hash does not establish permission to redistribute it. Fetch a source from its publisher or author and follow that version's terms; the project license grants no additional rights to it.

DIMACS clique data bytes are also omitted. [spectral_pruning/dimacs_data/provenance.json](spectral_pruning/dimacs_data/provenance.json) retains source URLs and hashes for reproducibility. The inspected distribution did not supply a recorded dataset redistribution grant. Obtain matching inputs separately before using that optional benchmark. No nearby software license is treated as a license for the dataset.

This is an attribution and scope record, not an assertion that every possible future dependency or redistribution has been cleared. Keep applicable upstream license texts, copyright notices and required attribution when distributing upstream copies.
