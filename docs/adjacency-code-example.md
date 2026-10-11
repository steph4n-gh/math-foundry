# A binary adjacency code in one minute

This Python-only example computes a small code and shows successful, blocked and inconsistent erasure inputs. It uses the existing exact APIs; it starts no researcher, writes no files, and makes no AI or Lean requests. No account or downloaded papers are needed.

From the public checkout root, install the Python dependencies if necessary:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -e .
python -B -m examples.adjacency_code_demo
```

The runnable source is [examples/adjacency_code_demo.py](../examples/adjacency_code_demo.py). Change its graph or received word to explore other small cases; keep the assumptions and finite evaluation limit below in view.

## What the graph represents

Take the cycle `0—1—2—3—0`. Variables and parity checks are separate copies of its four vertices. Its square adjacency matrix is the check matrix over GF(2), so the code is `C(G) = ker A(G)`. A check requires the sum of its neighboring variable bits to be even. Here the equations are `x1 + x3 = 0` and `x0 + x2 = 0`, each repeated twice. The codewords are `0000`, `0101`, `1010` and `1111`: dimension two, minimum nonzero weight two.

The unique-neighbor radius `u=1` means every nonempty erased-variable set of size at most one has a check touching exactly one erased variable. With word `1010` and variable 0 erased, check 1 touches variables 0 and 2; its known bit `x2=1` forces `x0=1`. A decoder step records `(check, recovered variable, recovered bit)`.

Expected output:

```text
C4 vertices: [0, 1, 2, 3]
Adjacency check matrix over GF(2):
  0 1 0 1
  1 0 1 0
  0 1 0 1
  1 0 1 0
Codewords: 0000, 0101, 1010, 1111
dimension=2, distance=2, unique_neighbor_radius=1
distance bridge: u + 1 = 2 <= d = 2
One erasure [None, 0, 1, 0]: DECODED, word=(1, 0, 1, 0)
Steps (check, recovered variable, recovered bit): ((1, 0, 1),)
Finite recovery check: all 20 C4 word/erasure cases with |S| <= u passed
Two erasures [None, 0, None, 0]: BLOCKED, unresolved=(0, 2)
Both 0000 and 1010 complete that blocked input.
Known bits [1, 0, 0, 0]: INCONSISTENT, violated_checks=(1, 3)
K2: n=2, dimension=0, distance=3, u=2 (zero-code sentinel)
Empty graph: n=0, dimension=0, distance=1, u=0 (zero-code sentinel)
Order 17: rejected (Exact adjacency-code evaluation supports at most 16 vertices)
AI requests: 0; Lean calls: 0; files written: 0
```

The script checks all four codewords with every erased set of size zero or one: twenty finite cases. Erasing both variables 0 and 2 leaves no single-unknown check. That particular blocked input has two valid completions. In general, `BLOCKED` means peeling cannot continue, not that no completion or unique completion exists. `INCONSISTENT` reports fully known checks whose parity is violated; it does not correct arbitrary bit errors. Known received bits must be uncorrupted for an erasure-recovery guarantee.

## Scope of the evidence

The checked universal coding theorem [unique_neighbor_distance.lean](../library/coding/unique_neighbor_distance.lean) proves `u + 1 <= d` for all finite graphs under the native definitions. [erasure_recovery.lean](../library/coding/erasure_recovery.lean) proves that two codewords agreeing outside an erased set of size at most `u` must be equal. These are known mechanisms, not claims of discovery. The latter theorem certifies mathematical uniqueness; it does not formally verify the Python peeling implementation. This example performs finite executable checks only. Fresh kernel replay is a separate task described in [verification](verification.md).

The exact Python code APIs accept simple undirected graphs of order at most **16**. Distance and stopping-set searches enumerate supports and can grow exponentially; larger graphs raise an error instead of returning an approximation. The trusted Lean definitions have all-finite-graph scope, independent of this Python cap.

A zero-dimensional code has only the zero word, so it has no ordinary minimum nonzero weight. The engine uses the explicit finite sentinel `d=n+1`: `K2` therefore has `d=3`, and the empty graph has `d=1`. These values do not describe useful message capacity. Always inspect dimension before interpreting a distance. With no stopping set, the convention is `u=n`.

This restricted adjacency-kernel construction is not automatically an asymptotically good expander/Tanner code, and the example establishes no cryptographic security, adversarial-error correction or decoding-performance advantage. See the [campaign definitions](expander-codes.md) and [coding proof notes](../library/coding/README.md) for the precise distinction.
