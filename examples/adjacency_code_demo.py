"""A finite GF(2) adjacency-code example; run from the checkout root.

    python -B -m examples.adjacency_code_demo

Uses the existing exact code/peeling APIs. No files, AI requests or Lean calls.
"""

from itertools import combinations, product

import networkx as nx

from autonomous_math.core.expander_codes import (
    MAX_EXACT_CODE_ORDER,
    compute_parity_code_dimension,
    compute_parity_code_distance,
    compute_unique_neighbor_radius,
    peel_erasures,
)


def main():
    graph = nx.cycle_graph(4)
    vertices = list(range(4))
    words = [
        word
        for word in product((0, 1), repeat=4)
        if all(sum(word[v] for v in graph.neighbors(check)) % 2 == 0
               for check in vertices)
    ]
    dimension = compute_parity_code_dimension(graph)
    distance = compute_parity_code_distance(graph)
    radius = compute_unique_neighbor_radius(graph)
    assert (dimension, distance, radius) == (2, 2, 1)
    assert len(words) == 2 ** dimension
    assert min(sum(word) for word in words if any(word)) == distance

    print("C4 vertices: [0, 1, 2, 3]")
    print("Adjacency check matrix over GF(2):")
    for check in vertices:
        print("  " + " ".join(str(int(graph.has_edge(check, v))) for v in vertices))
    print("Codewords:", ", ".join("".join(map(str, word)) for word in words))
    print(f"dimension={dimension}, distance={distance}, unique_neighbor_radius={radius}")
    print(f"distance bridge: u + 1 = {radius + 1} <= d = {distance}")

    received = [None, 0, 1, 0]  # Erase bit 0 of the nonzero word 1010.
    decoded = peel_erasures(graph, received)
    assert decoded.status == "DECODED" and decoded.word == (1, 0, 1, 0)
    assert decoded.steps == ((1, 0, 1),) and received == [None, 0, 1, 0]
    print(f"One erasure {received}: {decoded.status}, word={decoded.word}")
    print("Steps (check, recovered variable, recovered bit):", decoded.steps)

    checked = 0
    for word in words:
        for size in range(radius + 1):
            for erased in combinations(vertices, size):
                partial = [None if v in erased else word[v] for v in vertices]
                result = peel_erasures(graph, partial)
                assert result.status == "DECODED" and result.word == word
                checked += 1
    print(f"Finite recovery check: all {checked} C4 word/erasure cases with |S| <= u passed")

    blocked = peel_erasures(graph, [None, 0, None, 0])
    assert blocked.status == "BLOCKED" and blocked.unresolved_positions == (0, 2)
    assert not blocked.steps
    print(f"Two erasures [None, 0, None, 0]: {blocked.status}, unresolved={blocked.unresolved_positions}")
    print("Both 0000 and 1010 complete that blocked input.")

    inconsistent = peel_erasures(graph, [1, 0, 0, 0])
    assert inconsistent.status == "INCONSISTENT" and inconsistent.violated_checks == (1, 3)
    print(f"Known bits [1, 0, 0, 0]: {inconsistent.status}, violated_checks={inconsistent.violated_checks}")

    for name, control, expected in (
        ("K2", nx.path_graph(2), (0, 3, 2)),
        ("Empty graph", nx.empty_graph(0), (0, 1, 0)),
    ):
        values = (compute_parity_code_dimension(control),
                  compute_parity_code_distance(control),
                  compute_unique_neighbor_radius(control))
        assert values == expected
        print(f"{name}: n={len(control)}, dimension={values[0]}, distance={values[1]}, u={values[2]} (zero-code sentinel)")

    try:
        compute_parity_code_distance(nx.empty_graph(MAX_EXACT_CODE_ORDER + 1))
    except ValueError as error:
        print(f"Order {MAX_EXACT_CODE_ORDER + 1}: rejected ({error})")
    else:
        raise AssertionError("The exact evaluation order cap was not enforced")
    print("AI requests: 0; Lean calls: 0; files written: 0")


if __name__ == "__main__":
    main()
