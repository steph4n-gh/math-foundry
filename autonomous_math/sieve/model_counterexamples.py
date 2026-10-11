"""Host-checked graph witnesses; model text and claimed invariants are not evidence."""

from __future__ import annotations

import math

import networkx as nx

from autonomous_math.core.ast import Conjecture, GuardPredicate
from autonomous_math.core.invariants import GraphInvariantEvaluator
from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier

MAX_GRAPH_ORDER = 64
MAX_GRAPH_EDGES = 2016
HARD_INVARIANTS = {"chromatic_number", "clique_number", "independence_number"}


def validate_counterexample_graph(data) -> nx.Graph:
    """Accept only bounded JSON order/edges, with no coercion or graph constructors."""
    if not isinstance(data, dict) or set(data) != {"order", "edges"}:
        raise ValueError("Graph must contain exactly order and edges")
    order, edges = data["order"], data["edges"]
    if type(order) is not int or not 0 <= order <= MAX_GRAPH_ORDER:
        raise ValueError("Graph order must be an integer from 0 through 64")
    if not isinstance(edges, list) or len(edges) > min(MAX_GRAPH_EDGES, order * (order - 1) // 2):
        raise ValueError("Graph edge list exceeds the simple-graph bound")
    seen = set()
    for edge in edges:
        if not isinstance(edge, list) or len(edge) != 2 or any(type(v) is not int for v in edge):
            raise ValueError("Each edge must contain exactly two integer endpoints")
        u, v = edge
        if not (0 <= u < order and 0 <= v < order) or u == v:
            raise ValueError("Graph edge is out of range or a self-loop")
        pair = (min(u, v), max(u, v))
        if pair in seen:
            raise ValueError("Duplicate undirected graph edge")
        seen.add(pair)
    graph = nx.Graph()
    graph.add_nodes_from(range(order))
    graph.add_edges_from(sorted(seen))
    graph.name = "model_counterexample"
    return graph


def _guard_names(guard) -> set[str]:
    if guard is None or guard == "universal":
        return set()
    if isinstance(guard, str):
        guard = GuardPredicate.from_dict(guard)
    if guard.predicate_type == "conjunction":
        return set().union(*(_guard_names(g) for g in (guard.guards or [])))
    if guard.predicate_type == "comparison":
        if not math.isfinite(float(guard.threshold or 0)):
            raise ValueError("Guard threshold must be finite")
        return {guard.invariant or "order"}
    if guard.predicate_type == "property":
        name = guard.property_name
        if not GraphInvariantEvaluator.normalize_name(name).startswith("is_"):
            raise ValueError("Unsupported bounded guard property")
        return {name}
    return set()



def counterexample_order_limit(conjecture):
    if conjecture is None:
        return 64
    names = conjecture.lhs_expr.variables | conjecture.rhs_expr.variables | _guard_names(conjecture.guard_predicate)
    canonical = {GraphInvariantEvaluator.normalize_name(name) for name in names}
    return 16 if canonical & {"parity_code_dimension", "parity_code_distance", "unique_neighbor_radius"} else 64

def _refutation_values(graph, conjecture):
    if not isinstance(conjecture, Conjecture):
        raise ValueError("An exact host Conjecture is required")
    names = set(conjecture.lhs_expr.variables) | set(conjecture.rhs_expr.variables) | _guard_names(conjecture.guard_predicate)
    canonical = {GraphInvariantEvaluator.normalize_name(name) for name in names}
    hard = canonical & HARD_INVARIANTS
    order, size = len(graph), graph.number_of_edges()
    if order > counterexample_order_limit(conjecture):
        raise ValueError(f"Counterexample exceeds the exact checker order limit of {counterexample_order_limit(conjecture)} for this conjecture")
    if order > 32 and hard and size not in {0, order * (order - 1) // 2}:
        if ((hard & {"chromatic_number", "independence_number"} and not nx.is_bipartite(graph))
                or ("clique_number" in hard and any(nx.triangles(graph).values()))):
            raise ValueError("Unsupported bounded verification: large graph requires a non-polynomial exact invariant")
    # Chromatic search has at most n color checks; decomposed independence has
    # at most n solver components. Share five seconds across those checks.
    timeout_ms = min(5000, max(1, 5000 // max(order, 1)))
    env = GraphInvariantEvaluator.evaluate(graph, sorted(names), timeout_ms=timeout_ms)
    if any(not math.isfinite(float(value)) for value in env.values()):
        raise ValueError("Host invariant evaluation is nonfinite")
    if not conjecture.applies(graph, env):
        raise ValueError("Counterexample does not satisfy the premise guard")
    holds, lhs, rhs = conjecture.evaluate(graph, invariants=env)
    if not math.isfinite(lhs) or not math.isfinite(rhs):
        raise ValueError("Host conjecture evaluation is nonfinite")
    if holds:
        raise ValueError("Conjecture is not violated on the supplied graph")
    return lhs, rhs


def _structure(cert, conjecture, graph):
    if cert.refutation_witness.get("type") != "direct_evaluation":
        raise ValueError("Model certificates require a direct_evaluation witness")
    for check in (CounterexampleCertificateVerifier.verify_matrix_structure,
                  CounterexampleCertificateVerifier.verify_edge_consistency):
        valid, error = check(cert)
        if not valid:
            raise ValueError(error)
    valid, error = CounterexampleCertificateVerifier.verify_refutation_witness(cert, conjecture, graph)
    if not valid or cert.verification_hash != cert.compute_hash():
        raise ValueError(error or "Counterexample verification hash mismatch")


def verify_model_counterexample(data, conjecture) -> CounterexampleCertificate:
    """Evaluate a model graph with bounded exact host calls; undefined is rejected."""
    try:
        graph = validate_counterexample_graph(data)
        lhs, rhs = _refutation_values(graph, conjecture)
        cert = CounterexampleCertificate.from_counterexample_graph(graph, conjecture,
            witness={"type": "direct_evaluation", "details": {"lhs_value": lhs, "rel": conjecture.rel, "rhs_value": rhs}})
        _structure(cert, conjecture, graph)
        return cert
    except InterruptedError:
        raise
    except Exception as exc:
        raise ValueError(f"Counterexample verification failed: {exc}") from exc


def verify_model_counterexample_certificate(data, conjecture) -> CounterexampleCertificate:
    """Replay a serialized model certificate without unbounded solver re-evaluation."""
    try:
        if not isinstance(data, dict) or set(data) - set(CounterexampleCertificate.model_fields):
            raise ValueError("Unexpected counterexample certificate fields")
        edges = data["edges"]
        if not isinstance(edges, (list, tuple)) or len(edges) > MAX_GRAPH_EDGES:
            raise ValueError("Invalid certificate edges")
        graph = validate_counterexample_graph({"order": data["graph_order"],
            "edges": [list(edge) if isinstance(edge, (list, tuple)) else edge for edge in edges]})
        if data["conjecture_id"] != conjecture.id or type(data["graph_size"]) is not int or data["graph_size"] != graph.number_of_edges():
            raise ValueError("Counterexample target ID or graph size mismatch")
        matrix = data["adjacency_matrix"]
        if not isinstance(matrix, list) or len(matrix) != len(graph) or any(
                not isinstance(row, list) or len(row) != len(graph) or any(type(v) is not int or v not in (0, 1) for v in row)
                for row in matrix):
            raise ValueError("Invalid raw certificate adjacency matrix")
        cert = CounterexampleCertificate.from_dict(data)
        _structure(cert, conjecture, graph)
        invariants = data["invariants"]
        details = data["refutation_witness"].get("details")
        if (not isinstance(invariants, dict) or set(invariants) != {"order", "size"}
                or any(type(value) is not int for value in invariants.values())
                or not isinstance(details, dict) or set(details) != {"lhs_value", "rel", "rhs_value"}
                or any(type(details[name]) not in (int, float) or not math.isfinite(details[name])
                       for name in ("lhs_value", "rhs_value"))):
            raise ValueError("Invalid raw host invariant or refutation witness values")
        lhs, rhs = _refutation_values(graph, conjecture)
        expected = {"type": "direct_evaluation", "details": {"lhs_value": lhs, "rel": conjecture.rel, "rhs_value": rhs}}
        if cert.refutation_witness != expected or cert.invariants != {"order": len(graph), "size": graph.number_of_edges()}:
            raise ValueError("Counterexample witness or invariants differ from host evaluation")
        return cert
    except (InterruptedError, TimeoutError):
        raise
    except Exception as exc:
        raise ValueError(f"Counterexample certificate verification failed: {exc}") from exc
