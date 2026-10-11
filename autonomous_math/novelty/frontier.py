"""Small research-priority views; comparison evidence is never a proof."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import math


_SPECTRAL_FOUNDATIONS = {
    "model_e1bd2d98ab50c3dcff7c": {
        "campaigns": {"spectral", "advanced_spectral"},
        "statement_key": "b65476573631f7ff9e94c3c1c94d2d8be12e81fad3f9b281a0c02ee7bae5eac9",
        "quantity": "signless_laplacian_spectral_radius",
        "interpretation": "Routine irregularity correction: (n-1)q^2 >= 4((n-1)dbar^2+(Delta-dbar)^2).",
        "comparison": "Compare against the stronger published q >= sum(degree(v)^2)/m when m>0, not only the parent or RMS degree bound.",
    },
    "model_f1abeb346d4f50c57240": {
        "campaigns": {"advanced_spectral", "chemical_energy"},
        "statement_key": "5b936bcd4eee7e84e0fb9a197769564236b58c06fee56d74f9ba2ab1e26a6cc6",
        "quantity": "graph_energy",
        "interpretation": "Routine spectral bridge: E >= 2*dbar*(1+max(0,1-gamma)) on connected regular graphs of order at least two.",
        "comparison": "Compare against all supplied applicable energy bounds, including 2*rho, 2*sqrt(m), 2*m/rho (n on nonempty regular graphs), and the parent.",
    },
}


def spectral_refinement_frontier(atlas, family, receipt_validator=None):
    """Reserve two fixed foundations only when their exact current proofs bind.

    Fixed statement hashes prevent a different certified AST under a familiar ID
    from acquiring the interpretation below. These are useful classical helpers,
    not evidence of a literature gap.
    """
    from autonomous_math.core.ast import Conjecture
    from autonomous_math.conjecturing.model_proposals import proposal_statement_key
    from autonomous_math.research_state import validate_receipt
    validate = receipt_validator or validate_receipt
    parents, omitted, fingerprints = [], [], {}
    for identifier, spec in _SPECTRAL_FOUNDATIONS.items():
        if family not in spec["campaigns"]:
            continue
        record = atlas.get("theorems", {}).get(identifier)
        try:
            if not record or record.get("status") != "LEAN_CERTIFIED" or record.get("id") != identifier:
                raise ValueError("Certified foundation is unavailable")
            candidate = Conjecture.from_dict(record["conjecture"])
            key = proposal_statement_key(candidate)
            if key != spec["statement_key"]:
                raise ValueError("Foundation structured statement differs from the reviewed helper")
            path = (record.get("lean_proof") or {}).get("receipt_path", "")
            receipt, error = validate(path, identifier, fingerprints)
            if not receipt or receipt.get("conjecture") != record["conjecture"]:
                raise ValueError(error or "Foundation receipt AST differs")
            binding = {key: receipt[key] for key in ("theorem_name", "source_sha256", "challenge_sha256",
                       "workspace_sha256", "lean_binary_sha256")}
            binding.update(parent_id=identifier, statement_key=key, receipt_path=str(path))
            statement = candidate.to_dict()
            parents.append({"id": identifier, "quantity": spec["quantity"],
                "statement": {key: statement[key] for key in ("lhs_expr", "rel", "rhs_expr", "guard_predicate")},
                "binding": binding, "role": "routine_foundation", "interpretation": spec["interpretation"],
                "published_comparison_requirement": spec["comparison"],
                "field": "Real spectra of the exact finite simple graph matrices; no GF(2) identification.",
                "reuse": "The named Lean declaration is eligible for retrieval; every application must discharge its own premises."})
        except (OSError, ValueError, KeyError, TypeError) as exc:
            omitted.append({"id": identifier, "reason": str(exc)[:240]})
    return {"family": family, "parents": parents, "omitted": omitted,
        "policy": "At most half of proposal slots may refine these routine foundations; preserve independent exploration. "
                  "Require a concrete finite strictness witness against the strongest supplied applicable published comparators. "
                  "Finite numerical separation is not universal correctness, originality, or a publication-priority claim."}


def spectral_refinement_witness(candidate, witness, parents, sources=()):
    """Check one bounded finite witness, retaining numerical limitations explicitly."""
    import networkx as nx
    from autonomous_math.core.ast import BinaryOpNode, InvariantNode, UnaryOpNode
    from autonomous_math.core.invariants import GraphInvariantEvaluator
    if not isinstance(witness, dict) or set(witness) != {"order", "edges"}:
        raise ValueError("A refinement witness needs only order and edges")
    order, edges = witness["order"], witness["edges"]
    if type(order) is not int or not 2 <= order <= 12 or not isinstance(edges, list) or len(edges) > 66:
        raise ValueError("Refinement witness must have order 2..12 and at most 66 edges")
    normalized = []
    for edge in edges:
        if (not isinstance(edge, list) or len(edge) != 2 or any(type(v) is not int for v in edge)
                or not 0 <= edge[0] < edge[1] < order):
            raise ValueError("Witness edges must be distinct ordered pairs within its vertex set")
        normalized.append(tuple(edge))
    if len(set(normalized)) != len(normalized):
        raise ValueError("Witness repeats an edge")
    graph = nx.Graph()
    graph.add_nodes_from(range(order))
    graph.add_edges_from(normalized)
    variables = candidate.lhs_expr.variables | candidate.rhs_expr.variables | {"order", "size", "spectral_radius"}
    values = GraphInvariantEvaluator.evaluate(graph, sorted(variables))
    if not candidate.applies(graph, values):
        raise ValueError("Strictness witness does not satisfy the proposed guard")
    try:
        holds, left, right = candidate.evaluate(graph, values)
    except ArithmeticError as exc:
        raise ValueError("Witness expression exceeds finite numerical evaluation") from exc
    if not holds or not all(math.isfinite(value) for value in (left, right)):
        raise ValueError("The proposed bound fails on its own finite witness")

    def metric_term(node, quantity):
        if isinstance(node, InvariantNode) and node.name == quantity:
            return 1, 1.0
        if isinstance(node, UnaryOpNode) and node.op == "sqr" and isinstance(node.child, InvariantNode) and node.child.name == quantity:
            return 2, 1.0
        if isinstance(node, BinaryOpNode) and node.op == "*":
            for metric, factor in ((node.left, node.right), (node.right, node.left)):
                term = metric_term(metric, quantity)
                if term and quantity not in factor.variables:
                    return term[0], term[1] * factor.evaluate(values)
        return None

    comparison_tokens = {
        "published_degree_square_over_size": "signless_degree_square",
        "published_rms_degree": "signless_rms",
        "published_signless_max_degree": "signless_max_degree",
        "published_energy_twice_radius": "energy_spectral_radius",
        "published_energy_size": "energy_sqrt_edges",
        "published_energy_size_over_radius": "energy_edges_over_radius",
    }
    comparisons, unresolved, source_bindings, missing_sources, required_sources = [], [], {}, set(), set()
    for parent in parents:
        quantity = parent["quantity"]
        lhs, rhs = (candidate.lhs_expr, candidate.rhs_expr) if candidate.rel == ">=" else (candidate.rhs_expr, candidate.lhs_expr)
        term = metric_term(lhs, quantity) if candidate.rel in {">=", "<="} else None
        if not term or quantity in rhs.variables or term[1] <= 0:
            unresolved.append("Unsupported lower-bound shape for " + quantity)
            continue
        proposed = rhs.evaluate(values) / term[1]
        if term[0] == 2:
            if proposed < 0:
                raise ValueError("Squared lower bound cannot establish positive separation")
            proposed = math.sqrt(proposed)
        m, rho = values["size"], values["spectral_radius"]
        if quantity == "signless_laplacian_spectral_radius":
            z = sum(degree * degree for _, degree in graph.degree())
            baselines = {"published_degree_square_over_size": z / m if m else 0.0,
                         "published_rms_degree": 2 * math.sqrt(z / order)}
            if nx.is_connected(graph) and order >= 4:
                baselines["published_signless_max_degree"] = max(dict(graph.degree()).values()) + 1
        else:
            baselines = {"published_energy_twice_radius": 2 * rho,
                         "published_energy_size": 2 * math.sqrt(m),
                         "published_energy_size_over_radius": 2 * m / rho if rho > 0 else 0.0}
            if nx.is_connected(graph) and len(set(dict(graph.degree()).values())) == 1:
                degree = 2 * m / order
                gamma = GraphInvariantEvaluator.evaluate_single(graph, "normalized_laplacian_spectral_gap")
                baselines["certified_energy_gap_parent"] = 2 * degree * (1 + max(0, 1 - gamma))
        for name in baselines:
            token = comparison_tokens.get(name)
            if token is None:  # The local parent has its separate receipt binding.
                continue
            required_sources.add(token)
            applicable = [source for source in sources if token in source.get("comparison_baselines", [])]
            if not applicable:
                missing_sources.add(token)
            for source in applicable:
                source_bindings[source["source_id"]] = {key: source.get(key) for key in
                    ("source_id", "source_type", "title", "url", "locator", "version", "source_sha256", "text_sha256", "comparison_baselines")}
        best = max(baselines.values())
        tolerance = 1e-6 * max(1.0, abs(proposed), abs(best))
        if proposed <= best + tolerance:
            raise ValueError("Witness does not strictly improve the strongest applicable supplied comparator for " + quantity)
        comparisons.append({"quantity": quantity, "proposed_lower_bound": proposed,
                            "applicable_baselines": baselines, "strongest_lower_bound": best,
                            "strictness_margin": proposed - best, "numerical_tolerance": tolerance})
    return {"status": "unresolved" if unresolved or not comparisons else "empirical_separation_only",
            "comparisons": comparisons, "unresolved": unresolved,
            "comparison_source_bindings": [source_bindings[key] for key in sorted(source_bindings)],
            "source_coverage_status": "unresolved" if missing_sources else "snapshot_comparators_present",
            "missing_comparator_sources": sorted(missing_sources),
            "required_comparator_sources": sorted(required_sources),
            "source_scope": "Exact snapshot identities only; source availability and complete applicability must be independently revalidated in originality review.",
            "method": "One finite graph; host invariant evaluation and floating spectral arithmetic.",
            "scope": "Suggested strictness only. No universal proof, exact spectral certificate, or originality claim."}


def spectral_routine_variant(candidate, parents):
    """Recognize only exact weakenings of the two validated helper statements.

    No graph witness, floating arithmetic, variable cancellation, or broad
    semantic equivalence enters this implication check.
    """
    from fractions import Fraction
    from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture
    from autonomous_math.novelty.routine_filter import _add, _affine, expression_key, guard_implies
    if candidate.rel not in {">=", "<="}:
        return None
    left, right = ((candidate.lhs_expr, candidate.rhs_expr) if candidate.rel == ">="
                   else (candidate.rhs_expr, candidate.lhs_expr))

    def nonnegative(key):
        if key == ("constant",):
            return True
        if key[0] == "constant":
            return key[1] >= 0
        if key == ("invariant", "average_degree"):
            return True
        if key[:2] == ("unary", "sqr"):
            return True
        if key[:2] == ("binary", "max"):
            return any(child == ("constant", Fraction(0)) for child in key[2:])
        return key[:2] == ("binary", "*") and all(nonnegative(child) for child in key[2:])

    def dominates(stronger, weaker):
        difference = _add(_affine(stronger), _affine(weaker), Fraction(-1))
        if all(coefficient >= 0 and nonnegative(key) for key, coefficient in difference.items()):
            return True
        # The energy correction shares the nonnegative factor 2*dbar. Factor
        # containment proves a product difference; it never divides by dbar.
        if isinstance(stronger, BinaryOpNode) and stronger.op == "*":
            for factor, tail in ((stronger.left, stronger.right), (stronger.right, stronger.left)):
                if not nonnegative(expression_key(factor)):
                    continue
                if expression_key(factor) == expression_key(weaker):
                    remainder = ConstantNode(1)
                elif isinstance(weaker, BinaryOpNode) and weaker.op == "*":
                    remainder = next((other for same, other in ((weaker.left, weaker.right), (weaker.right, weaker.left))
                                      if expression_key(same) == expression_key(factor)), None)
                else:
                    remainder = None
                if remainder is not None and dominates(tail, remainder):
                    return True
        return False

    for parent in parents:
        previous = Conjecture.from_dict(dict(parent["statement"], id=parent["id"], statement=parent.get("interpretation", "")))
        if (expression_key(left) == expression_key(previous.lhs_expr)
                and guard_implies(candidate.guard_predicate, previous.guard_predicate)
                and dominates(previous.rhs_expr, right)):
            binding = {"parent": parent["binding"], "target": candidate.to_dict()}
            return {"method": "exact_nonnegative_correction_weakening", "parent_ids": [parent["id"]],
                "binding_sha256": hashlib.sha256(json.dumps(binding, sort_keys=True).encode()).hexdigest(),
                "relationship": "routine_weakening", "certifies_target": False,
                "rule": "Identical oriented left side; exact rational nonnegative residual and guard containment."}
    return None


def review_route(assessment):
    outcome = assessment.get("outcome", assessment.get("status"))
    if outcome in {"known_result", "routine_consequence"}:
        return "routine"
    if (outcome == "possible_extension"
            and (assessment.get("challenge") or {}).get("verdict") == "cleared_relative_advance"):
        return "extension_opportunity"
    return "evidence_gap"


def coding_frontier():
    """Recompute a concrete boundary witness with exact GF(2) arithmetic."""
    import networkx as nx
    from autonomous_math.core.expander_codes import (compute_parity_code_dimension,
        compute_parity_code_distance, compute_unique_neighbor_radius)
    edges = [[0, 1], [1, 2], [1, 4], [1, 5], [2, 3], [2, 6], [3, 4], [5, 6]]
    graph = nx.Graph()
    graph.add_nodes_from(range(7))
    graph.add_edges_from(edges)
    k, d, s = (compute_parity_code_dimension(graph), compute_parity_code_distance(graph),
               compute_unique_neighbor_radius(graph) + 1)
    if (k, d, s) != (1, 4, 3) or not nx.is_connected(graph):
        raise ValueError("The retained stopping-distance boundary witness failed exact replay")
    return {"family": "expander_codes", "question":
        "Which multi-cycle structures force a gap d-(u+1) for the binary adjacency kernel, "
        "and can that gap be bounded sharply using order, size and degree?",
        "cycle_excess": "For connected graphs r=m-n+1; seek the boundary beyond r<=1.",
        "witness": {"order": 7, "edges": edges, "dimension": k, "distance": d,
                    "stopping_distance": s, "cycle_excess": 2,
                    "method": "Exact GF(2) row reduction and finite bit-mask enumeration"},
        "policy": "Independent exploration question, not an established literature gap or a universal theorem. "
                  "Compare adjacency and incidence constructions explicitly. Keep positive dimension in guards."}


def progress_view(records, token_usage=None, period=None, now=None):
    """Expose triage versus opportunities; rates require complete accounting."""
    routes, candidates, gaps, cleared = Counter(), [], [], []
    for row in records:
        ai = row.get("ai_review") or {}
        if ai.get("status") != "complete" or ai.get("refresh_pending") or ai.get("superseded"):
            continue
        route = ("routine" if row.get("automatic_status") in {"known_result", "routine_consequence"}
                 else review_route(ai))
        routes[route] += 1
        item = {"id": row["id"], "summary": ai.get("summary", ""),
                "missing_evidence": ai.get("uncertainties", [])[:3]}
        if route == "extension_opportunity":
            candidates.append(item)
            cleared.append(row["id"])
        elif route == "evidence_gap":
            gaps.append(item)
    usage = token_usage or {}
    complete_usage = (usage.get("completed_requests", 0) > 0
                      and usage.get("completed_missing_usage_requests") == 0
                      and usage.get("unreadable_traces") == 0)
    tokens = usage.get("completed_total_tokens", 0)
    result = {"routes": dict(routes), "extension_candidates": candidates,
            "evidence_gaps": gaps, "cleared_candidate_ids": sorted(cleared),
            "cleared_candidates_per_million_recorded_tokens":
                len(cleared) * 1_000_000 / tokens if complete_usage and tokens > 0 else None,
            "token_accounting_complete": complete_usage,
            "interpretation": "Cleared candidates passed two provisional source comparisons. "
                "They are not confirmed original discoveries. The rate uses all retained research request tokens, "
                "including failed attempts; missing usage is unknown. Separate settings periods before comparisons."}
    if period and now is not None:
        elapsed = max(0, now-period["started_at"])
        starting = set(period.get("starting_certified_ids", []))
        current = {row["id"] for row in records}
        added = sorted(current-starting)
        qualified = sorted(set(cleared)-starting)
        result["settings_period"] = {"started_at": period["started_at"], "elapsed_hours": elapsed/3600,
            "starting_checkpoint": period["starting_checkpoint"], "new_certified_ids": added,
            "new_cleared_candidate_ids": qualified,
            "new_certificates_per_hour": len(added)*3600/elapsed if elapsed else None,
            "new_cleared_candidates_per_hour": len(qualified)*3600/elapsed if elapsed else None}
    return result
