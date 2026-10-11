"""A model cannot widen the trusted theorem grammar with its proposal JSON."""
import json
import hashlib
from pathlib import Path
from types import SimpleNamespace
import pytest

from autonomous_math.conjecturing import model_proposals as proposals_module
from autonomous_math.conjecturing.model_proposals import (
    build_proposal_context, decode_proposal, lookup_mathlib_declarations, propose_candidates,
)
from autonomous_math.core.ast import BinaryOpNode, ConstantNode, InvariantNode


def proposal(lhs=None, rhs=None, guard=None):
    return {"lhs_json": json.dumps(lhs or {"node_type": "invariant", "name": "chromatic_number"}),
            "rhs_json": json.dumps(rhs or {"node_type": "constant", "value": 2}),
            "rel": "<=", "guard_json": json.dumps(guard) if guard is not None else None,
            "explanation": "A bipartite graph has a two-coloring, connecting its structural premise to a coloring bound."}


def test_guarded_model_proposal_has_stable_structured_statement():
    p = proposal(guard={"node_type": "guard", "predicate_type": "property", "property_name": "is_bipartite"})
    first, second = decode_proposal(p), decode_proposal(p)
    assert first.to_dict() == second.to_dict()
    assert first.guard_predicate.property_name == "is_bipartite"
    assert first.metadata["origin"] == "codex_proposal"
    assert "novel" not in first.metadata


@pytest.mark.parametrize("node", [
    {"node_type": "invariant", "name": "assumed_spectral_bound"},
    {"node_type": "invariant", "name": "order", "axiom": "False"},
    {"node_type": "constant", "value": float("nan")},
    {"node_type": "constant", "value": True},
    {"node_type": "binary_op", "op": "/", "left": {"node_type": "constant", "value": 1},
     "right": {"node_type": "invariant", "name": "order"}},
])
def test_model_cannot_submit_unknown_or_partial_expressions(node):
    with pytest.raises(ValueError):
        decode_proposal(proposal(lhs=node))


@pytest.mark.parametrize("guard", [
    {"node_type": "guard", "predicate_type": "universal", "property_name": "is_bipartite"},
    {"node_type": "guard", "predicate_type": "universal", "threshold": 0},
    {"node_type": "guard", "predicate_type": "property", "property_name": "is_planar"},
    {"node_type": "guard", "predicate_type": "comparison", "invariant": "order", "op": ">=", "threshold": 1, "negated": True},
    {"node_type": "guard", "predicate_type": "comparison", "invariant": "order", "op": ">=", "threshold": float("inf")},
])
def test_model_cannot_smuggle_ignored_or_unformalized_premises(guard):
    with pytest.raises(ValueError):
        decode_proposal(proposal(guard=guard))


def test_model_expression_size_is_bounded():
    node = {"node_type": "invariant", "name": "order"}
    for _ in range(10):
        node = {"node_type": "unary_op", "op": "neg", "child": node}
    with pytest.raises(ValueError, match="depth"):
        decode_proposal(proposal(lhs=node))


@pytest.mark.parametrize("field,text", [
    ("lhs_json", '{"node_type":"invariant","name":"order","name":"size"}'),
    ("guard_json", '{"node_type":"guard","predicate_type":"property","property_name":"is_bipartite","property_name":"is_tree"}'),
])
def test_model_inner_ast_json_rejects_duplicate_fields(field, text):
    p = proposal()
    p[field] = text
    with pytest.raises(ValueError, match="Duplicate field"):
        decode_proposal(p)


def test_nonlinear_proposal_display_preserves_product_parentheses():
    omega = InvariantNode("clique_number")
    expression = BinaryOpNode("*", omega, BinaryOpNode("-", omega, ConstantNode(1)))
    assert expression.to_latex() == r"\omega(G) \cdot \left(\omega(G) - (1)\right)"


@pytest.mark.parametrize("location", ["nested_expression", "conjunction_guard"])
@pytest.mark.parametrize("sign", [1, -1])
def test_enormous_model_integer_is_rejected_without_losing_valid_proposals(tmp_path, location, sign):
    value = sign * 10**400
    if location == "nested_expression":
        invalid = proposal(lhs={"node_type": "binary_op", "op": "+",
            "left": {"node_type": "invariant", "name": "order"},
            "right": {"node_type": "constant", "value": value}})
    else:
        invalid = proposal(guard={"node_type": "guard", "predicate_type": "conjunction", "guards": [
            {"node_type": "guard", "predicate_type": "comparison", "invariant": "order",
             "op": ">=", "threshold": value}]})
    valid = proposal(guard={"node_type": "guard", "predicate_type": "property", "property_name": "is_bipartite"})
    class Synthesizer:
        def request_json(self, *args):
            return {"proposals": [invalid, valid]}, {"status": "RESPONSE_VALIDATED"}
    candidates, trace = propose_candidates(Synthesizer(), {}, tmp_path, deadline=0, limit=2)
    assert [c.to_dict() for c in candidates] == [decode_proposal(valid).to_dict()]
    assert trace["status"] == "VALIDATED" and trace["accepted"] == 1
    assert len(trace["rejected"]) == 1
    assert trace["rejected"][0]["index"] == 0
    assert "finite and bounded" in trace["rejected"][0]["reason"]
    assert json.loads((tmp_path / "proposal_validation.json").read_text())["accepted"] == 1


def _record(identifier, invariant="chromatic_number", rhs=2, status="EMPIRICAL_SURVIVOR", guard=None):
    conjecture = decode_proposal(proposal(lhs={"node_type": "invariant", "name": invariant},
                                         rhs={"node_type": "constant", "value": rhs}, guard=guard))
    conjecture = conjecture.model_copy(update={"id": identifier})
    return {"id": identifier, "status": status, "conjecture": conjecture.to_dict(),
            "catalog_tested": 100, "holdout_tested": 12,
            "lean_proof": {"receipt_path": identifier}, "novelty_status": "UNKNOWN_IN_LITERATURE"}


@pytest.fixture
def context_receipts(monkeypatch):
    records = {}
    def validate(path, expected_id, fingerprints):
        record = records.get(expected_id)
        if record is None:
            return None, "No intact receipt"
        return {"conjecture": record["conjecture"], "theorem_name": expected_id,
                "source_sha256": "a" * 64}, None
    monkeypatch.setattr(proposals_module, "validate_receipt", validate)
    monkeypatch.setattr(proposals_module, "lookup_mathlib_declarations", lambda *args: {
        "status": "UNAVAILABLE", "declarations": [], "sources": [], "interpretation": "Absence means unknown."})
    return records


def test_agenda_rotates_deterministically_and_keeps_family_relevant_targets(context_receipts):
    coloring = _record("coloring")
    spectral = _record("spectral", "graph_energy", 100)
    atlas = {"theorems": {"coloring": coloring, "spectral": spectral}}
    contexts = [build_proposal_context(dict(atlas, total_iterations=i)) for i in range(12)]
    assert len({c["agenda"]["family"] for c in contexts[:6]}) == 6
    assert [c["agenda"]["family"] for c in contexts[:6]] == [c["agenda"]["family"] for c in contexts[6:]]
    assert build_proposal_context(atlas) == build_proposal_context(atlas)
    assert build_proposal_context(atlas) == build_proposal_context({"theorems": dict(reversed(list(atlas["theorems"].items())))})
    assert [r["id"] for r in contexts[0]["context_selection"]["unresolved_targets"]] == ["coloring"]
    assert [r["id"] for r in contexts[2]["context_selection"]["unresolved_targets"]] == ["spectral"]
    resumed = build_proposal_context(dict(atlas, total_iterations=19, iteration=0))
    assert resumed["agenda"]["rotation_index"] == 1
    assert resumed["agenda"]["iteration"] == 19
    assert resumed["agenda"]["label"] == "Extremal edges and triangles"
    capabilities = proposals_module.capability_report()
    for context in contexts:
        assert set(context["agenda"]["focus_invariants"]) <= set(capabilities["invariants"])
        assert set(context["agenda"]["supported_properties"]) <= set(capabilities["properties"])


def test_large_checked_library_cannot_starve_unresolved_context(context_receipts):
    records = {f"a_{i:03}": _record(f"a_{i:03}", rhs=i + 2, status="LEAN_CERTIFIED") for i in range(100)}
    context_receipts.update(records)
    records["z_target"] = _record("z_target", "independence_number", 8)
    selection = build_proposal_context({"theorems": records})["context_selection"]
    assert [r["id"] for r in selection["unresolved_targets"]] == ["z_target"]
    assert len(selection["checked_bounds"]) <= 6
    assert all(r["evidence_status"] == "KERNEL_RECEIPT_VALIDATED" for r in selection["checked_bounds"])


def test_unresolved_named_target_precedes_fitted_hulls(context_receipts):
    records = {f"hull_{i}": _record(f"hull_{i}") for i in range(20)}
    for record in records.values():
        record["conjecture"]["metadata"]["origin"] = "parametric_hull"
    named = _record("z_motivated_bridge")
    named["conjecture"]["metadata"]["origin"] = "codex_proposal"
    records[named["id"]] = named
    selected = build_proposal_context({"theorems": records})["context_selection"]["unresolved_targets"]
    assert selected[0]["id"] == named["id"]


def test_checked_bridge_bound_is_available_without_a_checked_family_bound(context_receipts):
    bridge = _record("degree_bridge", "size", 10, "LEAN_CERTIFIED")
    bridge["conjecture"]["rhs_expr"] = {"node_type": "binary_op", "op": "*",
        "left": {"node_type": "invariant", "name": "order"},
        "right": {"node_type": "invariant", "name": "max_degree"}}
    context_receipts[bridge["id"]] = bridge
    selected = build_proposal_context({"total_iterations": 3, "theorems": {bridge["id"]: bridge}})["context_selection"]
    assert [r["id"] for r in selected["checked_bounds"]] == [bridge["id"]]


def test_strength_comparison_preserves_distinct_guard_domains(context_receipts):
    bipartite = {"node_type": "guard", "predicate_type": "property", "property_name": "is_bipartite"}
    universal = {"node_type": "guard", "predicate_type": "universal"}
    records = {r["id"]: r for r in [
        _record("weak", rhs=7, status="LEAN_CERTIFIED"),
        _record("strong", rhs=3, status="LEAN_CERTIFIED", guard=universal),
        _record("conditional_weak", rhs=3, status="LEAN_CERTIFIED", guard=bipartite),
        _record("conditional_strong", rhs=2, status="LEAN_CERTIFIED", guard=bipartite),
    ]}
    context_receipts.update(records)
    selected = build_proposal_context({"theorems": records})["context_selection"]["checked_bounds"]
    assert {r["id"] for r in selected} == {"strong", "conditional_strong"}
    assert next(r for r in selected if r["id"] == "conditional_strong")["guard"]["property_name"] == "is_bipartite"


def test_context_does_not_promote_unknown_status_or_unbound_receipt(context_receipts):
    records = {r["id"]: r for r in [_record("unknown", status="MAYBE_PROVED"),
                                       _record("invalid", status="LEAN_CERTIFIED"), _record("empirical")]}
    selection = build_proposal_context({"theorems": records})["context_selection"]
    assert selection["checked_bounds"] == []
    assert selection["unresolved_targets"][0]["evidence_status"] == "EMPIRICAL_ONLY_NOT_PROVED"
    assert selection["unresolved_targets"][0]["literature_status"] == "UNREVIEWED"
    assert {r["id"] for r in selection["excluded"]} == {"invalid", "unknown"}


def test_relevant_old_counterexample_is_kept_instead_of_unrelated_recent_tail(context_receipts):
    import networkx as nx
    from autonomous_math.core.ast import Conjecture
    from autonomous_math.sieve.certificates import CounterexampleCertificate
    old = _record("old_coloring", rhs=1, status="REFUTED",
                  guard={"node_type": "guard", "predicate_type": "property", "property_name": "is_bipartite"})
    cert = CounterexampleCertificate.from_counterexample_graph(nx.path_graph(3), Conjecture.from_dict(old["conjecture"]),
        witness={"type": "direct_evaluation", "details": {"lhs_value": 2, "rhs_value": 1}})
    old["counterexample"] = cert.to_dict()
    tail = [_record(f"recent_{i}", "graph_energy", 0, "REFUTED") for i in range(8)]
    selection = build_proposal_context({"theorems": {old["id"]: old}, "recent_refutations": tail})["context_selection"]
    assert [r["id"] for r in selection["counterexamples"]] == [old["id"]]
    chosen = selection["counterexamples"][0]
    assert chosen["graph"]["edges"] == [(0, 1), (1, 2)]
    assert chosen["graph"]["verification_hash"] == cert.verification_hash
    assert "NOT_REPLAYED_HERE" in chosen["evidence_status"]
    assert chosen["guard"]["property_name"] == "is_bipartite"
    old["counterexample"]["verification_hash"] = "bad"
    assert build_proposal_context({"theorems": {old["id"]: old}})["context_selection"]["counterexamples"] == []


def _lookup_workspace(tmp_path, monkeypatch, source):
    workspace = tmp_path / "certified_lean"
    root = workspace / ".lake/packages/mathlib"
    path = root / "Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean"
    path.parent.mkdir(parents=True)
    path.write_text(source)
    (workspace / "lake-manifest.json").write_text(json.dumps({"packages": [{"name": "mathlib",
        "rev": proposals_module._MATHLIB_REVISION, "url": "https://github.com/leanprover-community/mathlib4.git"}]}))
    def git(command, **kwargs):
        assert command[0] == "git" and kwargs["timeout"] == 3
        return SimpleNamespace(stdout=proposals_module._MATHLIB_REVISION if command[1] == "rev-parse" else "")
    monkeypatch.setattr(proposals_module.subprocess, "run", git)
    return workspace, path


def test_lookup_keeps_source_types_names_context_and_hashes_but_not_comments(tmp_path, monkeypatch):
    source = """/- theorem chromaticNumber_fake : False := by sorry -/
namespace SimpleGraph
variable {V : Type} (G : SimpleGraph V)
@[simp] theorem chromaticNumber_bound [Fintype V] :
    G.chromaticNumber ≤ Fintype.card V := by
  exact G.chromaticNumber_le_card
private theorem chromaticNumber_secret : False := by sorry
end SimpleGraph
"""
    workspace, path = _lookup_workspace(tmp_path, monkeypatch, source)
    agenda = build_proposal_context({}, workspace)["agenda"]
    lookup = lookup_mathlib_declarations(agenda, workspace)
    assert lookup == lookup_mathlib_declarations(agenda, workspace)
    assert lookup["status"] == "SOURCE_MATCHES"
    assert [d["name"] for d in lookup["declarations"]] == ["SimpleGraph.chromaticNumber_bound"]
    declaration = lookup["declarations"][0]
    assert declaration["type"] == "[Fintype V] : G.chromaticNumber ≤ Fintype.card V"
    assert declaration["line"] == 4
    assert declaration["source_context"] == "variable {V : Type} (G : SimpleGraph V)"
    assert declaration["source_sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
    assert "not elaborated types" in lookup["interpretation"] and "unknown" in lookup["interpretation"]


@pytest.mark.parametrize("bad_source", ["oversize", "symlink", "wrong_pin"])
def test_lookup_rejects_unbounded_or_unpinned_sources(tmp_path, monkeypatch, bad_source):
    workspace, path = _lookup_workspace(tmp_path, monkeypatch, "theorem chromaticNumber_ok : True := by trivial")
    if bad_source == "oversize":
        path.write_text(" " * 512001)
    elif bad_source == "symlink":
        outside = tmp_path / "outside.lean"
        outside.write_text(path.read_text())
        path.unlink()
        path.symlink_to(outside)
    else:
        (workspace / "lake-manifest.json").write_text('{"packages": []}')
    agenda = {"family": "coloring_and_independence"}
    lookup = lookup_mathlib_declarations(agenda, workspace)
    assert lookup["status"] == "UNAVAILABLE" and lookup["declarations"] == []


def test_lookup_actual_pinned_mathlib_is_bounded_and_replayable():
    workspace = Path(__file__).resolve().parents[2] / "certified_lean"
    if not (workspace / ".lake/packages/mathlib/.git").exists():
        pytest.skip("Pinned local Mathlib sources are not installed")
    lookup = lookup_mathlib_declarations({"family": "coloring_and_independence"}, workspace)
    assert lookup["status"] == "SOURCE_MATCHES", lookup
    assert 1 <= len(lookup["declarations"]) <= 12
    assert lookup == lookup_mathlib_declarations({"family": "coloring_and_independence"}, workspace)
    assert "SimpleGraph.cliqueNum_le_chromaticNumber" in {d["name"] for d in lookup["declarations"]}
    for declaration in lookup["declarations"]:
        path = Path(declaration["source_path"])
        assert declaration["source_sha256"] == hashlib.sha256(path.read_bytes()).hexdigest()
        assert "theorem" in path.read_text().splitlines()[declaration["line"] - 1] or "lemma" in path.read_text().splitlines()[declaration["line"] - 1]
        assert len(declaration["type"]) <= 1600


def test_proposal_trace_persists_agenda_and_lookup_before_read_only_request(tmp_path, context_receipts):
    target = _record("target")
    class Synthesizer:
        def request_json(self, prompt, schema, attempt_dir, deadline):
            context = json.loads(prompt.split("\n", 1)[1])
            assert context["agenda"]["family"] == "coloring_and_independence"
            assert context["context_selection"]["unresolved_targets"][0]["id"] == "target"
            assert "sharpness unknown" in prompt and "Read only" in prompt
            return {"proposals": [proposal()]}, {"status": "RESPONSE_VALIDATED"}
    candidates, trace = propose_candidates(Synthesizer(), {"theorems": {"target": target}}, tmp_path, 0)
    assert len(candidates) == 1
    assert trace == json.loads((tmp_path / "proposal_validation.json").read_text())
    assert trace["context_bytes"] <= 48000
    assert len(trace["context_sha256"]) == 64
    assert trace["mathlib_lookup"]["status"] == "UNAVAILABLE"


def test_out_of_family_proposal_is_rejected_without_expanding_formalization(tmp_path, context_receipts):
    class Synthesizer:
        def request_json(self, *args):
            return {"proposals": [proposal(lhs={"node_type": "invariant", "name": "size"})]}, {}
    candidates, trace = propose_candidates(Synthesizer(), {}, tmp_path, 0)
    assert not candidates
    assert "selected mathematical family" in trace["rejected"][0]["reason"]


def test_failed_model_request_retains_agenda_lookup_and_selected_context(tmp_path, context_receipts):
    from autonomous_math.prover.codex_synthesis import SynthesisError
    class Synthesizer:
        def request_json(self, *args):
            raise SynthesisError("No model response", {"status": "TIMEOUT"})
    candidates, trace = propose_candidates(Synthesizer(), {}, tmp_path, 0)
    assert not candidates and trace["status"] == "ERROR"
    assert trace["agenda"]["revision"] == proposals_module.AGENDA_REVISION
    assert "mathlib_lookup" in trace and "context_selection" in trace
