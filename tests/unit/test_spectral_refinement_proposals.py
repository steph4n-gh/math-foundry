"""Receipt-bound refinement admission without model or compiler calls."""
import copy
import json
from pathlib import Path

import pytest

from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.core.ast import BinaryOpNode as B, ConstantNode as C, Conjecture, GuardPredicate, InvariantNode as I, UnaryOpNode as U
from autonomous_math.novelty import frontier
from autonomous_math import research_state
from autonomous_math.prover.trusted_lean import render_challenge


IRREGULAR = "model_e1bd2d98ab50c3dcff7c"
ENERGY = "model_f1abeb346d4f50c57240"


def test_native_proposal_schema_requires_all_object_properties_without_breaking_legacy_decode():
    def visit(value):
        if isinstance(value, dict):
            if value.get("type") == "object":
                assert value.get("additionalProperties") is False
                assert set(value["required"]) == set(value["properties"])
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)
    visit(proposals.CANDIDATE_SCHEMA)
    assert "parent_ids" not in proposals.LITERATURE_COMPARISON_SCHEMA["required"]
    assert "strictness_witness" not in proposals.LITERATURE_COMPARISON_SCHEMA["required"]


def foundations():
    n, a, delta, q = I("order"), I("average_degree"), I("max_degree"), I("signless_laplacian_spectral_radius")
    irregular = Conjecture.create(id=IRREGULAR, lhs=B("*", B("-", n, C(1)), U("sqr", q)), rel=">=",
        rhs=B("*", C(4), B("+", B("*", B("-", n, C(1)), U("sqr", a)), U("sqr", B("-", delta, a)))))
    guard = GuardPredicate(predicate_type="conjunction", guards=[
        GuardPredicate(predicate_type="property", property_name="is_connected"),
        GuardPredicate(predicate_type="property", property_name="is_regular"),
        GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=2)])
    energy = Conjecture.create(id=ENERGY, lhs=I("graph_energy"), rel=">=", guard=guard,
        rhs=B("*", B("*", C(2), a), B("+", C(1), B("max", C(0), B("-", C(1), I("normalized_laplacian_spectral_gap"))))))
    return irregular, energy


@pytest.fixture
def atlas(tmp_path, monkeypatch):
    # Stored-receipt fixture exercises actual byte/AST checks. It does not claim
    # these synthetic test files were compiled or certified by a kernel.
    monkeypatch.setattr(research_state, "workspace_fingerprint", lambda *args: "c" * 64)
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"status": "UNAVAILABLE", "declarations": [], "sources": []})
    compiler = tmp_path / "lean-fixture"
    compiler.write_text("compiler identity fixture")
    records = {}
    for candidate in foundations():
        challenge, name = render_challenge(candidate)
        source = tmp_path / (candidate.id + ".lean")
        source.write_text(challenge)
        receipt_path = tmp_path / (candidate.id + ".receipt.json")
        receipt = {"schema_version": 1, "status": "KERNEL_VERIFIED", "conjecture_id": candidate.id,
            "conjecture": candidate.to_dict(), "theorem_name": name, "axioms": [], "statement_checked": True,
            "duration_ms": 0, "source_path": str(source), "source_sha256": research_state.sha256(source),
            "challenge_path": str(source), "challenge_sha256": research_state.sha256(source),
            "workspace": str(tmp_path), "workspace_sha256": "c" * 64,
            "lean_binary": str(compiler), "lean_binary_sha256": research_state.sha256(compiler)}
        receipt_path.write_text(json.dumps(receipt))
        records[candidate.id] = {"id": candidate.id, "status": "LEAN_CERTIFIED", "conjecture": candidate.to_dict(),
            "lean_proof": {"receipt_path": str(receipt_path)}}
    return {"theorems": records, "total_iterations": 214, "research_family": "advanced_spectral"}


def test_complete_foundations_reserved_with_exact_actual_names_and_bindings(atlas):
    original = copy.deepcopy(atlas)
    # Neither a much larger library nor the ordinary six-bound context limit
    # can hide the explicit two foundations.
    atlas["theorems"].update({f"a_{i}": {"id": f"a_{i}", "status": "EMPIRICAL_SURVIVOR",
        "conjecture": Conjecture.create(id=f"a_{i}", lhs=I("graph_energy"), rel=">=", rhs=C(i)).to_dict()} for i in range(50)})
    context = proposals.build_proposal_context(atlas)
    parents = context["spectral_refinement_frontier"]["parents"]
    assert {p["id"] for p in parents} == {IRREGULAR, ENERGY}
    for parent in parents:
        candidate = Conjecture.from_dict(atlas["theorems"][parent["id"]]["conjecture"])
        assert parent["binding"]["theorem_name"] == render_challenge(candidate)[1]
        assert parent["binding"]["statement_key"] == proposals.proposal_statement_key(candidate)
        assert parent["statement"]["guard_predicate"] == candidate.to_dict()["guard_predicate"]
        assert parent["role"] == "routine_foundation" and "Real spectra" in parent["field"]
        assert len(parent["binding"]["source_sha256"]) == 64
    assert {k: atlas["theorems"][k] for k in original["theorems"]} == original["theorems"]


@pytest.mark.parametrize("campaign,expected", [
    ("spectral", {IRREGULAR}), ("advanced_spectral", {IRREGULAR, ENERGY}),
    ("chemical_energy", {ENERGY}), ("expander_codes", set()), ("extremal_coloring", set())])
def test_foundations_route_only_to_compatible_campaigns(atlas, campaign, expected):
    context = proposals.build_proposal_context(dict(atlas, research_family=campaign))
    assert {p["id"] for p in context.get("spectral_refinement_frontier", {}).get("parents", [])} == expected
    if campaign == "chemical_energy":
        assert {"average_degree", "normalized_laplacian_spectral_gap"} <= set(context["agenda"]["bridge_invariants"])


@pytest.mark.parametrize("tamper", ["missing_receipt", "source_bytes", "receipt_ast", "record_ast", "metadata_ast"])
def test_missing_or_tampered_foundation_cannot_be_used(atlas, tamper):
    record = atlas["theorems"][ENERGY]
    path = Path(record["lean_proof"]["receipt_path"])
    receipt = json.loads(path.read_text())
    if tamper == "missing_receipt":
        path.unlink()
    elif tamper == "source_bytes":
        Path(receipt["source_path"]).write_text("changed artifact")
    elif tamper == "receipt_ast":
        receipt["conjecture"]["rhs_expr"] = C(0).to_dict()
        path.write_text(json.dumps(receipt))
    elif tamper == "record_ast":
        record["conjecture"]["rhs_expr"] = C(0).to_dict()
    else:
        record["conjecture"]["metadata"]["ignored_by_statement_key"] = True
    result = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]
    assert [p["id"] for p in result["parents"]] == [IRREGULAR]
    assert any(row["id"] == ENERGY for row in result["omitted"])


def proposal(candidate, role="helper_lemma", parent=ENERGY, witness=None):
    data = candidate.to_dict()
    return {"lhs_json": json.dumps(data["lhs_expr"]), "rhs_json": json.dumps(data["rhs_expr"]),
        "guard_json": json.dumps(data["guard_predicate"]) if data["guard_predicate"] else None,
        "rel": candidate.rel, "explanation": "A bounded helper proposal; no mathematical advance claim.",
        "literature_comparison": {"role": role, "baseline_status": "missing", "best_supplied_baseline": "Unresolved supplied comparison",
            "baseline_assumptions": "Real adjacency spectra on finite simple graphs", "proposed_gap": "Helper only or suggested strictness",
            "proposed_domain": "Explicit structured guard", "field": "Real", "premise_relation": "unknown", "source_quotes": [],
            "originality": "unestablished", "parent_ids": [parent] if parent else [], "strictness_witness": witness}}


def stronger_energy(identifier, offset):
    _, parent = foundations()
    return Conjecture.create(id=identifier, lhs=parent.lhs_expr, rel=parent.rel,
        rhs=B("+", parent.rhs_expr, C(offset)), guard=parent.guard_predicate)


def test_unsupported_declared_improvement_shape_is_rejected_before_proof_spend(atlas):
    cycle = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    candidate = Conjecture.create(id="unsupported_refinement", lhs=B("+", I("graph_energy"), C(1)),
        rel=">=", rhs=C(7), metadata={"literature_comparison": {
            "role": "candidate_improvement", "parent_ids": [ENERGY], "strictness_witness": cycle}})
    context = proposals.build_proposal_context(atlas)
    with pytest.raises(ValueError, match="supported finite lower-bound comparison"):
        proposals._bind_spectral_refinement(candidate, context, atlas)
    assert "spectral_refinement" not in candidate.metadata


def test_four_proposal_call_preserves_two_independent_slots_and_retains_bindings(atlas, tmp_path):
    responses = [proposal(stronger_energy("h1", 1)), proposal(stronger_energy("h2", 2)),
        proposal(Conjecture.create(id="i1", lhs=I("graph_energy"), rel=">=", rhs=C(0)), role="independent_exploration", parent=None),
        proposal(Conjecture.create(id="i2", lhs=I("estrada_index"), rel=">=", rhs=C(0)), role="independent_exploration", parent=None)]
    class Synth:
        def request_json(self, prompt, schema, *args):
            assert schema["properties"]["proposals"]["maxItems"] == 4
            assert ENERGY in prompt and IRREGULAR in prompt
            assert "q>=sum(degree^2)/m" in prompt and "reserve the rest for independent_exploration" in prompt
            return {"proposals": responses}, {}
    candidates, trace = proposals.propose_candidates(Synth(), atlas, tmp_path / "request", 0, limit=4)
    assert len(candidates) == 4 and trace["accepted"] == 4
    assert [c.metadata.get("spectral_refinement", {}).get("role") for c in candidates] == ["helper_lemma", "helper_lemma", None, None]
    for candidate in candidates[:2]:
        binding = candidate.metadata["spectral_refinement"]["parent_bindings"][0]
        assert binding["parent_id"] == ENERGY and binding["theorem_name"] == ENERGY
        assert candidate.metadata["spectral_refinement"]["witness_validation"]["status"] == "helper_only"


def test_refinement_cannot_consume_independent_slots_or_use_missing_parent(atlas, tmp_path):
    responses = [proposal(stronger_energy(f"h{i}", i)) for i in range(1, 4)]
    responses.append(proposal(stronger_energy("missing", 5), parent="unknown_parent"))
    class Synth:
        def request_json(self, *args):
            return {"proposals": responses}, {}
    candidates, trace = proposals.propose_candidates(Synth(), atlas, tmp_path / "request", 0, limit=4)
    assert len(candidates) == 2
    assert "reserved" in trace["rejected"][0]["reason"]
    assert "unbound" in trace["rejected"][1]["reason"]


def test_helper_labels_without_parent_ids_cannot_consume_independent_slots(atlas, tmp_path):
    responses = [proposal(stronger_energy(f"h{i}", i), parent=None) for i in range(1, 4)]
    class Synth:
        def request_json(self, *args):
            return {"proposals": responses}, {}
    candidates, trace = proposals.propose_candidates(Synth(), atlas, tmp_path / "request", 0, limit=4)
    assert len(candidates) == 2 and "reserved" in trace["rejected"][0]["reason"]


def test_parent_restatement_and_candidate_improvement_without_witness_are_rejected(atlas):
    context = proposals.build_proposal_context(atlas)
    _, parent = foundations()
    repeated = proposals.decode_proposal(proposal(parent, role="candidate_improvement"))
    with pytest.raises(ValueError, match="routine"):
        proposals._bind_spectral_refinement(repeated, context, atlas)
    missing = proposals.decode_proposal(proposal(stronger_energy("unknown", 0.1), role="candidate_improvement"))
    with pytest.raises(ValueError, match="witness"):
        proposals._bind_spectral_refinement(missing, context, atlas)


def test_energy_witness_must_improve_n_baseline_not_only_weaker_gap_parent(atlas):
    parents = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]["parents"]
    parents = [p for p in parents if p["id"] == ENERGY]
    _, foundation = foundations()
    candidate = Conjecture.create(id="weak", lhs=I("graph_energy"), rel=">=", rhs=C(5), guard=foundation.guard_predicate)
    cycle = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    with pytest.raises(ValueError, match="strongest"):
        frontier.spectral_refinement_witness(candidate, cycle, parents)
    stronger = Conjecture.create(id="strict", lhs=I("graph_energy"), rel=">=", rhs=C(7), guard=foundation.guard_predicate)
    result = frontier.spectral_refinement_witness(stronger, cycle, parents)
    assert result["status"] == "empirical_separation_only"
    assert result["comparisons"][0]["strongest_lower_bound"] == pytest.approx(6)
    assert "No universal proof" in result["scope"]
    assert result["source_coverage_status"] == "unresolved"
    assert set(result["missing_comparator_sources"]) == {"energy_spectral_radius", "energy_sqrt_edges", "energy_edges_over_radius"}
    assert result["required_comparator_sources"] == result["missing_comparator_sources"]
    sources = [{"source_id": "saved_energy_text", "source_type": "primary_literature", "text_sha256": "a" * 64,
        "source_sha256": "b" * 64, "comparison_baselines": ["energy_spectral_radius", "energy_sqrt_edges", "energy_edges_over_radius"]}]
    bound = frontier.spectral_refinement_witness(stronger, cycle, parents, sources)
    assert bound["source_coverage_status"] == "snapshot_comparators_present"
    assert bound["comparison_source_bindings"][0]["source_id"] == "saved_energy_text"
    assert bound["comparison_source_bindings"][0]["text_sha256"] == "a" * 64


@pytest.mark.parametrize("correction", [0, 0.5, 1])
def test_energy_correction_weakening_is_exactly_routine_only_with_parent_guards(atlas, correction):
    _, parent = foundations()
    candidate = Conjecture.create(id="weaker", lhs=parent.lhs_expr, rel=">=", guard=parent.guard_predicate,
        rhs=B("*", B("*", C(2), I("average_degree")), B("+", C(1),
            B("*", C(correction), B("max", C(0), B("-", C(1), I("normalized_laplacian_spectral_gap")))))))
    parents = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]["parents"]
    audit = frontier.spectral_routine_variant(candidate, parents)
    assert audit["parent_ids"] == [ENERGY] and audit["certifies_target"] is False
    universal = candidate.model_copy(update={"guard_predicate": None})
    assert frontier.spectral_routine_variant(universal, parents) is None
    strict = candidate.model_copy(update={"rel": ">"})
    assert frontier.spectral_routine_variant(strict, parents) is None


@pytest.mark.parametrize("coefficient,expected", [(0, True), (2, True), (4, True), (5, False)])
def test_irregularity_correction_weakening_never_cancels_n_minus_one(atlas, coefficient, expected):
    parent, _ = foundations()
    candidate = Conjecture.create(id="correction", lhs=parent.lhs_expr, rel=">=",
        rhs=B("+", B("*", C(4), B("*", B("-", I("order"), C(1)), U("sqr", I("average_degree")))),
            B("*", C(coefficient), U("sqr", B("-", I("max_degree"), I("average_degree"))))))
    parents = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]["parents"]
    assert bool(frontier.spectral_routine_variant(candidate, parents)) is expected


def test_energy_stronger_correction_is_not_routine_and_negative_spectral_atom_is_not_nonnegative(atlas):
    _, parent = foundations()
    parents = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]["parents"]
    stronger = stronger_energy("stronger", 1)
    assert frontier.spectral_routine_variant(stronger, parents) is None
    fake = copy.deepcopy(parents[1])
    fake["statement"]["rhs_expr"] = I("smallest_adjacency_eigenvalue").to_dict()
    zero = Conjecture.create(id="zero", lhs=I("graph_energy"), rel=">=", rhs=C(0), guard=parent.guard_predicate)
    assert frontier.spectral_routine_variant(zero, [fake]) is None


def test_overflowing_suggested_witness_rejects_only_that_proposal(atlas, tmp_path):
    _, parent = foundations()
    overflow = Conjecture.create(id="overflow", lhs=I("graph_energy"), rel=">=",
        rhs=U("exp", C(1e6)), guard=parent.guard_predicate)
    cycle = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    responses = [proposal(overflow, role="candidate_improvement", witness=cycle),
        proposal(Conjecture.create(id="independent", lhs=I("estrada_index"), rel=">=", rhs=C(0)),
                 role="independent_exploration", parent=None)]
    class Synth:
        def request_json(self, *args):
            return {"proposals": responses}, {}
    candidates, trace = proposals.propose_candidates(Synth(), atlas, tmp_path / "request", 0, limit=4)
    assert len(candidates) == 1 and "finite numerical" in trace["rejected"][0]["reason"]


@pytest.mark.parametrize("witness", [{"order": 100, "edges": []}, {"order": 3, "edges": [[0, 0]]},
    {"order": 3, "edges": [[1, 0]]}, {"order": 3, "edges": [[0, 1], [0, 1]]},
    {"order": 3, "edges": [[0, True]]}, {"order": 3, "edges": [[0, 3]]}])
def test_finite_witness_grammar_is_bounded(atlas, witness):
    parent = proposals.build_proposal_context(atlas)["spectral_refinement_frontier"]["parents"][1]
    with pytest.raises(ValueError):
        frontier.spectral_refinement_witness(stronger_energy("x", 1), witness, [parent])
