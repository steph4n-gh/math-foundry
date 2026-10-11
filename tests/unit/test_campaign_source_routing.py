"""Campaign sources preserve mathematical fields, guards and offline limits."""
import hashlib
import json

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.novelty import primary_sources as sources


def theorem(invariant, guard=None, metadata=None):
    c = Conjecture.create(id="routing_control", lhs=InvariantNode(invariant), rel=">=",
                         rhs=ConstantNode(0), guard=guard)
    data = c.to_dict()
    if metadata:
        data["metadata"] = metadata
    return {"conjecture": data}


def test_forest_source_requires_positive_structured_guard_not_model_prose():
    variables = {"graph_energy", "parity_code_dimension", "order", "size"}
    forest = GuardPredicate(predicate_type="property", property_name="is_forest")
    positive = sources.literature_topics({}, variables, theorem("graph_energy", forest))
    assert {"forest_energy", "forest_rank_matching"} <= set(positive)
    assert sources.requested_papers({}, variables, theorem("graph_energy", forest))[0]["url"].endswith("1802.10142v1")
    for target in [theorem("graph_energy", metadata={"explanation": "is_forest would simplify this proof"}),
                   theorem("graph_energy", GuardPredicate(predicate_type="property", property_name="is_forest", negated=True))]:
        topics = sources.literature_topics({}, variables, target)
        assert not {"forest_energy", "forest_rank_matching"} & set(topics)


def test_noncode_topics_do_not_switch_to_characteristic_two_or_incidence_codes():
    record = {"evidence_requests": [{"topic": "alternating_rank", "detail": "compare rank"},
                                    {"topic": "clique_binary_rank", "detail": "compare clique rank"},
                                    {"topic": "cycle_incidence", "detail": "compare cycle theorem"}]}
    variables = {"graph_energy", "spectral_radius", "order", "size"}
    topics = sources.literature_topics(record, variables, theorem("graph_energy"))
    assert topics == ["energy_lower_bounds", "adjacency_edge_envelope"]
    papers = sources.requested_papers(record, variables, theorem("graph_energy"))
    assert papers and all(set(paper["topics"]) & set(topics) for paper in papers)
    assert not {"alternating_rank", "clique_binary_rank", "cycle_incidence"} & set(topics)
    coding = sources.requested_papers(record, {"parity_code_dimension"}, theorem("parity_code_dimension"))
    assert coding[0]["url"].endswith("2405.09254v1")


def test_existing_chromatic_primary_and_missing_noncode_topics_remain_distinct(tmp_path, monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("Cached guidance must not fetch")
    monkeypatch.setattr(sources, "_fetch", forbidden)
    chromatic = sources.prepare_cached_guidance({"chromatic_number", "order", "size"}, tmp_path)
    assert chromatic["coverage"]["requested_topics"] == ["chromatic_edges"]
    assert not chromatic["coverage"]["unregistered_primary_topics"]
    assert chromatic["coverage"]["primary_literature"] == 0
    assert chromatic["coverage"]["unavailable"][0]["url"].endswith("1209.1050v1")
    for variables, topic in [({"estrada_index", "order"}, "estrada"),
                             ({"independence_number", "size"}, "independent_edges")]:
        payload = sources.prepare_cached_guidance(variables, tmp_path)
        assert payload["coverage"]["unregistered_primary_topics"] == [topic]
        assert payload["coverage"]["primary_literature"] == 0
        assert not payload["sources"]
    assert not (tmp_path / "novelty_sources").exists()


@pytest.mark.parametrize("variables,family", [
    ({"spectral_radius", "order", "size", "max_degree"}, "advanced_spectral"),
    ({"algebraic_connectivity", "min_degree", "size"}, "advanced_spectral"),
    ({"chromatic_number", "order", "size", "max_degree"}, "coloring_and_independence"),
    ({"independence_number", "order", "size"}, "coloring_and_independence"),
    ({"triangle_count", "order", "size"}, "extremal_edges_and_triangles"),
    ({"diameter", "order", "max_degree"}, "metric_topological"),
    ({"size", "order", "max_degree"}, "degree_and_structural_classes"),
    ({"parity_code_dimension", "spectral_radius", "size"}, "expander_codes"),
])
def test_pinned_lookup_uses_mathematical_focus_before_degree_bridges(tmp_path, monkeypatch, variables, family):
    from autonomous_math.conjecturing import model_proposals
    declaration = tmp_path / "Spectrum.lean"
    declaration.write_text("namespace Matrix\nvariable (A : Matrix n n R)\n"
                           "theorem spectral_control : True := by trivial\nend Matrix\n")
    proof = tmp_path / "target.lean"
    proof.write_text("theorem routing_control : True := by exact Matrix.spectral_control\n")
    receipt = tmp_path / "receipt.json"
    receipt.write_text(json.dumps({"workspace": str(tmp_path), "source_path": str(proof),
                                   "theorem_name": "routing_control"}))
    calls = []
    def lookup(agenda, workspace):
        calls.append((agenda, workspace))
        return {"status": "AVAILABLE", "sources": [{"source_path": str(declaration),
                "source_sha256": hashlib.sha256(declaration.read_bytes()).hexdigest(),
                "mathlib_relative_path": "Mathlib/Analysis/Matrix/Spectrum.lean"}]}
    monkeypatch.setattr(model_proposals, "lookup_mathlib_declarations", lookup)
    selected, failures = sources.pinned_mathlib_sources({"lean_proof": {"receipt_path": str(receipt)}}, variables)
    assert calls == [({"family": family}, str(tmp_path))]
    assert not failures and selected[0]["theorem_id"] == "Matrix.spectral_control"
    assert "variable (A : Matrix n n R)" in selected[0]["source_context"]


def test_source_policy_identity_refreshes_noncode_without_invalidating_unchanged_code(tmp_path):
    record = {"fingerprint": "exact-proof"}
    for invariant in ["parity_code_dimension", "min_degree", "chromatic_number", "spectral_radius"]:
        target = theorem(invariant)
        papers = sources.requested_papers(record, {invariant}, target)
        old = sources._digest([sources.SOURCE_REVISION, record["fingerprint"], sources.MATHLIB_PIN,
                               [], [(paper, None, None) for paper in papers]])
        current = sources.current_evidence_key(record, target, tmp_path)
        assert (current == old) == (invariant != "spectral_radius")


def test_all_seven_offline_contexts_use_their_selected_campaign(tmp_path, monkeypatch):
    import run_research
    from autonomous_math.conjecturing import model_proposals
    from autonomous_math.prover.trusted_lean import capability_report
    monkeypatch.setattr(sources, "_fetch", lambda *_: pytest.fail("Offline context fetched a paper"))
    capabilities = set(capability_report()["invariants"])
    for name, preset in run_research.CAMPAIGN_PRESETS.items():
        atlas = {"theorems": {}, "total_iterations": 3, "research_family": name}
        context = model_proposals.build_proposal_context(atlas)
        feedback = model_proposals.build_review_feedback(atlas, {"records": []}, tmp_path)
        assert preset["proposal_family"] == name == context["agenda"]["family"] == feedback["family"]
        assert set(context["agenda"]["focus_invariants"]) == set(preset["focus_invariants"]) & capabilities
        assert context["agenda"]["selection"] == "explicit_campaign"
        assert context["agenda"]["rotation_length"] == 1
    assert not (tmp_path / "novelty_sources").exists()
