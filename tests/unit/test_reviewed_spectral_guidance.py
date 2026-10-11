"""Reviewed comparisons guide proposals without extending proof assumptions."""
import copy
import hashlib
import json

import pytest

from autonomous_math.conjecturing import model_proposals as proposals
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.novelty import model_review, primary_sources as sources, review as reviews


def named_fixture(tmp_path, monkeypatch):
    c = Conjecture.create(id="target", lhs=InvariantNode("max_degree"), rel="<=", rhs=ConstantNode(3))
    path = tmp_path / "receipt.json"
    path.write_text("{}")
    record = {"id": c.id, "status": "LEAN_CERTIFIED", "conjecture": c.to_dict(), "lean_proof": {"receipt_path": str(path)}}
    receipt = {"schema_version": 2, "conjecture": c.to_dict(), "theorem_name": c.id, "source_sha256": "a" * 64,
               "challenge_sha256": "b" * 64, "workspace_sha256": "c" * 64}
    fingerprint = reviews._fingerprint(record, receipt, path)
    named = {"id": c.id, "fingerprint": fingerprint, "reviewer": "AI-assisted named source comparison",
             "status": "routine_consequence", "summary": "Published premise implies this bound",
             "contribution": "Routine consequence, no originality established",
             "closest_results": [{"title": "Primary theorem", "url": "https://example.org/paper.pdf",
                 "citation": "Author (2007), Theorem 4.2", "relationship": "routine_consequence",
                 "comparison": "Same exact domain; explicit elementary deduction"}],
             "checks": [{"label": label, "status": "pass", "detail": "Exact domain compared"}
                        for label in reviews.REQUIRED_CHECKS], "uncertainties": ["Historical priority remains unresolved"]}
    review = {"id": c.id, "fingerprint": fingerprint, "automatic_assessment": {"status": "awaiting_review"},
              "ai_review": {"status": "complete"}, "assessment": {"evidence": named}}
    monkeypatch.setattr(proposals, "validate_receipt", lambda *args: (receipt, ""))
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"status": "UNAVAILABLE", "declarations": [], "sources": []})
    return {"research_family": "degree_and_structural_classes", "theorems": {c.id: record}}, review, named, receipt


def test_receipt_bound_named_routine_guidance_precedes_old_ai_without_new_authority(tmp_path, monkeypatch):
    atlas, review, named, _ = named_fixture(tmp_path, monkeypatch)
    original = copy.deepcopy((atlas, review))
    monkeypatch.setattr(model_review, "validate_completed_review", lambda *args: pytest.fail("Old AI must not override named routine comparison"))
    feedback = proposals.build_review_feedback(atlas, {"records": [review]}, tmp_path)
    assert (atlas, review) == original
    item = feedback["entries"][0]
    assert item["provenance"] == "receipt_bound_named_assessment_guidance"
    assert item["outcome"] == "routine_consequence" and item["route"] == "routine"
    assert item["action"] == "avoid_exact_restatement"
    assert item["source_binding"]["reviewer"] == named["reviewer"]
    assert "not expert review" in item["source_binding"]["scope"]
    assert "no proof" in item["interpretation"]
    digest = feedback.pop("sha256")
    assert digest == hashlib.sha256(json.dumps(feedback, sort_keys=True, allow_nan=False).encode()).hexdigest()


@pytest.mark.parametrize("bad", ["id", "fingerprint", "reviewer", "comparison", "checks", "credential_url", "potential", "awaiting"])
def test_unbound_malformed_or_positive_named_text_does_not_override_ai(tmp_path, monkeypatch, bad):
    atlas, review, named, _ = named_fixture(tmp_path, monkeypatch)
    if bad in {"id", "fingerprint"}: named[bad] = "stale"
    elif bad == "reviewer": named["reviewer"] = ""
    elif bad == "comparison": named["closest_results"] = []
    elif bad == "checks": named["checks"] = []
    elif bad == "credential_url": named["closest_results"][0]["url"] = "https://user:secret@example.org/paper"
    elif bad == "potential": named["status"] = "potential_contribution"
    else: named["status"] = "awaiting_review"
    calls = []
    monkeypatch.setattr(model_review, "validate_completed_review", lambda *args: calls.append(args) or {
        "assessment": {"outcome": "unresolved", "summary": "Still unresolved", "comparisons": [], "uncertainties": []}})
    feedback = proposals.build_review_feedback(atlas, {"records": [review]}, tmp_path)
    assert len(calls) == 1
    assert feedback["entries"][0]["provenance"] == "completed_source_validated_ai_guidance"
    assert feedback["entries"][0]["route"] == "evidence_gap"


@pytest.mark.parametrize("bad", ["receipt_ast", "record_fingerprint"])
def test_stale_exact_proof_drops_even_named_routine_guidance(tmp_path, monkeypatch, bad):
    atlas, review, _, receipt = named_fixture(tmp_path, monkeypatch)
    if bad == "receipt_ast": receipt["conjecture"]["rhs_expr"]["value"] = 4
    else: review["fingerprint"] = "stale"
    monkeypatch.setattr(model_review, "validate_completed_review", lambda *args: pytest.fail("Stale proof must not reach AI guidance"))
    assert not proposals.build_review_feedback(atlas, {"records": [review]}, tmp_path)["entries"]


def test_reviewed_topics_do_not_route_coding_or_coloring_into_spectral_corpus():
    assert "adjacency_edge_envelope" in sources.literature_topics({}, {"spectral_radius", "size"})
    assert "signless_clique_cut" in sources.literature_topics({}, {"signless_laplacian_spectral_radius", "clique_number"})
    for variables in ({"parity_code_distance", "order", "size"}, {"chromatic_number", "size"}):
        topics = sources.literature_topics({}, variables)
        assert not set(topics) & {"adjacency_edge_envelope", "signless_clique_cut"}
        assert not any(p.get("reviewed_comparison") for p in sources.requested_papers({}, variables))
    assert sources.SOURCE_REVISION == "spectral-comparison-primary-papers-v4"
    assert sources.EXTRACTION_REVISION == "complete-html-statements-and-context-v2"


@pytest.mark.parametrize("title", ["A Bound on the Spectral Radius of Graphs with e Edges", "The Spectral Radius of a Planar Graph"])
def test_transcription_binds_pdf_and_page_image_without_replacing_exact_quote(tmp_path, monkeypatch, title):
    paper = next(p for p in sources._PAPERS if p["title"] == title)
    comparison = paper["reviewed_comparison"]
    spec = paper["pdf_context_markers"][0]
    raw = spec["start"] + " garbled scan mathematical glyphs " + spec["end"]
    entry = {**paper, "source_sha256": comparison["source_sha256"], "final_url": paper["url"],
             "version": "retained", "pdf_path": "novelty_sources/scan.pdf", "text_path": "novelty_sources/pages.json",
             "text_file_sha256": "a" * 64, "format": "pdf"}
    cache = tmp_path / "novelty_sources";cache.mkdir()
    image = cache / (entry["source_sha256"] + ".reviewed-page.png")
    with pytest.raises(OSError): sources._paper_excerpt(entry, [{"page": 2, "text": raw}], set(), tmp_path)
    image.write_bytes(b"retained page image fixture")
    monkeypatch.setattr(sources, "sha256", lambda path: comparison["page_image_sha256"])
    source = sources._paper_excerpt(entry, [{"page": 2, "text": raw}], set(), tmp_path)[0]
    assert source["text"] == raw[:raw.index(spec["end"])]
    assert source["math_readable"] is False
    assert source["reviewed_comparison"]["statement"] != source["text"]
    assert source["cache_files"][-1]["kind"] == "reviewed_page_image"
    changed = {**entry, "source_sha256": "0" * 64}
    assert "reviewed_comparison" not in sources._paper_excerpt(changed, [{"page": 2, "text": raw}], set(), tmp_path)[0]
    monkeypatch.setattr(sources, "sha256", lambda path: "f" * 64)
    with pytest.raises(ValueError, match="page-image binding"): sources._paper_excerpt(entry, [{"page": 2, "text": raw}], set(), tmp_path)


@pytest.mark.parametrize("family,spectral", [("spectral", True), ("advanced_spectral", True), ("chemical_energy", True), ("expander_codes", False), ("extremal_coloring", False)])
def test_steering_is_spectral_only_and_keeps_four_slots(tmp_path, monkeypatch, family, spectral):
    monkeypatch.setattr(proposals, "lookup_mathlib_declarations", lambda *args: {"status": "UNAVAILABLE", "declarations": [], "sources": []})
    class Capture:
        def request_json(self, prompt, schema, *args):
            assert ("The clique/complement Q quotient" in prompt) == spectral
            assert "at most half the proposal slots" in prompt
            assert schema["properties"]["proposals"]["maxItems"] == 4
            if spectral:
                assert "existing AST" in prompt and "not a durable helper_for binding" in prompt
            return {"proposals": []}, {}
    candidates, _ = proposals.propose_candidates(Capture(), {"research_family": family, "theorems": {}}, tmp_path / family, 0, limit=4)
    assert candidates == []


@pytest.mark.parametrize("url", ["https://math.mit.edu/~rstan/pubs/pubfiles/other.pdf", "https://people.clas.ufl.edu/avince/files/other.pdf", "https://journals.uwyo.edu/index.php/ela/article/download/1026/1026/1026", "https://dml.cz/other.pdf"])
def test_new_public_primary_locations_are_exact_only(url):
    with pytest.raises(ValueError): sources.paper_url(url)
