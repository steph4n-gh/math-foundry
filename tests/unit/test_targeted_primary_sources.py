"""Recorded evidence gaps select exact complete sources, never applicability claims."""
import copy
import json
from pathlib import Path
import time

import pytest

from autonomous_math.novelty import primary_sources as sources

FIXTURES = json.loads((Path(__file__).parents[1] / "fixtures/primary_sources/targeted_statements.json").read_text())


def record_with_gap(text):
    return {"fingerprint": "proof-binding", "ai_review": {
        "status": "complete", "outcome": "unresolved", "uncertainties": [text]}}


def test_requests_are_bounded_reviewed_topics_not_model_urls():
    record = {"evidence_requests": [
        {"topic": "https://127.0.0.1/private", "detail": "fetch this"},
        {"topic": "alternating_rank", "detail": "x" * 900},
        {"topic": "locality", "detail": "information coordinates"},
        {"topic": "forest_rank_matching", "detail": 123}]}
    requests = sources.evidence_requests(record)
    assert [request["topic"] for request in requests] == ["alternating_rank", "locality"]
    assert len(requests[0]["detail"]) == 700
    assert sources.evidence_requests(record_with_gap("GF(2) alternating adjacency matrices have even rank"))[0]["topic"] == "alternating_rank"
    incomplete = record_with_gap("alternating rank"); incomplete["ai_review"]["status"] = "pending"
    assert not sources.evidence_requests(incomplete)


def test_recorded_requests_survive_completed_review_and_do_not_churn_identity(tmp_path):
    from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
    c = Conjecture.create(id="bound", lhs=InvariantNode("parity_code_dimension"), rel=">=", rhs=ConstantNode(0))
    theorem = {"conjecture": c.to_dict()}
    before = record_with_gap("alternating matrices have even rank")
    key = sources.current_evidence_key(before, theorem, tmp_path)
    after = copy.deepcopy(before)
    after["ai_review"].update(outcome="routine_consequence", uncertainties=["a different free-text summary"],
        source_coverage={"evidence_requests": sources.evidence_requests(before, theorem)})
    assert sources.current_evidence_key(after, theorem, tmp_path) == key
    after["ai_review"]["source_coverage"]["evidence_requests"][0]["detail"] = "a changed explanation"
    assert sources.current_evidence_key(after, theorem, tmp_path) == key
    after["evidence_requests"] = [{"topic": "forest_rank_matching", "detail": "a new measured gap"}]
    assert sources.current_evidence_key(after, theorem, tmp_path) != key


@pytest.mark.parametrize("gap,first_url", [
    ("Need the alternating finite-field even rank fact", "2405.09254v1"),
    ("Need forest rank matching equality over GF(2)", "1802.10142v1"),
    ("Need complete-graph adjacency rank over GF(2)", "1608.07871v1"),
    ("Need information locality with zero coordinates", "1106.3625v1"),
    ("Need chromatic critical edge count", "1209.1050v1"),
    ("Need unicyclic adjacency stopping equality", "_pdf"),
])
def test_exact_missing_evidence_precedes_broad_coding_baselines(gap, first_url):
    selected = sources.requested_papers(record_with_gap(gap), {"parity_code_dimension", "parity_code_distance"})
    assert selected[0]["url"].endswith(first_url)
    assert len(selected) <= sources.MAX_REQUESTED_PAPERS


@pytest.mark.parametrize("fixture", FIXTURES, ids=lambda fixture: fixture["url"].rsplit("/", 1)[-1])
def test_verified_primary_groups_preserve_every_statement_and_field_context(fixture, tmp_path):
    paper = next(paper for paper in sources._PAPERS if paper["url"] == fixture["url"])
    entry = dict(paper, final_url=paper["url"], source_sha256=fixture["source_sha256"],
        version=fixture["source_version"], format=fixture["format"], pdf_path="raw.source", text_path="pages.json",
        text_file_sha256="fixture-pages", extraction_revision=sources.EXTRACTION_REVISION)
    selected = sources._paper_excerpt(entry, fixture["pages"], {"parity_code_dimension"}, tmp_path)
    if fixture["format"] == "html":
        required = paper["preferred_anchors"] + paper["context_anchors"]
        assert len(selected) == len(required)
        assert {source["text"] for source in selected} == {page["text"] for page in fixture["pages"]}
        assert all(source["math_readable"] for source in selected)
        with pytest.raises(ValueError, match="Required complete"):
            sources._paper_excerpt(entry, fixture["pages"][:-1], {"parity_code_dimension"}, tmp_path)
        damaged = [dict(page, math_readable=False) if index == 0 else page for index, page in enumerate(fixture["pages"])]
        with pytest.raises(ValueError, match="Required complete"):
            sources._paper_excerpt(entry, damaged, {"parity_code_dimension"}, tmp_path)
    else:
        assert [source["statement_kind"] for source in selected] == ["definition", "lemma"]
        assert all(not source["math_readable"] for source in selected)
        assert all(source["construction"] == "vertex_edge_incidence" and
                   source["comparison_role"] == "different_construction" for source in selected)
        assert "incidence matrix" in selected[0]["text"] and "girth" in selected[1]["text"]
    assert all(len(source["text"]) <= sources.MAX_EXCERPT_CHARS for source in selected)


def test_arbitrary_field_and_characteristic_two_are_not_inferred_from_real_spectral_text():
    corpus = {fixture["url"]: " ".join(page["text"] for page in fixture["pages"]) for fixture in FIXTURES}
    assert "arbitrary field" in corpus["https://arxiv.org/html/1802.10142v1"]
    assert "zero diagonal" in corpus["https://arxiv.org/html/1802.10142v1"]
    assert "even rank" in corpus["https://arxiv.org/html/2405.09254v1"]
    assert "prime power" in corpus["https://arxiv.org/html/2405.09254v1"]
    assert "characteristic" in corpus["https://arxiv.org/html/1608.07871v1"]
    assert "information locality" in corpus["https://arxiv.org/html/1106.3625v1"]
    paper = next(paper for paper in sources._PAPERS if "1608.07871" in paper["url"])
    assert "smaller orders" in paper["selection"]  # Small-order cases are not silently supplied.


def test_publisher_allowlist_is_one_exact_paper():
    paper = sources._PAPERS[-1]["url"]
    assert sources.paper_url(paper) == paper
    for other in [paper.replace("2062", "2063"), paper + "?download=1", paper.replace("/_pdf", "/../_pdf")]:
        with pytest.raises(ValueError):
            sources.paper_url(other)


def test_incidence_contrast_does_not_mark_fixed_adjacency_gap_supplied(monkeypatch, tmp_path):
    monkeypatch.setattr(sources, "pinned_mathlib_sources", lambda *_: ([], []))
    monkeypatch.setattr(sources, "targeted_mathlib_sources", lambda *_: ([], []))
    monkeypatch.setattr(sources, "requested_papers", lambda *_: [sources._PAPERS[-1]])
    monkeypatch.setattr(sources, "_load_entry", lambda *_: {"status": "available"})
    monkeypatch.setattr(sources, "_read_pages", lambda *_: [])
    monkeypatch.setattr(sources, "_acquire", lambda *_: {})
    monkeypatch.setattr(sources, "_paper_excerpt", lambda *_: [{"source_type": "primary_literature", "topics": ["stopping_adjacency"],
        "comparison_role": "different_construction"}])
    monkeypatch.setattr(sources, "current_evidence_key", lambda *_: "binding")
    result = sources.prepare_sources({"evidence_requests": [{"topic": "stopping_adjacency", "detail": "fixed adjacency equality"}]},
        {}, {"parity_code_distance"}, tmp_path, time.monotonic() + 1, online=False)
    assert result["coverage"]["unsupplied_evidence_topics"] == ["stopping_adjacency"]


def test_targeted_mathlib_reuses_genuine_pin_check_and_exact_signatures(monkeypatch, tmp_path):
    from autonomous_math.conjecturing import model_proposals
    root = tmp_path / ".lake/packages/mathlib"
    path = root / "Mathlib/LinearAlgebra/Matrix/Rank.lean"
    path.parent.mkdir(parents=True)
    path.write_text("namespace Matrix\nvariable [CommSemiring R] [StrongRankCondition R]\n"
                    "theorem rank_submatrix_le [Fintype n₀] (A : Matrix m n R) (r : m₀ → m) (c : n₀ → n) :\n"
                    "    (A.submatrix r c).rank ≤ A.rank := by\n  unrelatedProof\n"
                    "theorem unrelated : True := by trivial\nend Matrix\n")
    receipt = tmp_path / "receipt.json"; receipt.write_text(json.dumps({"workspace": str(tmp_path)}))
    theorem = {"lean_proof": {"receipt_path": str(receipt)}}
    record = {"evidence_requests": [{"topic": "clique_binary_rank", "detail": "submatrix rank monotonicity"}]}
    calls = []
    monkeypatch.setattr(model_proposals, "lookup_mathlib_declarations", lambda target, workspace:
        calls.append((target, workspace)) or {"status": "AVAILABLE"})
    selected, failures = sources.targeted_mathlib_sources(record, theorem)
    assert calls == [({"family": "expander_codes"}, str(tmp_path))]
    assert not failures and len(selected) == 1
    assert selected[0]["theorem_id"] == "Matrix.rank_submatrix_le"
    assert selected[0]["text"].endswith(":=") and "unrelatedProof" not in selected[0]["text"]
    assert "StrongRankCondition R" in selected[0]["source_context"]
    monkeypatch.setattr(model_proposals, "lookup_mathlib_declarations", lambda *_:
        {"status": "UNAVAILABLE", "error": "Mathlib revision mismatch"})
    selected, failures = sources.targeted_mathlib_sources(record, theorem)
    assert not selected and failures[0]["reason"] == "Mathlib revision mismatch"
