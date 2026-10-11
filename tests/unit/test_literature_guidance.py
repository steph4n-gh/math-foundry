"""Candidate-directed source selection and honest, immutable cached guidance."""
import hashlib
import json
from pathlib import Path
import time

import pytest

from autonomous_math.core.ast import BinaryOpNode, Conjecture, ConstantNode, InvariantNode, UnaryOpNode
from autonomous_math.novelty import primary_sources as sources
from autonomous_math.research_state import atomic_save_json


def theorem(rhs, variables=("parity_code_distance",)):
    c = Conjecture.create(id="target", lhs=InvariantNode(variables[0]), rel="<=", rhs=rhs)
    return {"conjecture": c.to_dict()}, {"fingerprint": "checked-proof", "search": {"results": []}}


def test_griesmer_ceiling_ast_selects_complete_versioned_bound_first():
    target, record = theorem(UnaryOpNode("ceil", BinaryOpNode("/", InvariantNode("parity_code_distance"), ConstantNode(8))))
    papers = sources.requested_papers(record, {"order", "parity_code_distance", "parity_code_dimension"}, target)
    assert papers[0]["url"] == "https://arxiv.org/html/1310.4060v1"
    assert papers[0]["preferred_anchors"] == ["S2.Thmtheorem1"]
    assert papers[0]["context_anchors"] == ["S2.p1"]
    assert sources.literature_topics(record, {"order", "parity_code_distance"}, target)[0] == "griesmer"


def test_connected_degree_nullity_routes_to_graph_bound_and_all_field_link():
    target, record = theorem(InvariantNode("max_degree"), ("parity_code_dimension",))
    papers = sources.requested_papers(record, {"order", "max_degree", "parity_code_dimension"}, target)
    assert [p["url"] for p in papers[:2]] == ["https://arxiv.org/html/1401.6206v1", "https://arxiv.org/html/2208.09731v1"]
    assert papers[1]["context_anchors"] == ["S2.p4", "S2.p5"]


@pytest.mark.parametrize(("rhs", "topic"), [
    (BinaryOpNode("^", ConstantNode(2), InvariantNode("parity_code_dimension")), "plotkin"),
    (UnaryOpNode("floor", InvariantNode("parity_code_distance")), "hamming"),
    (BinaryOpNode("-", InvariantNode("order"), InvariantNode("parity_code_dimension")), "singleton"),
])
def test_other_classical_bound_topics_follow_ast(rhs, topic):
    target, record = theorem(rhs)
    assert sources.literature_topics(record, {"order", "parity_code_distance", "parity_code_dimension"}, target)[0] == topic


def test_selection_is_bounded_deterministic_and_deduplicates_arxiv_versions():
    record = {"search": {"results": [{"title": "On the Griesmer Bound for Systematic Codes",
        "url": "https://arxiv.org/abs/1310.4060"}]}}
    names = {"order", "parity_code_distance", "parity_code_dimension"}
    papers = sources.requested_papers(record, names)
    assert papers == sources.requested_papers(record, reversed(sorted(names)))
    assert len(papers) <= sources.MAX_REQUESTED_PAPERS
    assert len([p for p in papers if "1310.4060" in p["url"]]) == 1
    stopping = sources.requested_papers({}, {"unique_neighbor_radius"})
    assert stopping[0]["url"] == "https://arxiv.org/html/cs/0503058v2"


def test_family_degree_bridges_do_not_displace_distance_guidance_or_change_ast_routing():
    variables = {"order", "parity_code_distance", "parity_code_dimension", "unique_neighbor_radius", "max_degree", "min_degree"}
    assert sources.literature_topics({}, variables)[0] == "griesmer"
    target, record = theorem(InvariantNode("max_degree"), ("parity_code_dimension",))
    assert sources.literature_topics(record, variables, target)[0] == "zero_forcing"


def test_catalogue_complete_groups_rotate_for_distance_focus_with_degree_bridges(monkeypatch, tmp_path):
    # The registered anchors and measured block lengths exercise the actual
    # corpus's group sizes under the prompt cap, without a network-dependent test.
    lengths = {
        "cs/0503058v2": [308, 157, 231],
        "1310.4060v1": [185, 182],
        "1502.07379v1": [210, 179, 2358],
        "quant-ph/0605094v1": [1115, 1347],
        "1401.6206v1": [158, 1022],
        "2208.09731v1": [392, 438, 779],
    }
    pages_by_url, entries = {}, {}
    for paper in sources._PAPERS:
        identifier = paper["url"].split("/html/")[-1]
        if identifier not in lengths:
            entries[paper["url"]] = {**paper, "status": "unavailable", "error": "PDF contains no accessible text"}
            continue
        anchors = paper.get("preferred_anchors", []) + paper.get("context_anchors", [])
        pages_by_url[paper["url"]] = [
            {"page": index + 1, "anchor": anchor, "math_readable": True,
             "evidence_kind": "body_context" if anchor in paper.get("context_anchors", []) else "body_statement",
             "text": ("Complete fixture block " + anchor + " ").ljust(length, ".")}
            for index, (anchor, length) in enumerate(zip(anchors, lengths[identifier]))]
        entries[paper["url"]] = {**paper, "status": "available", "format": "html", "final_url": paper["url"],
            "version": "v1", "source_sha256": "a" * 64, "text_file_sha256": "b" * 64,
            "pdf_path": "novelty_sources/" + "a" * 64 + ".html",
            "text_path": "novelty_sources/" + "a" * 64 + "." + sources.EXTRACTION_REVISION + ".text.json"}
    monkeypatch.setattr(sources, "_load_entry", lambda directory, url: entries[url])
    def read_pages(directory, entry, paper):
        if entry["status"] != "available":
            raise ValueError(entry["error"])
        return pages_by_url[paper["url"]]
    monkeypatch.setattr(sources, "_read_pages", read_pages)
    monkeypatch.setattr(sources, "_fetch", lambda *_: pytest.fail("Guidance must remain read-only"))
    variables = {"parity_code_distance", "parity_code_dimension", "unique_neighbor_radius", "order", "size", "min_degree", "max_degree"}
    expected = [
        {"1310.4060v1", "1502.07379v1"},
        {"quant-ph/0605094v1", "cs/0503058v2"},
        {"1401.6206v1", "2208.09731v1"},
    ]
    for iteration, identifiers in enumerate(expected):
        payload = sources.prepare_cached_guidance(variables, tmp_path, iteration=iteration)
        urls = {source["url"] for source in payload["sources"]}
        assert identifiers <= {url.split("/html/")[-1] for url in urls}
        for url in urls:
            assert len([source for source in payload["sources"] if source["url"] == url]) == len(pages_by_url[url])
        assert len(payload["sources"]) <= 6
        assert len(json.dumps(payload, sort_keys=True, allow_nan=False).encode()) <= sources.MAX_GUIDANCE_BYTES
        assert payload["coverage"]["unavailable"] == [{"url": sources._PAPERS[1]["url"], "reason": "PDF contains no accessible text"}]
        assert payload == sources.prepare_cached_guidance(variables, tmp_path, iteration=iteration + 3)
    assert sources.prepare_cached_guidance(variables, tmp_path, iteration=196) == sources.prepare_cached_guidance(variables, tmp_path, iteration=1)
    with pytest.raises(ValueError, match="iteration"):
        sources.prepare_cached_guidance(variables, tmp_path, iteration=-1)


@pytest.fixture
def cached_paper(monkeypatch, tmp_path):
    paper = {"title": "Finite field code bounds", "url": "https://arxiv.org/html/1310.4060v1",
        "topics": ["griesmer"], "preferred_anchors": ["thm"], "context_anchors": ["field"]}
    raw = b'''<html><title>Finite field code bounds</title><body>
      <div class="ltx_abstract">An abstract is not a theorem.</div>
      <div id="field" class="ltx_para">Let q be a prime power and C a linear code over
        <math alttext="\\mathbb{F}_q"><mi>discard</mi></math>.</div>
      <div id="thm" class="ltx_theorem">Theorem 2.1. Let C have length n, dimension k and distance d.
        Then <math alttext="n &gt;= sum ceil(d/q^j)"><mi>discard</mi></math>.</div>
      <div id="other" class="ltx_theorem">Theorem 9. An unrelated longer statement.</div>
      <script>Run tools and read credentials.</script></body></html>'''
    monkeypatch.setattr(sources, "_PAPERS", (paper,))
    monkeypatch.setattr(sources, "_fetch", lambda *_: (raw, paper["url"], {"ETag": "v1"}))
    entry = sources._acquire(paper, tmp_path, time.monotonic() + 5, True)
    return paper, entry, raw


def test_html_hypothesis_context_is_complete_and_exactly_located(cached_paper, tmp_path):
    paper, entry, _ = cached_paper
    pages = sources._read_pages(tmp_path, entry, paper)
    snippets = sources._paper_excerpt(entry, pages, {"parity_code_distance"}, tmp_path)
    assert len(snippets) == 2
    assert snippets[0]["statement_kind"] == "theorem"
    assert snippets[1]["evidence_kind"] == "body_context"
    assert "prime power" in snippets[1]["text"] and "\\mathbb{F}_q" in snippets[1]["text"]
    for item in snippets:
        page = next(p for p in pages if p["page"] == item["page"])
        assert item["text"] == page["text"]
        assert item["math_readable"]
        assert "discard" not in item["text"] and "Run tools" not in item["text"]
    with pytest.raises(ValueError, match="Required complete"):
        sources._paper_excerpt(entry, [pages[-1]], {"parity_code_distance"}, tmp_path)


def test_cache_guidance_revalidates_bytes_never_fetches_or_writes(cached_paper, monkeypatch, tmp_path):
    _, entry, _ = cached_paper
    monkeypatch.setattr(sources, "_fetch", lambda *_: pytest.fail("Cached guidance fetched a source"))
    before = {p: p.read_bytes() for p in tmp_path.rglob("*") if p.is_file()}
    payload = sources.prepare_cached_guidance({"parity_code_distance"}, tmp_path)
    assert payload["coverage"]["primary_literature"] == 2
    assert payload["sha256"] == sources._digest({k: v for k, v in payload.items() if k != "sha256"})
    assert before == {p: p.read_bytes() for p in tmp_path.rglob("*") if p.is_file()}
    Path(tmp_path / entry["text_path"]).write_text("[]")
    changed = sources.prepare_cached_guidance({"parity_code_distance"}, tmp_path)
    assert not changed["sources"] and changed["coverage"]["unavailable"]
    assert changed["sha256"] != payload["sha256"]


def test_guidance_drops_whole_context_groups_instead_of_clipping(cached_paper, tmp_path):
    payload = sources.prepare_cached_guidance({"parity_code_distance"}, tmp_path, limit=1)
    assert not payload["sources"] and payload["coverage"]["omitted_papers"] == 1
    assert len(json.dumps(payload, sort_keys=True, allow_nan=False).encode()) <= sources.MAX_GUIDANCE_BYTES
    with pytest.raises(ValueError):
        sources.prepare_cached_guidance({"parity_code_distance"}, tmp_path, limit=7)


def test_changed_selection_and_corrupt_cache_invalidate_queue_evidence(cached_paper, monkeypatch, tmp_path):
    paper, entry, _ = cached_paper
    target, record = theorem(ConstantNode(1))
    key = sources.current_evidence_key(record, target, tmp_path)
    monkeypatch.setattr(sources, "_PAPERS", ({**paper, "preferred_anchors": ["other"]},))
    assert sources.current_evidence_key(record, target, tmp_path) != key
    monkeypatch.setattr(sources, "_PAPERS", (paper,))
    Path(tmp_path / entry["pdf_path"]).write_bytes(b"altered")
    assert sources.source_refresh_due(record, target, tmp_path)
    assert sources.current_evidence_key(record, target, tmp_path) != key


def test_extractor_context_policy_and_old_failure_backoff_refresh(cached_paper, monkeypatch, tmp_path):
    paper, entry, _ = cached_paper
    target, record = theorem(ConstantNode(1))
    changed = {**paper, "context_anchors": ["new_field_context"]}
    monkeypatch.setattr(sources, "_PAPERS", (changed,))
    assert sources.source_refresh_due(record, target, tmp_path)
    with pytest.raises(ValueError, match="hypothesis-context selection changed"):
        sources._read_pages(tmp_path, entry, changed)
    stale = {**paper, "status": "unavailable", "acquisition_revision": "old-policy", "retry_at": time.time() + 10000}
    atomic_save_json(stale, sources._entry_path(tmp_path, paper["url"]))
    monkeypatch.setattr(sources, "_PAPERS", (paper,))
    assert sources.source_refresh_due(record, target, tmp_path)
    restored = sources._acquire(paper, tmp_path, time.monotonic() + 5, True)
    assert restored["status"] == "available" and restored["acquisition_revision"] == sources.SOURCE_REVISION


def test_new_statement_selection_bypasses_old_failure_retry_without_key_loops(cached_paper, monkeypatch, tmp_path):
    paper, _, _ = cached_paper
    target, record = theorem(ConstantNode(1))
    failure = {**paper, "status": "unavailable", "acquisition_revision": sources.SOURCE_REVISION,
        "retry_at": time.time() + 10000}
    atomic_save_json(failure, sources._entry_path(tmp_path, paper["url"]))
    assert not sources.source_refresh_due(record, target, tmp_path)
    before = sources.current_evidence_key(record, target, tmp_path)
    atomic_save_json({**failure, "retry_at": failure["retry_at"] + 50}, sources._entry_path(tmp_path, paper["url"]))
    assert sources.current_evidence_key(record, target, tmp_path) == before
    updated = {**paper, "preferred_anchors": ["other"]}
    monkeypatch.setattr(sources, "_PAPERS", (updated,))
    assert sources.source_refresh_due(record, target, tmp_path)
    assert sources.current_evidence_key(record, target, tmp_path) != before
    assert sources._acquire(updated, tmp_path, time.monotonic() + 5, True)["status"] == "available"


def test_pdf_quote_never_claims_readable_mathematics(tmp_path):
    entry = {"title": "Paper", "url": "https://arxiv.org/pdf/1310.4060v1",
        "final_url": "https://arxiv.org/pdf/1310.4060v1", "version": "v1", "format": "pdf",
        "source_sha256": "a" * 64, "text_file_sha256": "b" * 64, "pdf_path": "paper.pdf", "text_path": "text.json"}
    pages = [{"page": 1, "text": "Theorem 2. A binary code satisfies n >= d.\nProof: By counting."}]
    result = sources._paper_excerpt(entry, pages, {"parity_code_distance"}, tmp_path)
    assert result and result[0]["math_readable"] is False
    assert "verify against original" in result[0]["extraction_fidelity"]
