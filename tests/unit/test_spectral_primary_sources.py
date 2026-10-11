"""Spectral comparisons retain complete hypotheses and honest byte provenance."""
import hashlib
import json

import pytest

from autonomous_math.novelty import primary_sources as sources


def test_spectral_targets_route_to_their_actual_matrix_field():
    q = {"signless_laplacian_spectral_radius", "average_degree", "max_degree", "order"}
    energy = {"graph_energy", "normalized_laplacian_spectral_gap", "average_degree"}
    assert sources.literature_topics({}, q)[:2] == ["signless_irregularity", "signless_local_refinements"]
    assert sources.requested_papers({}, q)[0]["url"] == "https://arxiv.org/html/1407.4285v1"
    assert sources.literature_topics({}, energy)[:2] == ["normalized_energy_bridge", "energy_lower_bounds"]
    assert not any("zero_forcing" in paper.get("topics", []) for paper in sources.requested_papers({}, energy))


def entry(paper):
    fmt = "html" if "/html/" in paper["url"] else "pdf"
    digest = hashlib.sha256(paper["url"].encode()).hexdigest()
    return {**paper, "status": "available", "format": fmt, "final_url": paper["url"],
            "version": "SHA256 snapshot " + digest, "source_sha256": digest,
            "text_file_sha256": "b" * 64, "extraction_revision": sources.EXTRACTION_REVISION,
            "pdf_path": "novelty_sources/" + digest + "." + fmt,
            "text_path": "novelty_sources/" + digest + "." + sources.EXTRACTION_REVISION + ".text.json"}


def test_registered_pdf_windows_are_complete_exact_and_never_math_readable(tmp_path):
    paper = next(p for p in sources._PAPERS if p["title"] == "A Very Short Proof for a Lower Bound for Energy of Graphs")
    blocks = []
    for spec in paper["pdf_context_markers"]:
        blocks.append({"page": spec["page"], "text": "header\n" + spec["start"] + "\nExact complete body.\n" + spec["end"] + "\nfooter"})
    snippets = sources._paper_excerpt(entry(paper), blocks, {"graph_energy"}, tmp_path)
    assert len(snippets) == 2
    assert snippets[-1]["comparison_baselines"] == ["energy_spectral_radius"]
    assert snippets[-1]["evidence_kind"] == "body_statement"
    assert snippets[-1]["statement_kind"] == "unknown"  # A remark is not relabelled a theorem.
    for source in snippets:
        original = next(p["text"] for p in blocks if p["page"] == source["page"])
        assert original[source["excerpt_start"]:source["excerpt_start"] + len(source["text"])] == source["text"]
        assert hashlib.sha256(source["text"].encode()).hexdigest() == source["text_sha256"]
        assert source["math_readable"] is False
    with pytest.raises(ValueError, match="start unavailable"):
        sources._paper_excerpt(entry(paper), blocks[:1], {"graph_energy"}, tmp_path)
    ambiguous = [{**blocks[0], "text": blocks[0]["text"] * 2}, blocks[1]]
    with pytest.raises(ValueError, match="ambiguous"):
        sources._paper_excerpt(entry(paper), ambiguous, {"graph_energy"}, tmp_path)


@pytest.mark.parametrize("url", [
    "https://www.math.ucsd.edu/~fan/other.pdf",
    "https://match.pmf.kg.ac.rs/electronic_versions/Match84/n2/other.pdf",
    "https://dspace.stir.ac.uk/bitstream/1893/18513/1/other.pdf",
    "https://fanchung.ucsd.edu/cbms.pdf?token=1",
])
def test_spectral_allowlist_does_not_expand_to_hosts(url):
    with pytest.raises(ValueError):
        sources.paper_url(url)


def test_newer_unacquired_comparators_are_machine_readable_gaps(monkeypatch, tmp_path):
    monkeypatch.setattr(sources, "_PAPERS", ())
    q = {"signless_laplacian_spectral_radius", "average_degree"}
    payload = sources.prepare_cached_guidance(q, tmp_path)
    gaps = payload["coverage"]["comparison_gaps"]
    assert len(gaps) == 2 and all(gap["http_status"] == 403 for gap in gaps)
    assert "irregular graphs" in gaps[0]["title"]
    assert "5214733" in gaps[1]["url"]
    assert not payload["sources"]
    assert "signless_local_refinements" in payload["coverage"]["unregistered_primary_topics"]
    assert not sources.prepare_cached_guidance({"graph_energy"}, tmp_path)["coverage"]["comparison_gaps"]
    monkeypatch.setattr(sources, "pinned_mathlib_sources", lambda *_: ([], []))
    monkeypatch.setattr(sources, "targeted_mathlib_sources", lambda *_: ([], []))
    monkeypatch.setattr(sources, "current_evidence_key", lambda *_: "fixed")
    assert sources.prepare_sources({}, {}, q, tmp_path, 0, online=False)["coverage"]["comparison_gaps"] == gaps


def test_measured_complete_spectral_groups_rotate_within_the_existing_budget(monkeypatch, tmp_path):
    # Block lengths measured from the acquired six-paper corpus. Registered
    # anchors/windows and full metadata exercise real group counts/budget,
    # without depending on network access or the experiment directory.
    lengths = {
        "Spectral radius minus average degree: a better bound": [134, 317, 303],
        "Energies of Hypergraphs": [207, 903, 565, 791, 501, 377],
        "Eigenvalue bounds for the signless Laplacian": [1334, 230, 191],
        "Graph energy estimates via the Chebyshev functional": [147, 195, 146, 318, 162],
        "Lectures on Spectral Graph Theory": [665, 320],
        "A Very Short Proof for a Lower Bound for Energy of Graphs": [858, 612],
    }
    entries, pages, sizes = {}, {}, {}
    for paper in sources._PAPERS:
        if paper["title"] not in lengths:
            continue
        e = entry(paper)
        entries[paper["url"]] = e
        blocks = []
        if e["format"] == "html":
            anchors = paper.get("preferred_anchors", []) + paper.get("context_anchors", [])
            for index, (anchor, length) in enumerate(zip(anchors, lengths[paper["title"]])):
                blocks.append({"page": index + 1, "anchor": anchor, "math_readable": True,
                               "evidence_kind": "body_context" if anchor in paper.get("context_anchors", []) else "body_statement",
                               "text": ("Complete exact block " + anchor + " ").ljust(length, ".")})
        else:
            for spec, length in zip(paper["pdf_context_markers"], lengths[paper["title"]]):
                text = (spec["start"] + "\n").ljust(max(length - len(spec["end"]), len(spec["start"]) + 2), ".") + spec["end"]
                blocks.append({"page": spec["page"], "text": text})
        pages[paper["url"]] = blocks
        sizes[paper["url"]] = len(blocks)
    monkeypatch.setattr(sources, "_load_entry", lambda directory, url: entries.get(url, {}))
    def read_pages(directory, e, paper):
        if paper["url"] not in pages:
            raise ValueError("Not cached")
        return pages[paper["url"]]
    monkeypatch.setattr(sources, "_read_pages", read_pages)
    monkeypatch.setattr(sources, "_fetch", lambda *_: pytest.fail("Cached guidance must not acquire"))
    variables = {"graph_energy", "normalized_laplacian_spectral_gap", "signless_laplacian_spectral_radius", "average_degree", "max_degree", "order"}
    seen = set()
    for iteration in range(5):
        payload = sources.prepare_cached_guidance(variables, tmp_path, iteration=iteration)
        assert len(payload["sources"]) <= 6
        assert len(json.dumps(payload, sort_keys=True, allow_nan=False).encode()) <= sources.MAX_GUIDANCE_BYTES
        assert payload["sha256"] == sources._digest({k: v for k, v in payload.items() if k != "sha256"})
        # Each complete paper group has one byte identity and every selected
        # context keeps the same raw-artifact hash plus its individual text hash.
        for url, count in sizes.items():
            digest = hashlib.sha256(url.encode()).hexdigest()
            selected = [s for s in payload["sources"] if s["source_sha256"] == digest]
            if selected:
                assert len(selected) == count
                assert all(s["cache_files"][0]["sha256"] == digest for s in selected)
        seen.update(token for source in payload["sources"] for token in source.get("comparison_baselines", []))
    assert seen == {"signless_degree_square", "signless_rms", "signless_max_degree", "normalized_regular_bridge",
                    "energy_spectral_radius", "energy_sqrt_edges", "energy_edges_over_radius", "energy_regular_order"}
