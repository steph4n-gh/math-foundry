"""Research packets preserve exact mathematics and fail closed on unsafe evidence."""
import hashlib
import io
import json
from pathlib import Path
import zipfile

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.export import research_packet as packet
from autonomous_math.dashboard.data_service import DashboardDataService


@pytest.fixture
def proof(tmp_path, monkeypatch):
    c = Conjecture.create(id="packet_proof", lhs=InvariantNode("order"), rel=">=", rhs=ConstantNode(0))
    source = tmp_path / "proof.lean"
    source.write_text("theorem packet_proof : True := by trivial\n")
    challenge = tmp_path / "challenge.lean"
    challenge.write_text("theorem packet_proof : True := by sorry\n")
    receipt = {"schema_version": 1, "status": "KERNEL_VERIFIED", "conjecture_id": c.id,
        "conjecture": c.to_dict(), "source_path": str(source), "source_sha256": packet._hash(source.read_bytes()),
        "challenge_path": str(challenge), "challenge_sha256": packet._hash(challenge.read_bytes()),
        "workspace_sha256": "a" * 64, "theorem_name": c.id, "axioms": [], "statement_checked": True,
        "lean_version": "Fixture compiler", "diagnostics": {"stderr": "PRIVATE_LOG_DO_NOT_EXPORT"}}
    receipt_path = tmp_path / "receipt.json"
    receipt_path.write_text(json.dumps(receipt))
    record = {"id": c.id, "conjecture": c.to_dict(), "status": "LEAN_CERTIFIED",
              "lean_proof": {"receipt_path": str(receipt_path)}}
    monkeypatch.setattr(packet, "validate_receipt", lambda path, identifier, fingerprints=None: (json.loads(Path(path).read_text()), None))
    def review():
        r = json.loads(receipt_path.read_text())
        identity = {"conjecture": record["conjecture"], "receipt_schema_version": r["schema_version"],
            "receipt_sha256": packet._hash(receipt_path.read_bytes()), "source_sha256": r["source_sha256"],
            "challenge_sha256": r["challenge_sha256"], "workspace_sha256": r["workspace_sha256"]}
        return {"id": c.id, "status": "awaiting_review", "fingerprint": packet._hash(json.dumps(identity, sort_keys=True, allow_nan=False).encode()),
                "uncertainties": ["Publication priority remains open."], "expert_review": {"status": "pending"}}
    return record, review, receipt_path


def unzip(raw):
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        return {name: archive.read(name) for name in archive.namelist()}


def test_packet_is_inspectable_exact_and_explicit_about_missing_evidence(proof, tmp_path):
    record, review, receipt_path = proof
    raw, manifest = packet.build_research_packet(record, review(), tmp_path)
    files = unzip(raw)
    assert set(files) == {"proof.lean", "challenge.lean", "receipt.json", "research.json", "README.md", "manifest.json"}
    report = json.loads(files["research.json"])
    receipt = json.loads(files["receipt.json"])
    assert report["conjecture"] == receipt["conjecture"] == record["conjecture"]
    assert "order counts vertices" in report["writeup"]["what"]
    assert "later proof" in report["writeup"]["why"]
    assert "No primary-literature text coverage" in " ".join(report["evidence_gaps"])
    assert report["review"]["status"] == "awaiting_review"
    assert "Lean guard:" in files["README.md"].decode()
    assert "no new Lean replay" in report["provenance"]["scope"]
    assert "PRIVATE_LOG_DO_NOT_EXPORT" not in b"".join(files.values()).decode()
    assert report["provenance"]["receipt_sha256"] == packet._hash(receipt_path.read_bytes())
    for entry in manifest["files"]:
        assert entry["sha256"] == packet._hash(files[entry["path"]])
        assert entry["bytes"] == len(files[entry["path"]])


def test_saved_writeup_is_reused_and_no_review_does_not_block_export(proof, tmp_path):
    record, _, receipt_path = proof
    record["conjecture"].setdefault("metadata", {})["writeup"] = "Existing checked theorem writeup."
    receipt = json.loads(receipt_path.read_text())
    receipt["conjecture"] = record["conjecture"]
    receipt_path.write_text(json.dumps(receipt))
    raw, _ = packet.build_research_packet(record, None, tmp_path)
    report = json.loads(unzip(raw)["research.json"])
    assert report["writeup"]["what"].startswith("Lean proves ")
    assert report["writeup"]["what"].endswith("Existing checked theorem writeup.")
    assert report["review"]["status"] == "awaiting_review"
    assert any("No saved review fingerprint" in gap for gap in report["evidence_gaps"])


def test_curated_comparison_is_readable_and_markdown_html_is_escaped(proof, tmp_path):
    record, make_review, _ = proof
    review = make_review()
    review["closest_results"] = [{"title": "Checked reference <script>bad()</script>", "theorem_id": "parent",
        "citation": "Existing checked library", "comparison": "An exact implication.", "relationship": "routine_consequence"}]
    files = unzip(packet.build_research_packet(record, review, tmp_path)[0])
    markdown = files["README.md"].decode()
    assert "An exact implication." in markdown
    assert "Existing checked library" in markdown
    assert "Checked theorem ID: parent" in markdown
    assert "<script>" not in markdown


def test_bound_excerpt_has_locator_version_hash_and_no_logs_or_full_paper(proof, tmp_path):
    record, make_review, _ = proof
    review = make_review()
    quote = "This exact source states a finite graph relation."
    source = {"source_id": "primary1", "source_type": "primary_literature", "text": quote + " Extra source context.",
        "locator": "PDF page 2, theorem 1", "version": "sha256 snapshot", "source_sha256": "b" * 64,
        "title": "A paper", "url": "https://example.org/paper.pdf"}
    source["text_sha256"] = packet._hash(source["text"].encode())
    attempt = tmp_path / "attempt"
    attempt.mkdir()
    source_pack = attempt / "source_pack.json"
    source_pack.write_text(json.dumps({"id": record["id"], "fingerprint": review["fingerprint"], "sources": [source]}))
    review["ai_review"] = {"status": "complete", "outcome": "possible_extension", "trace_path": str(attempt / "trace.json"),
        "source_pack_sha256": packet._hash(source_pack.read_bytes()), "error": "SECRET_RAW_STDERR",
        "comparisons": [{"source_id": "primary1", "quote": quote, "comparison": "A provisional comparison."}],
        "source_coverage": {"primary_literature": 1, "local_mathlib": 2}}
    files = unzip(packet.build_research_packet(record, review, tmp_path)[0])
    report = json.loads(files["research.json"])
    assert files["evidence/comparison-01.txt"].decode() == quote
    evidence = report["comparisons"][0]
    assert evidence["quote_binding"] == "matched saved source context"
    assert evidence["locator"] == source["locator"] and evidence["source_sha256"] == source["source_sha256"]
    assert "SECRET_RAW_STDERR" not in b"".join(files.values()).decode()
    assert "Extra source context" not in b"".join(files.values()).decode()
    assert report["review"]["status"] == "awaiting_review"
    assert "possible_extension" in files["README.md"].decode()


@pytest.mark.parametrize("change", ["source_changed", "wrong_ast", "stale_review", "source_symlink", "parent_symlink", "traversal", "oversized"])
def test_unsafe_or_mismatched_proof_fails_closed(proof, tmp_path, change):
    record, make_review, receipt_path = proof
    review = make_review()
    receipt = json.loads(receipt_path.read_text())
    source = Path(receipt["source_path"])
    if change == "source_changed": source.write_text("changed source")
    elif change == "wrong_ast": record["conjecture"]["id"] = "different"
    elif change == "stale_review": review["fingerprint"] = "old"
    elif change == "source_symlink":
        target = tmp_path / "other.lean"
        source.rename(target)
        source.symlink_to(target)
    elif change == "parent_symlink":
        link = tmp_path / "linked"
        link.symlink_to(tmp_path, target_is_directory=True)
        receipt["source_path"] = str(link / source.name)
    elif change == "traversal": receipt["source_path"] = str(tmp_path / "child" / ".." / source.name)
    elif change == "oversized": source.write_bytes(b"x" * (packet.MAX_FILE_BYTES + 1))
    if change in {"parent_symlink", "traversal"}: receipt_path.write_text(json.dumps(receipt))
    with pytest.raises(ValueError): packet.build_research_packet(record, review, tmp_path)


def test_untrusted_ai_paths_are_not_followed_and_missing_binding_is_visible(proof, tmp_path):
    record, make_review, _ = proof
    review = make_review()
    review["ai_review"] = {"status": "complete", "trace_path": "../private/trace.json", "source_pack_sha256": "unknown",
        "comparisons": [{"source_id": "unknown", "source_path": "/etc/passwd", "quote": "Unbound historical excerpt."}]}
    raw, _ = packet.build_research_packet(record, review, tmp_path)
    files = unzip(raw)
    report = json.loads(files["research.json"])
    assert any("Parent traversal" in gap for gap in report["evidence_gaps"])
    assert report["comparisons"][0]["quote_binding"] == "not independently bound in this packet"
    assert not any("passwd" in name or ".." in Path(name).parts for name in files)


def test_dashboard_packet_lookup_is_read_only_and_unknown_is_explicit(proof, tmp_path, monkeypatch):
    record, review, _ = proof
    service = DashboardDataService(data_dir=tmp_path)
    monkeypatch.setattr(service, "load_atlas", lambda: {"theorems": {record["id"]: record}})
    monkeypatch.setattr(service, "get_novelty_reviews", lambda atlas: {"records": [review()]})
    before = sorted(str(path.relative_to(tmp_path)) for path in tmp_path.rglob("*"))
    response = service.get_research_packet(record["id"])
    assert response["found"] and response["archive_base64"].startswith("UEsDB")
    assert service.get_research_packet("../../unknown")["found"] is False
    assert sorted(str(path.relative_to(tmp_path)) for path in tmp_path.rglob("*")) == before


def test_packet_http_route_preserves_attachment_and_failure_contract(proof, tmp_path, monkeypatch):
    from urllib.error import HTTPError
    from urllib.request import urlopen
    from autonomous_math.dashboard.server import run_dashboard
    record, review, _ = proof
    monkeypatch.setattr(DashboardDataService, "load_atlas", lambda self: {"theorems": {record["id"]: record}})
    monkeypatch.setattr(DashboardDataService, "get_novelty_reviews", lambda self, atlas: {"records": [review()]})
    server = run_dashboard(port=0, block=False, data_dir=tmp_path)
    try:
        base = f"http://127.0.0.1:{server.server_port}/api/research_packet/"
        with urlopen(base + record["id"]) as response:
            body = json.load(response)
            assert body["found"] and body["manifest"]["theorem_id"] == record["id"]
        with pytest.raises(HTTPError) as error:
            urlopen(base + "absent")
        assert error.value.code == 404
        assert json.load(error.value)["found"] is False
    finally:
        server.shutdown()
        server.server_close()


def test_foundation_writeup_matches_exact_ast_and_guard():
    from autonomous_math.core.ast import GuardPredicate
    c = Conjecture.create(id="colors", lhs=InvariantNode("chromatic_number"), rel="<=", rhs=InvariantNode("order"))
    record = {"id": c.id, "conjecture": c.to_dict()}
    unguarded = packet.proof_writeup(record)
    assert "give each vertex its own color" in unguarded["what"]
    assert "clique number" in unguarded["why"]
    record["conjecture"]["guard_predicate"] = GuardPredicate("is_bipartite").to_dict()
    guarded = packet.proof_writeup(record)
    assert "bipartite" in guarded["what"]
    assert "under the guard" in guarded["what"]
    assert "Every finite simple graph can be colored" not in guarded["what"]
    record["conjecture"]["rel"] = ">="
    assert "give each vertex its own color" not in packet.proof_writeup(record)["what"]


@pytest.mark.parametrize("invariant, expected", [
    ("parity_code_dimension", "independent binary information"),
    ("parity_code_distance", "smallest support"),
    ("unique_neighbor_radius", "parity check"),
    ("graph_energy", "spectral quantities"),
    ("density", "local neighbor counts"),
])
def test_family_writeups_explain_specific_mathematical_value(invariant, expected):
    c = Conjecture.create(id="family", lhs=InvariantNode(invariant), rel=">=", rhs=ConstantNode(0))
    writeup = packet.proof_writeup({"id": c.id, "conjecture": c.to_dict()})
    assert writeup["what"].startswith("Lean proves ")
    assert expected in writeup["why"]
    assert "not mathematical originality" in writeup["scope"]


def test_prospective_model_explanation_is_not_certified_what():
    c = Conjecture.create(id="proposal", lhs=InvariantNode("order"), rel=">=", rhs=ConstantNode(0))
    record = {"id": c.id, "conjecture": c.to_dict()}
    record["conjecture"]["metadata"] = {"origin": "codex_proposal", "explanation": "We propose an unrestricted decoding breakthrough."}
    writeup = packet.proof_writeup(record)
    assert "breakthrough" not in writeup["what"] + writeup["why"]
    assert writeup["model_commentary"] == record["conjecture"]["metadata"]["explanation"]
    assert "not part of the certified statement" in writeup["commentary_scope"]
