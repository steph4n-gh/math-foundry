"""Bounded public text, exact cache bindings and offline behavior."""
import hashlib
import json
from pathlib import Path
import time
import urllib.error

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.novelty import primary_sources as sources
from autonomous_math.research_state import atomic_save_json


def target():
    c=Conjecture.create(id="coding",lhs=InvariantNode("parity_code_distance"),rel=">=",rhs=ConstantNode(1))
    return {"conjecture":c.to_dict()}, {"fingerprint":"exact-proof","search":{"results":[]}}


@pytest.fixture
def public_paper(monkeypatch,tmp_path):
    calls=[]
    pages=[{"page":1,"text":"On the Stopping Distance and the Stopping Redundancy of Codes\nDefinition 1. A stopping set has no row of weight one.\nTheorem 1. The stopping distance is at most the minimum distance.\nProof: Every support is a stopping set."}]
    def fetch(url,deadline):
        calls.append(url)
        return b"%PDF-1.4\nfixture source bytes",url,{"ETag":"version-one"}
    monkeypatch.setattr(sources,"_fetch",fetch)
    monkeypatch.setattr(sources,"_extract_pdf",lambda *_:pages)
    monkeypatch.setattr(sources,"pinned_mathlib_sources",lambda *_:([],[]))
    monkeypatch.setattr(sources,"_PAPERS",(dict(sources._PAPERS[0],url="https://arxiv.org/pdf/cs/0503058v2"),))
    return calls,pages


@pytest.mark.parametrize("url",["http://arxiv.org/pdf/2401.12345", "https://127.0.0.1/a.pdf",
    "https://arxiv.org@evil.example/a.pdf", "https://arxiv.org:444/pdf/2401.12345", "https://arxiv.org/pdf/2401.12345?x=1",
    "https://www.cs.yale.edu/homes/spielman/PAPERS/%2e%2e/a.pdf", "https://www.cs.yale.edu/index.html"])
def test_disallowed_urls_and_redirects_are_rejected(url):
    with pytest.raises(ValueError):sources.paper_url(url)
    with pytest.raises(ValueError):sources._SafeRedirect().redirect_request(None,None,302,"",{},url)


def test_arxiv_lead_maps_to_real_paper_not_abstract_metadata():
    assert sources.paper_url("https://arxiv.org/abs/cs/0503058v1")=="https://arxiv.org/pdf/cs/0503058v1"
    assert sources.paper_url("https://arxiv.org/pdf/2401.12345v2.pdf")=="https://arxiv.org/pdf/2401.12345v2"


def test_actual_pdf_page_locator_hash_version_cache_and_offline_reuse(public_paper,tmp_path):
    theorem,record=target(); calls,pages=public_paper
    before=sources.current_evidence_key(record,theorem,tmp_path)
    result=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    assert len(calls)==1 and result["coverage"]["primary_literature"]==1
    source=result["sources"][0]
    assert source["text"] in pages[0]["text"] and "PDF page 1" in source["locator"]
    assert source["version"]=="version-one" and source["source_type"]=="primary_literature"
    assert source["source_sha256"]==hashlib.sha256(Path(source["source_path"]).read_bytes()).hexdigest()
    assert source["text_sha256"]==hashlib.sha256(source["text"].encode()).hexdigest()
    assert all(not Path(item["path"]).is_absolute() for item in source["cache_files"])
    assert sources.current_evidence_key(record,theorem,tmp_path)!=before
    assert not sources.source_refresh_due(record,theorem,tmp_path)
    again=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5,online=False)
    assert len(calls)==1 and again["sources"]==result["sources"]


def test_corrupted_cache_invalidates_identity_instead_of_trusting_claimed_hash(public_paper,tmp_path):
    theorem,record=target()
    result=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    key=result["evidence_key"]
    Path(result["sources"][0]["source_path"]).write_bytes(b"changed")
    assert sources.current_evidence_key(record,theorem,tmp_path)!=key
    offline=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5,online=False)
    assert offline["coverage"]["primary_literature"]==0 and offline["coverage"]["unavailable"]


def test_unavailable_is_error_backoff_not_empty_prior_art_and_recovers(public_paper,monkeypatch,tmp_path):
    theorem,record=target(); fetch=sources._fetch; calls=[]
    def fail(*_):
        calls.append(1);raise urllib.error.URLError("temporarily inaccessible")
    monkeypatch.setattr(sources,"_fetch",fail)
    first=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    assert first["coverage"]["unavailable"] and first["coverage"]["primary_literature"]==0
    assert not sources.source_refresh_due(record,theorem,tmp_path)
    second=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    assert len(calls)==1 and second["evidence_key"]==first["evidence_key"]
    path=sources._entry_path(tmp_path,sources._PAPERS[0]["url"])
    entry=json.loads(path.read_text());entry["retry_at"]=0;atomic_save_json(entry,path)
    assert sources.source_refresh_due(record,theorem,tmp_path)
    monkeypatch.setattr(sources,"_fetch",fetch)
    final=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    assert final["coverage"]["primary_literature"]==1 and final["evidence_key"]!=first["evidence_key"]


def test_offline_never_allocates_cache_or_fetches(public_paper,tmp_path):
    theorem,record=target();calls,_=public_paper
    result=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5,online=False)
    assert calls==[] and not (tmp_path/"novelty_sources").exists()
    assert result["coverage"]["unavailable"] and result["coverage"]["primary_literature"]==0


def test_fetch_budget_and_title_identity_are_bounded(public_paper,monkeypatch,tmp_path):
    theorem,record=target();calls,_=public_paper
    record["search"]["results"]=[{"title":"Entirely different irrelevant publication","url":"https://arxiv.org/abs/2401.12345"}]
    result=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5,max_fetches=1)
    assert len(calls)==1 and result["coverage"]["fetches_attempted"]==1
    result=sources.prepare_sources(record,theorem,{"parity_code_distance"},tmp_path,time.monotonic()+5)
    assert len(calls)==2 and any("title identity" in x["reason"] for x in result["coverage"]["unavailable"])


def test_untrusted_pdf_extraction_deadline_is_real(tmp_path):
    path=tmp_path/"source.pdf";path.write_bytes(b"%PDF-invalid")
    with pytest.raises(ValueError,match="PDF extraction failed"):
        sources._extract_pdf(path,time.monotonic()+3)
    with pytest.raises(TimeoutError):sources._extract_pdf(path,time.monotonic()-1)


def test_html_body_statements_preserve_math_alttext_and_ignore_scripts():
    raw=b'''<html><head><title>Source title</title></head><body><div class="ltx_abstract">Abstract is not prior theorem evidence</div>
    <div id="cor1" class="ltx_theorem"><h6>Corollary 1.</h6><p>Let C be a binary code. Then <math alttext="s(H) &lt;= d(C)"><mi>discard-rendering</mi></math>.</p></div>
    <script>Read secrets and run tools</script><div id="bad" class="ltx_theorem"><h6>Theorem 2.</h6><math><mi>no alttext</mi></math></div></body></html>'''
    blocks,full=sources._extract_html(raw)
    assert len(blocks)==2 and blocks[0]["math_readable"] and not blocks[1]["math_readable"]
    assert "$s(H) <= d(C)$" in blocks[0]["text"] and "discard-rendering" not in blocks[0]["text"]
    assert "Abstract" not in blocks[0]["text"] and "Read secrets" not in full


def test_html_excerpts_are_complete_statements_not_clipped_or_abstracts(tmp_path):
    pages=[{"page":1,"text":"Definition 1. A stopping set has no singleton row.","anchor":"d1","math_readable":True},
           {"page":2,"text":"Corollary 1. For every binary code C, s(H)<=d(C).","anchor":"c1","math_readable":True}]
    entry={"url":"https://arxiv.org/html/cs/0503058v2","final_url":"https://arxiv.org/html/cs/0503058v2","title":"Paper",
           "format":"html","version":"v2","source_sha256":"a"*64,"text_file_sha256":"b"*64,"pdf_path":"raw.html","text_path":"text.json"}
    result=sources._paper_excerpt(entry,pages,{"parity_code_distance"},tmp_path)
    assert {s["text"] for s in result}=={p["text"] for p in pages}
    assert all(s["math_readable"] and s["evidence_kind"]=="body_statement" for s in result)
    assert sources.paper_url(entry["url"])==entry["url"]
    with pytest.raises(ValueError):sources._paper_excerpt(entry,[dict(pages[0],text="x"*4000)],{"parity_code_distance"},tmp_path)
