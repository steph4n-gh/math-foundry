"""Unsupported graph-domain audits finish unresolved without inventing code semantics."""
import copy
import hashlib
import json
import time

import pytest

from autonomous_math.novelty import model_review, primary_sources
from autonomous_math.novelty.review_worker import next_review
from autonomous_math.research_state import sha256
from tests.unit.test_model_review import corpus, atlas, answer, Synthesizer, extension_pack


def noncode_pack(corpus, tmp_path, invariant="chromatic_number"):
    target = corpus.theorem("noncode_target", invariant)
    data, record = atlas(target), corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data)
    text = "Theorem 3. For every connected finite simple graph, the stated graph invariant is nonnegative."
    paper, pages = tmp_path / "noncode_primary.txt", tmp_path / "noncode_pages.json"
    paper.write_text(text)
    pages.write_text(json.dumps([{"page": 0, "text": text}]))
    source = dict(pack["sources"][0], source_id="noncode_primary", source_type="primary_literature", is_target=False,
        theorem_id=None, evidence_kind="body_statement", math_readable=True, statement_kind="theorem",
        source_path=str(paper), source_sha256=sha256(paper), text=text,
        text_sha256=hashlib.sha256(text.encode()).hexdigest(), page=0, excerpt_start=0,
        cache_files=[{"kind": "extracted_pages", "path": pages.name, "sha256": sha256(pages)}])
    pack["sources"].append(source)
    pack["source_coverage"]["primary_literature"] = 1
    response = answer(pack, "possible_extension", 1)
    response["contribution"] = "This synthetic control alleges removal of a connectedness restriction, with no host-supported domain audit; it does not establish an advance."
    for check in response["checks"]:
        check["status"] = "pass"
    response["comparisons"][0].update(premise_relation="target_broader", generalization=None)
    return target, data, record, pack, response


@pytest.mark.parametrize("invariant", ["chromatic_number", "spectral_radius", "graph_energy"])
@pytest.mark.parametrize("null_audit", [True, False])
def test_valid_quoted_noncode_wider_comparison_is_unresolved_not_validation_error(corpus, tmp_path, invariant, null_audit):
    _, _, _, pack, response = noncode_pack(corpus, tmp_path, invariant)
    if not null_audit:
        response["comparisons"][0].pop("generalization")
    response["uncertainties"] = [f"Unsettled historical question {n}." for n in range(6)]
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved"
    assert result["model_outcome"] == "possible_extension"
    assert result["comparisons"][0]["quote"] == response["comparisons"][0]["quote"]
    assert result["comparisons"][0]["generalization_validation"]["status"] == "unsupported_noncode"
    assert model_review.NONCODE_AUDIT_LIMITATION in result["uncertainties"]
    assert "code_semantics" not in pack["semantics"]
    assert pack["semantics"]["wider_domain_audit"]["status"] == "unsupported_noncode"
    replayed = model_review._validate_assessment(model_review._assessment_fields(result), pack)
    assert replayed["outcome"] == result["outcome"]
    assert replayed["comparisons"] == result["comparisons"]
    assert replayed["summary"] == result["summary"]


def test_noncode_scope_cannot_be_overridden_by_another_favorable_comparison(corpus, tmp_path):
    _, _, _, pack, response = noncode_pack(corpus, tmp_path)
    comparison = copy.deepcopy(response["comparisons"][0])
    comparison.update(premise_relation="same_domain_and_premises")
    response["comparisons"].append(comparison)
    assert model_review._validate_assessment(response, pack)["outcome"] == "unresolved"


@pytest.mark.parametrize("outcome", ["known_result", "routine_consequence", "unresolved"])
def test_unsupported_wider_relation_never_becomes_source_backed_derivation(corpus, tmp_path, outcome):
    _, _, _, pack, response = noncode_pack(corpus, tmp_path)
    response["outcome"] = outcome
    response["comparisons"][0]["relationship"] = "restatement" if outcome == "known_result" else "routine_consequence"
    for check in response["checks"]:
        check["status"] = "fail"
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved"
    assert "wider-domain host audit is unavailable" in result["summary"]


def test_completed_noncode_review_keeps_usage_replays_and_is_not_requeued(corpus, tmp_path, monkeypatch):
    target, data, record, pack, response = noncode_pack(corpus, tmp_path)
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *args, **kwargs: copy.deepcopy(pack))
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *args: pack["evidence_key"])
    synthesizer = Synthesizer(response)
    directory = tmp_path / "novelty_attempts" / "noncode_request"
    result = model_review.assess_review(record, target, data, synthesizer, directory, time.monotonic()+5)
    assert result["status"] == "complete" and result["outcome"] == "unresolved"
    assert "challenge" not in result and len(synthesizer.calls) == 1
    assert result["usage"] == {"input_tokens": 20, "output_tokens": 12}
    assert result["usage_accounting"] == {"request_count": 1, "missing_usage_count": 0,
                                          "scope": "Only reported request usage is counted; missing usage is unknown."}
    assert result["requests"][0]["status"] == "complete"
    assert result["requests"][0]["trace_sha256"] == sha256(directory / "trace.json")
    assert json.loads((directory / "answer.json").read_text()) == response
    assert "Never invent GF2 semantics for a non-code target" in synthesizer.calls[0][0]
    record["status"] = "awaiting_review"
    record["ai_review"] = result
    first = model_review.validate_completed_review(record, data, tmp_path)
    second = model_review.validate_completed_review(record, data, tmp_path)
    assert first == second
    assert first["assessment"]["outcome"] == "unresolved"
    assert next_review([record], data, time.time()+3600) is None


@pytest.mark.parametrize("corruption", ["missing", "null", "incidence", "nonseparating", "fabricated_quote"])
def test_code_wider_domain_witnesses_still_fail_closed(corpus, tmp_path, corruption):
    _, _, _, pack, response = extension_pack(corpus, tmp_path)
    comparison = response["comparisons"][0]
    if corruption == "missing":
        comparison.pop("generalization")
    elif corruption == "null":
        comparison["generalization"] = None
    elif corruption == "incidence":
        comparison["generalization"]["semantics"]["matrix"] = "incidence"
    elif corruption == "nonseparating":
        comparison["generalization"]["separating_graph"]["edges"].pop()
    else:
        comparison["generalization"]["definitions_quote"] = "This definition was fabricated and is absent from the paper."
    with pytest.raises(ValueError):
        model_review._validate_assessment(response, pack)


def test_valid_coding_audit_keeps_current_revision_and_gate(corpus, tmp_path):
    _, _, _, pack, response = extension_pack(corpus, tmp_path)
    result = model_review._validate_assessment(response, pack)
    assert model_review.REVIEW_REVISION == "primary-source-ai-comparison-v2-generalization-challenge"
    assert result["outcome"] == "possible_extension"
    assert result["comparisons"][0]["generalization_validation"]["status"] == "verified_finite_separation"
