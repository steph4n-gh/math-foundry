"""Checked source bytes ground AI triage; titles and self-citation do not."""
import copy
import json
from pathlib import Path
from types import SimpleNamespace
import time

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.novelty import model_review
from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer, SynthesisError
from autonomous_math.research_state import sha256


@pytest.fixture
def corpus(monkeypatch, tmp_path):
    def validate(path, identifier, fingerprints):
        try:
            r = json.loads(Path(path).read_text())
            if not r.get("fixture_valid") or r["conjecture_id"] != identifier:
                return None, "Rejected fixture"
            if any(sha256(r[f"{k}_path"]) != r[f"{k}_sha256"] for k in ("source", "challenge")):
                return None, "Changed fixture"
            fingerprints.setdefault("workspace", "checked")
            return r, None
        except (OSError, ValueError, KeyError):
            return None, "Missing fixture"
    monkeypatch.setattr(model_review, "validate_receipt", validate)
    def theorem(identifier, invariant="order", guard=None):
        c = Conjecture.create(id=identifier, lhs=InvariantNode(invariant), rel=">=", rhs=ConstantNode(0), guard=guard)
        source, challenge, path = (tmp_path / f"{identifier}.{s}" for s in ("lean", "challenge.lean", "receipt.json"))
        source.write_text(f"import Mathlib.Tactic\n\ntheorem {identifier} (n : ℕ) : (0 : ℝ) ≤ n := by\n  exact Nat.cast_nonneg n\n")
        challenge.write_text(f"Fixture exact challenge {identifier}")
        r = {"schema_version": 1, "fixture_valid": True, "conjecture_id": identifier, "conjecture": c.to_dict(),
             "theorem_name": identifier, "source_path": str(source), "source_sha256": sha256(source),
             "challenge_path": str(challenge), "challenge_sha256": sha256(challenge), "workspace_sha256": "f" * 64}
        path.write_text(json.dumps(r))
        return {"id": identifier, "status": "LEAN_CERTIFIED", "conjecture": c.to_dict(), "lean_proof": {"receipt_path": str(path)}}
    def review(theorem, **extra):
        path = theorem["lean_proof"]["receipt_path"]
        return {"id": theorem["id"], "fingerprint": model_review._proof_fingerprint(theorem, json.loads(Path(path).read_text()), path),
                "closest_results": [], "search": {"status": "complete", "results": []}, **extra}
    return SimpleNamespace(theorem=theorem, review=review)


def atlas(*items):
    return {"theorems": {item["id"]: item for item in items}}


def answer(pack, outcome="unresolved", index=None, relationship="related_context"):
    s = pack["sources"][index] if index is not None else None
    failed = "restatement" if outcome == "known_result" else "routine_consequence"
    return {"outcome": outcome, "summary": "Completed AI comparison of supplied checked propositions.",
            "contribution": "No original contribution has been established.",
            "comparisons": [] if s is None else [{"source_id": s["source_id"], "quote": s["text"].splitlines()[0],
                "relationship": relationship, "comparison": "The quoted proposition has the same sides and complete common premise.",
                "premise_relation": "same_domain_and_premises"}],
            "checks": [{"label": label, "status": "fail" if s and label == failed and outcome != "unresolved" else "unknown",
                "detail": "The source supports this comparison; other exclusions remain open.", "source_ids": [s["source_id"]] if s else []}
                for label in sorted(model_review.CHECK_LABELS)],
            "uncertainties": ["Historical priority requires primary literature theorem text."]}


class Synthesizer:
    def __init__(self, response):
        self.response, self.calls = response, []
    def request_json(self, prompt, schema, directory, deadline, *, tools_disabled=False):
        self.calls.append((prompt, schema, tools_disabled))
        trace = {"actual_model": "configured-model", "configuration": {"reasoning_effort": "xhigh"},
                 "usage": {"input_tokens": 20, "output_tokens": 12}, "duration_ms": 1234.5}
        (directory / "trace.json").write_text(json.dumps(trace))
        (directory / "answer.json").write_text(json.dumps(self.response))
        return copy.deepcopy(self.response), trace


def test_pack_bounds_guard_closest_context_and_omits_invalid_sources(corpus):
    target = corpus.theorem("target", guard=GuardPredicate(predicate_type="comparison", invariant="order", op=">=", threshold=1))
    parents = [corpus.theorem(f"parent_{i}") for i in range(8)]
    bad, unrelated = corpus.theorem("bad"), corpus.theorem("unrelated", "size")
    Path(bad["lean_proof"]["receipt_path"]).unlink()
    empirical = corpus.theorem("empirical"); empirical["status"] = "EMPIRICAL_SURVIVOR"
    r = corpus.review(target, closest_results=[{"theorem_id": "bad"}, {"theorem_id": "parent_7"}])
    data = atlas(target, *parents, bad, unrelated, empirical); before = copy.deepcopy(data)
    pack = model_review.build_review_source_pack(r, target, data)
    assert len(pack["sources"]) == 5 and pack["sources"][1]["theorem_id"] == "parent_7"
    assert not {"bad", "unrelated", "empirical"} & {s["theorem_id"] for s in pack["sources"]}
    assert pack["target"] == target["conjecture"] and pack["sources"][0]["premise_lean"]
    assert pack["omitted_context"][0]["id"] == "bad"
    for s in pack["sources"]:
        assert s["text"] in Path(s["source_path"]).read_text() and s["source_sha256"] == sha256(s["source_path"])
        assert s["title"] and s["url"] is None
    assert data == before


def test_code_semantics_and_crossref_metadata_are_not_theorem_evidence(corpus):
    target = corpus.theorem("code", "parity_code_distance")
    metadata = [{"title": "x" * 1500, "url": "https://example.org", "doi": "10.1/a", "year": 2020}] * 8
    pack = model_review.build_review_source_pack(corpus.review(target, search={"results": metadata}), target, atlas(target))
    assert len(pack["bibliographic_metadata"]) == 5 and len(pack["bibliographic_metadata"][0]["title"]) == 700
    assert "n+1" in pack["semantics"]["code_semantics"]["parity_code_distance"]
    assert pack["primary_literature_text"] == "not supplied" and "not theorem text" in pack["metadata_scope"]
    assert all("source_id" not in m for m in pack["bibliographic_metadata"])


@pytest.mark.parametrize("corruption", ["fingerprint", "ast", "receipt", "source"])
def test_invalid_target_never_reaches_model(corpus, tmp_path, corruption):
    target = corpus.theorem("target"); r = corpus.review(target)
    if corruption == "fingerprint":
        r["fingerprint"] = "bad"
    elif corruption == "ast":
        target["conjecture"]["rhs_expr"]["value"] = 99
    elif corruption == "receipt":
        Path(target["lean_proof"]["receipt_path"]).unlink()
    else:
        receipt = json.loads(Path(target["lean_proof"]["receipt_path"]).read_text())
        Path(receipt["source_path"]).write_text("changed")
    synth = Synthesizer({})
    with pytest.raises(ValueError):
        model_review.assess_review(r, target, atlas(target), synth, tmp_path / "request", time.monotonic() + 5)
    assert not synth.calls


@pytest.mark.parametrize("outcome,relationship", [("known_result", "restatement"), ("routine_consequence", "routine_consequence")])
def test_grounded_results_are_completed_ai_triage_not_expert_endorsement(corpus, tmp_path, outcome, relationship):
    target, parent = corpus.theorem("target"), corpus.theorem("parent")
    data, r = atlas(target, parent), corpus.review(target)
    synth = Synthesizer(answer(model_review.build_review_source_pack(r, target, data), outcome, 1, relationship))
    result = model_review.assess_review(r, target, data, synth, tmp_path / "request", time.monotonic() + 5)
    assert result["status"] == "complete" and result["outcome"] == outcome
    assert result["reviewer_kind"] == "model" and result["model"] == "configured-model" and result["reasoning_effort"] == "xhigh"
    assert result["usage"] == {"input_tokens": 20, "output_tokens": 12} and result["duration_ms"] == 1234.5
    assert result["comparisons"][0]["title"] == "Checked local theorem parent" and result["comparisons"][0]["url"] is None
    assert "publication priority" in result["uncertainties"][-1]
    assert synth.calls[0][2] is True and synth.calls[0][1] is model_review.REQUEST_SCHEMA
    assert "Crossref METADATA is not theorem evidence" in synth.calls[0][0]
    assert "expert_review" not in result and "potential_contribution" not in json.dumps(result)
    assert (tmp_path / "request/source_pack.json").is_file() and Path(result["trace_path"]).is_file()


def test_only_target_evidence_cannot_turn_self_citation_into_prior_art(corpus, tmp_path):
    target = corpus.theorem("target"); data, r = atlas(target), corpus.review(target)
    pack = model_review.build_review_source_pack(r, target, data)
    result = model_review.assess_review(r, target, data, Synthesizer(answer(pack, "known_result", 0, "restatement")),
                                       tmp_path / "request", time.monotonic() + 5)
    assert result["status"] == "complete" and result["outcome"] == "unresolved" and result["model_outcome"] == "known_result"
    assert any("No quoted non-target" in u for u in result["uncertainties"])


@pytest.mark.parametrize("corruption", ["unknown_source", "invented_quote", "metadata", "check_source", "duplicate_check", "unsupported_outcome", "extra_field"])
def test_bad_sources_quotes_and_fields_reject_but_preserve_request(corpus, tmp_path, corruption):
    target, parent = corpus.theorem("target"), corpus.theorem("parent")
    data, r = atlas(target, parent), corpus.review(target)
    response = answer(model_review.build_review_source_pack(r, target, data), "known_result", 1, "restatement")
    if corruption in {"unknown_source", "metadata"}:
        response["comparisons"][0]["source_id"] = "metadata_0" if corruption == "metadata" else "invented_source"
    elif corruption == "invented_quote":
        response["comparisons"][0]["quote"] = "This quote was never present in the actual checked source."
    elif corruption == "check_source":
        response["checks"][0]["source_ids"] = ["invented_source"]
    elif corruption == "duplicate_check":
        response["checks"][1]["label"] = response["checks"][0]["label"]
    elif corruption == "unsupported_outcome":
        response["outcome"] = "potential_contribution"
    else:
        response["url"] = "https://invented.example/paper"
    directory = tmp_path / "request"
    with pytest.raises(SynthesisError, match="source validation failed"):
        model_review.assess_review(r, target, data, Synthesizer(response), directory, time.monotonic() + 5)
    assert json.loads((directory / "assessment_validation.json").read_text())["status"] == "rejected"
    assert (directory / "answer.json").is_file() and (directory / "source_pack.json").is_file()


def test_unresolved_can_honestly_have_no_comparisons(corpus, tmp_path):
    target = corpus.theorem("target"); data, r = atlas(target), corpus.review(target)
    pack = model_review.build_review_source_pack(r, target, data)
    result = model_review.assess_review(r, target, data, Synthesizer(answer(pack)), tmp_path / "request", time.monotonic() + 5)
    assert result["outcome"] == "unresolved" and not result["comparisons"]


@pytest.mark.parametrize("missing",[None,"primary","body","math","definition","premise","check","contradiction"])
def test_possible_extension_requires_primary_body_exact_quotes_and_consistent_exclusions(corpus,missing):
    target=corpus.theorem("target");data=atlas(target);r=corpus.review(target)
    pack=model_review.build_review_source_pack(r,target,data)
    source=dict(pack["sources"][0],source_id="primary_fixture",source_type="primary_literature",is_target=False,
                evidence_kind="body_statement",math_readable=True,statement_kind="theorem",theorem_id=None,text="Theorem 2. Every binary code satisfying the stated hypothesis has minimum distance at least three.")
    pack["sources"].append(source);pack["source_coverage"]["primary_literature"]=1
    response=answer(pack,"possible_extension",1,"related_context")
    response["contribution"]="The target would improve the quoted lower bound from three to four under the same explicitly compared premises."
    for check in response["checks"]:check["status"]="pass"
    if missing=="primary":source["source_type"]="checked_local_theorem"
    elif missing=="body":source["evidence_kind"]="abstract"
    elif missing=="math":source["math_readable"]=False
    elif missing=="definition":source["statement_kind"]="definition"
    elif missing=="premise":response["comparisons"][0]["premise_relation"]="different"
    elif missing=="check":response["checks"][0]["status"]="unknown"
    elif missing=="contradiction":response["comparisons"][0]["relationship"]="restatement"
    result=model_review._validate_assessment(response,pack)
    assert result["outcome"]==("possible_extension" if missing is None else "unresolved")
    assert "expert_review" not in result


def test_completed_review_revalidator_binds_actual_artifacts_and_source(corpus,tmp_path):
    target,parent=corpus.theorem("target"),corpus.theorem("parent")
    data,r=atlas(target,parent),corpus.review(target)
    pack=model_review.build_review_source_pack(r,target,data)
    result=model_review.assess_review(r,target,data,Synthesizer(answer(pack,"known_result",1,"restatement")),
        tmp_path/"novelty_attempts/request",time.monotonic()+5)
    r["ai_review"]=result
    validated=model_review.validate_completed_review(r,data,tmp_path)
    assert validated["assessment"]["outcome"]=="known_result"
    assert validated["artifact_binding"]["assessment_sha256"]==sha256(tmp_path/"novelty_attempts/request/assessment_validation.json")
    receipt=json.loads(Path(parent["lean_proof"]["receipt_path"]).read_text())
    Path(receipt["source_path"]).write_text("changed")
    with pytest.raises(ValueError):model_review.validate_completed_review(r,data,tmp_path)


def test_prior_exact_quote_failure_is_concise_repair_feedback(corpus,tmp_path):
    target=corpus.theorem("target");data=atlas(target);r=corpus.review(target,ai_review={"status":"error","error":"AI review quotation is not exact supplied source text"})
    synth=Synthesizer(answer(model_review.build_review_source_pack(r,target,data)))
    model_review.assess_review(r,target,data,synth,tmp_path/"request",time.monotonic()+5)
    assert "Previous failed attempt" in synth.calls[0][0] and "quotation is not exact" in synth.calls[0][0]


@pytest.mark.parametrize("changed",["assessment","pack","parent_record"])
def test_read_only_source_validation_rejects_modified_artifacts_or_removed_comparison(corpus,tmp_path,changed):
    target,parent=corpus.theorem("target"),corpus.theorem("parent");data=atlas(target,parent);r=corpus.review(target)
    response=answer(model_review.build_review_source_pack(r,target,data),"known_result",1,"restatement")
    result=model_review.assess_review(r,target,data,Synthesizer(response),tmp_path/"novelty_attempts/request",time.monotonic()+5)
    r["ai_review"]=result
    if changed=="parent_record":data["theorems"].pop("parent")
    else:
        file=tmp_path/"novelty_attempts/request"/("source_pack.json" if changed=="pack" else "assessment_validation.json")
        file.write_text(file.read_text()+" ")
    with pytest.raises(ValueError):model_review.validate_completed_review(r,data,tmp_path)


def test_expired_deadline_failure_and_repeated_request_preserve_evidence(corpus, tmp_path):
    target = corpus.theorem("target"); data, r = atlas(target), corpus.review(target)
    synth = Synthesizer({})
    with pytest.raises(SynthesisError, match="deadline"):
        model_review.assess_review(r, target, data, synth, tmp_path / "expired", time.monotonic() - 1)
    with pytest.raises(ValueError, match="finite"):
        model_review.assess_review(r, target, data, synth, tmp_path / "infinite", float("inf"))
    assert not synth.calls
    class Failing:
        def request_json(self, *args, **kwargs):
            raise SynthesisError("Service unavailable", {"status": "FAILED"})
    directory = tmp_path / "failed"
    with pytest.raises(SynthesisError, match="Service unavailable"):
        model_review.assess_review(r, target, data, Failing(), directory, time.monotonic() + 5)
    assert (directory / "source_pack.json").is_file() and not (directory / "assessment_validation.json").exists()
    with pytest.raises(SynthesisError, match="overwrite"):
        model_review.assess_review(r, target, data, synth, directory, time.monotonic() + 5)


@pytest.mark.parametrize("tools_disabled", [False, True])
def test_tool_opt_in_preserves_proof_mode_and_configured_model_effort(tmp_path, monkeypatch, tools_disabled):
    cli = tmp_path / "fake_codex"
    cli.write_text("#!/usr/bin/env python3\nimport json,sys\nfrom pathlib import Path\na=sys.argv[1:]\nsys.stdin.read()\nPath(a[a.index('--output-last-message')+1]).write_text('{}')\nprint(json.dumps({'type':'turn.completed','usage':{'input_tokens':2,'output_tokens':1}}))\n")
    cli.chmod(0o755)
    config_dir, workspace = tmp_path / "config", tmp_path / "workspace"
    config_dir.mkdir(); workspace.mkdir()
    config = config_dir / "config.toml"; original = 'model="configured-model"\nmodel_reasoning_effort="xhigh"\n'
    config.write_text(original); monkeypatch.setenv("CODEX_HOME", str(config_dir))
    synth = CodexProofSynthesizer(workspace_dir=workspace, cli_path=cli)
    _, trace = synth.request_json("Bounded fixture", {"type": "object", "additionalProperties": False},
                                  tmp_path / "request", time.monotonic() + 5, tools_disabled=tools_disabled)
    args = trace["command"]; disabled = {args[i + 1] for i, value in enumerate(args[:-1]) if value == "--disable"}
    assert ("shell_tool" in disabled) == ("unified_exec" in disabled) == tools_disabled
    assert ('web_search="disabled"' in args) == tools_disabled
    assert trace["configuration"].get("tools_disabled", False) == tools_disabled
    assert args[args.index("--model") + 1] == "configured-model" and 'model_reasoning_effort="xhigh"' in args
    assert config.read_text() == original and not synth.active_process_groups()


def extension_pack(corpus, tmp_path):
    target = corpus.theorem("code_target", "parity_code_distance",
        guard=GuardPredicate(invariant="parity_code_dimension", op=">=", threshold=1))
    data, record = atlas(target), corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data)
    text = ("Theorem 2. For a GF2 adjacency kernel code of positive dimension and maximum degree at most two, "
            "the nonzero minimum weight is nonnegative. Distance is n+1 for a zero code. "
            "Stopping radius is minimum stopping-set size minus one, or n when no stopping set exists.")
    paper = tmp_path / "fixture_primary.txt"; paper.write_text(text)
    pages = tmp_path / "fixture_pages.json"; pages.write_text(json.dumps([{"page": 0, "text": text}]))
    primary = dict(pack["sources"][0], source_id="primary_fixture", source_type="primary_literature", is_target=False,
        theorem_id=None, evidence_kind="body_statement", math_readable=True, statement_kind="theorem",
        source_path=str(paper), source_sha256=sha256(paper), text=text,
        text_sha256=model_review.hashlib.sha256(text.encode()).hexdigest(), page=0, excerpt_start=0,
        cache_files=[{"kind": "extracted_pages", "path": pages.name, "sha256": sha256(pages)}])
    pack["sources"].append(primary); pack["source_coverage"]["primary_literature"] = 1
    response = answer(pack, "possible_extension", 1)
    response["contribution"] = "This synthetic control alleges removal of the maximum-degree hypothesis under identical definitions; it tests evidence gates, not a novel theorem."
    for check in response["checks"]: check["status"] = "pass"
    comparison = response["comparisons"][0]
    comparison["premise_relation"] = "target_broader"
    comparison["generalization"] = {
        "baseline_guard": [{"invariant": "parity_code_dimension", "op": ">=", "threshold": 1},
                           {"invariant": "max_degree", "op": "<=", "threshold": 2}],
        "guard_quote": text, "definitions_quote": text, "conclusion_relation": "same_conclusion",
        "semantics": {"field": "GF2", "matrix": "adjacency", "code": "kernel",
                      "distance": "nonzero_min_weight_n_plus_one_sentinel", "stopping": "minimum_stopping_size_minus_one"},
        "separating_graph": {"order": 4, "edges": [[0, 1], [0, 2], [0, 3]]}}
    return target, data, record, pack, response


@pytest.mark.parametrize("corruption", [None, "matrix", "definitions_quote", "baseline", "not_separating", "edge", "duplicate", "order", "missing_audit"])
def test_target_broader_requires_exact_definition_quotes_and_recomputed_domain_witness(corpus, tmp_path, corruption):
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    evidence = response["comparisons"][0]["generalization"]
    if corruption == "matrix": evidence["semantics"]["matrix"] = "incidence"
    elif corruption == "definitions_quote": evidence["definitions_quote"] = "A definition invented from a paper title instead of supplied source text."
    elif corruption == "baseline": evidence["baseline_guard"] = [{"invariant": "max_degree", "op": "<=", "threshold": 2}]
    elif corruption == "not_separating": evidence["separating_graph"]["edges"].pop()
    elif corruption == "edge": evidence["separating_graph"]["edges"][0] = [0, 4]
    elif corruption == "duplicate": evidence["separating_graph"]["edges"].append([0, 1])
    elif corruption == "order": evidence["separating_graph"]["order"] = 9
    elif corruption == "missing_audit": response["comparisons"][0].pop("generalization")
    if corruption is not None:
        with pytest.raises(ValueError): model_review._validate_assessment(response, pack)
    else:
        result = model_review._validate_assessment(response, pack)
        audit = result["comparisons"][0]["generalization_validation"]
        assert result["outcome"] == "possible_extension"
        assert audit["invariants"]["max_degree"] == 3 and audit["invariants"]["parity_code_dimension"] == 2
        assert audit["target_guard_holds"] and not audit["baseline_guard_holds"]
        assert "provisional semantic AI" in audit["scope"]


class PairedSynthesizer(Synthesizer):
    def __init__(self, responses):
        super().__init__(None); self.responses = list(responses)
    def request_json(self, *args, **kwargs):
        response = self.responses.pop(0)
        if isinstance(response, Exception): raise response
        self.response = response
        return super().request_json(*args, **kwargs)


@pytest.mark.parametrize("verdict", ["possible_extension", "routine_consequence", "unresolved"])
def test_skeptical_challenge_clears_or_rejects_provisional_claim_with_identical_source_pack(corpus, tmp_path, monkeypatch, verdict):
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    critic = copy.deepcopy(response)
    if verdict != "possible_extension":
        critic = answer(pack, verdict, 1, "routine_consequence" if verdict == "routine_consequence" else "related_context")
    synth = PairedSynthesizer([response, critic])
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *a, **kw: copy.deepcopy(pack))
    from autonomous_math.novelty import primary_sources
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *a: None)
    directory = tmp_path / "novelty_attempts/request"
    result = model_review.assess_review(record, target, data, synth, directory, time.monotonic() + 5)
    assert len(synth.calls) == 2 and all(call[2] for call in synth.calls)
    expected = {"possible_extension": "cleared_relative_advance", "routine_consequence": "source_backed_derivation", "unresolved": "evidence_gap"}
    assert result["challenge"]["verdict"] == expected[verdict] and result["outcome"] == verdict
    assert result["preliminary_assessment"]["outcome"] == "possible_extension"
    second_pack = json.loads(synth.calls[1][0].split("\n", 1)[1])["source_pack"]
    assert second_pack == pack
    assert result["usage"] == {"input_tokens": 40, "output_tokens": 24}
    assert result["duration_ms"] == 2469.0 and result["usage_accounting"]["missing_usage_count"] == 0
    record["ai_review"] = result
    assert model_review.validate_completed_review(record, data, tmp_path)["assessment"]["outcome"] == verdict
    if verdict == "possible_extension":
        record["ai_review"].pop("challenge")
        with pytest.raises(ValueError, match="binding changed"):
            model_review.validate_completed_review(record, data, tmp_path)


@pytest.mark.parametrize("failure", ["timeout", "fabricated_quote"])
def test_critic_failure_retains_first_assessment_and_both_requests_without_promoting(corpus, tmp_path, monkeypatch, failure):
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    critic = SynthesisError("Request timed out", {"duration_ms": 1200000, "usage": {}}) if failure == "timeout" else copy.deepcopy(response)
    if failure == "fabricated_quote": critic["comparisons"][0]["quote"] = "This fabricated quotation never occurs in supplied theorem text."
    synth = PairedSynthesizer([response, critic])
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *a, **kw: copy.deepcopy(pack))
    directory = tmp_path / "request"
    with pytest.raises(SynthesisError, match="challenge failed") as caught:
        model_review.assess_review(record, target, data, synth, directory, time.monotonic() + 5)
    trace = caught.value.trace
    assert len(trace["requests"]) == 2 and trace["requests"][0]["status"] == "complete"
    assert trace["requests"][1]["status"] in {"error", "rejected"}
    assert json.loads((directory / "preliminary_assessment_validation.json").read_text())["outcome"] == "possible_extension"
    assert json.loads((directory / "challenge/assessment_validation.json").read_text())["status"] == "rejected"
    assert not (directory / "assessment_validation.json").exists()
    if failure == "timeout":
        assert trace["usage_accounting"]["missing_usage_count"] == 1 and trace["usage"] == {}


def test_checked_dependencies_beat_incidental_overlap_and_long_proofs_keep_complete_signatures(corpus):
    target = corpus.theorem("target", "parity_code_distance")
    parents = [corpus.theorem(f"parent_{i}", "parity_code_distance") for i in range(7)]
    dependency = corpus.theorem("dependency", "parity_code_dimension")
    target["lean_proof"]["used_lemma_ids"] = ["dependency"]
    data, record = atlas(target, *parents, dependency), corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data)
    assert pack["sources"][1]["theorem_id"] == "dependency" and len(pack["sources"]) == 5
    receipt_path = Path(dependency["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    source = Path(receipt["source_path"]); source.write_text(source.read_text() + " " * model_review.MAX_EXCERPT_CHARS)
    receipt["source_sha256"] = sha256(source); receipt_path.write_text(json.dumps(receipt))
    pack = model_review.build_review_source_pack(record, target, data)
    chosen = next(item for item in pack["sources"] if item.get("theorem_id") == "dependency")
    assert chosen["proof_body_omitted"] and not chosen["excerpt_truncated"]
    assert chosen["text"].endswith(':= by') and 'long proof body omitted' in chosen['scope']


@pytest.mark.parametrize('corruption', [None, 'unknown', 'other_paper', 'unreadable'])
def test_generalization_definitions_can_use_bound_same_paper_context_but_not_unrelated_text(corpus, tmp_path, corruption):
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    context = dict(pack['sources'][1], source_id='primary_definitions', evidence_kind='body_context', statement_kind='context',
                   text='Definition: the code uses GF2 adjacency kernel vectors and the explicit zero-code distance sentinel.')
    pack['sources'].append(context)
    audit = response['comparisons'][0]['generalization']
    audit.update(definitions_source_id=context['source_id'], definitions_quote=context['text'])
    if corruption == 'unknown': audit['definitions_source_id'] = 'not_supplied'
    elif corruption == 'other_paper': context['source_sha256'] = 'd' * 64
    elif corruption == 'unreadable': context['math_readable'] = False
    if corruption:
        with pytest.raises(ValueError): model_review._validate_assessment(response, pack)
    else:
        assert model_review._validate_assessment(response, pack)['outcome'] == 'possible_extension'


def test_separating_guard_graph_cannot_replace_checking_exact_target_conclusion(corpus, tmp_path):
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    pack['target']['rhs_expr']['value'] = 10
    with pytest.raises(ValueError, match='target conclusion fails'):
        model_review._validate_assessment(response, pack)


def test_provider_schema_uses_supported_nullable_optional_fields_and_anyof():
    def visit(schema):
        assert 'oneOf' not in schema and 'const' not in schema
        if schema.get('type') == 'object':
            assert schema.get('additionalProperties') is False
            assert set(schema['required']) == set(schema['properties'])
        for child in schema.get('properties', {}).values(): visit(child)
        if 'items' in schema: visit(schema['items'])
        for child in schema.get('anyOf', []): visit(child)
    visit(model_review.REQUEST_SCHEMA)
    comparison = model_review.REQUEST_SCHEMA['properties']['comparisons']['items']
    assert {'type': 'null'} in comparison['properties']['generalization']['anyOf']


def test_provider_null_generalization_keeps_known_routine_compatibility(corpus):
    target, parent = corpus.theorem('target'), corpus.theorem('parent')
    pack = model_review.build_review_source_pack(corpus.review(target), target, atlas(target, parent))
    response = answer(pack, 'known_result', 1, 'restatement')
    response['comparisons'][0]['generalization'] = None
    model_review.validate_json_schema(response, model_review.REQUEST_SCHEMA)
    assert model_review._validate_assessment(response, pack)['outcome'] == 'known_result'


def test_domain_specific_conclusion_overlap_selects_forest_comparison_over_order_degree(corpus):
    from autonomous_math.core.ast import BinaryOpNode
    target = corpus.theorem('target', 'parity_code_distance')
    t = Conjecture.create(id='target', lhs=InvariantNode('parity_code_distance'), rel='<=',
        rhs=BinaryOpNode('+', InvariantNode('unique_neighbor_radius'), InvariantNode('order')))
    receipt_path = Path(target['lean_proof']['receipt_path']); receipt = json.loads(receipt_path.read_text())
    receipt['conjecture'] = t.to_dict(); receipt_path.write_text(json.dumps(receipt)); target['conjecture'] = t.to_dict()
    other = [corpus.theorem(f'earlier_{i}', 'parity_code_distance') for i in range(8)]
    forest = corpus.theorem('forest_equality', 'parity_code_distance')
    c = Conjecture.create(id='forest_equality', lhs=InvariantNode('parity_code_distance'), rel='==',
        rhs=BinaryOpNode('+', InvariantNode('unique_neighbor_radius'), ConstantNode(1)), guard=GuardPredicate('is_forest'))
    p = Path(forest['lean_proof']['receipt_path']); receipt = json.loads(p.read_text())
    receipt['conjecture'] = c.to_dict(); p.write_text(json.dumps(receipt)); forest['conjecture'] = c.to_dict()
    pack = model_review.build_review_source_pack(corpus.review(target), target, atlas(target, *other, forest))
    assert pack['sources'][1]['theorem_id'] == 'forest_equality'


def test_oversized_checked_signature_is_omitted_even_when_its_proof_is_short(corpus):
    target, parent = corpus.theorem('target'), corpus.theorem('parent')
    p = Path(parent['lean_proof']['receipt_path']); receipt = json.loads(p.read_text())
    source = Path(receipt['source_path'])
    source.write_text(source.read_text().replace(' (n : ℕ)', ' (n : ℕ)' + ' ' * model_review.MAX_EXCERPT_CHARS))
    receipt['source_sha256'] = sha256(source); p.write_text(json.dumps(receipt))
    pack = model_review.build_review_source_pack(corpus.review(target), target, atlas(target, parent))
    assert len(pack['sources']) == 1 and any(item['id'] == 'parent' for item in pack['omitted_context'])
