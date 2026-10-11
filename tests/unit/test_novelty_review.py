"""Literature retrieval is bounded evidence, never automatic originality."""
import copy
import fcntl
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from urllib.error import HTTPError

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.novelty import review
from autonomous_math.research_state import sha256, writer_lock


@pytest.fixture
def engine(monkeypatch, tmp_path):
    policy = tmp_path / "classification_policy.py"
    policy.write_text("policy-v1")
    statuses, classified, validated = {}, [], []

    def classify(record, atlas):
        classified.append((record["id"], set(atlas["theorems"])))
        return {"status": statuses.get(record["id"], "awaiting_review"),
                "summary": "A mathematical comparison, not an originality certificate.",
                "contribution": "not yet established", "closest_results": [],
                "checks": [{"label": "exact_comparison", "status": "unknown", "detail": "Specific comparison remains open."}],
                "uncertainties": ["A bibliographic search cannot establish originality."]}

    module = SimpleNamespace(__file__=str(policy), classify_record=classify)
    monkeypatch.setitem(sys.modules, "autonomous_math.novelty.review_classification", module)
    monkeypatch.setattr("autonomous_math.novelty.review_classification", module, raising=False)

    def validate(path, identifier, fingerprints):
        validated.append(identifier)
        try:
            data = json.loads(Path(path).read_text())
            if data["conjecture_id"] != identifier or not data["fixture_valid"]:
                return None, "Fixture receipt rejected"
            if any(sha256(Path(data[f"{key}_path"])) != data[f"{key}_sha256"] for key in ("source", "challenge")):
                return None, "Changed artifact"
            fingerprints.setdefault("fixture_workspace", "checked")
            return data, None
        except (OSError, ValueError, KeyError):
            return None, "Missing fixture receipt"

    monkeypatch.setattr(review, "validate_receipt", validate)

    def record(identifier, invariant="order", iteration=1):
        conjecture = Conjecture.create(id=identifier, lhs=InvariantNode(invariant), rel=">=", rhs=ConstantNode(0))
        source = tmp_path / f"{identifier}.lean"
        challenge = tmp_path / f"{identifier}.challenge.lean"
        source.write_text("Unit fixture proof source " + identifier)
        challenge.write_text("Unit fixture target " + identifier)
        receipt = tmp_path / f"{identifier}.receipt.json"
        receipt.write_text(json.dumps({"schema_version": 1, "fixture_valid": True,
            "conjecture_id": identifier, "conjecture": conjecture.to_dict(),
            "source_path": str(source), "source_sha256": sha256(source),
            "challenge_path": str(challenge), "challenge_sha256": sha256(challenge),
            "workspace_sha256": "a" * 64}))
        return {"id": identifier, "conjecture": conjecture.to_dict(), "status": "LEAN_CERTIFIED",
                "discovered_iteration": iteration, "lean_proof": {"receipt_path": str(receipt)}}

    return SimpleNamespace(record=record, statuses=statuses, classified=classified,
                           validated=validated, policy=policy)


def atlas(*records):
    return {"theorems": {record["id"]: record for record in records}}


def test_ai_review_is_bound_to_receipt_and_does_not_grant_originality(engine, tmp_path):
    snapshot = atlas(engine.record("ai_target"))
    current = review.update_reviews(snapshot, tmp_path, online=False)["records"][0]
    completed = {"status": "complete", "outcome": "known_result", "summary": "AI comparison", "attempts": 1}
    saved = review.record_ai_review(snapshot, tmp_path, current["id"], current["fingerprint"], completed)
    assert saved["records"][0]["status"] == "awaiting_review"
    assert saved["counts"]["ai_complete"] == 1
    assert saved["counts"]["ai_pending"] == 0
    refreshed = review.update_reviews(snapshot, tmp_path, online=False)
    refreshed_ai = refreshed["records"][0]["ai_review"]
    assert all(refreshed_ai[key] == value for key,value in completed.items())
    assert refreshed_ai["refresh_pending"] and not refreshed_ai["evidence_current"]
    assert refreshed["counts"]["ai_complete"] == 0 and refreshed["counts"]["ai_pending"] == 1
    with pytest.raises(ValueError, match="current validated proof"):
        review.record_ai_review(snapshot, tmp_path, current["id"], "obsolete", completed)
    with pytest.raises(ValueError, match="cannot establish"):
        review.record_ai_review(snapshot, tmp_path, current["id"], current["fingerprint"],
                               dict(completed, outcome="potential_contribution"))
    source = json.loads(Path(snapshot["theorems"]["ai_target"]["lean_proof"]["receipt_path"]).read_text())["source_path"]
    Path(source).write_text("Changed proof")
    assert review.get_reviews(snapshot, tmp_path)["records"] == []


def test_public_completed_count_fails_closed_when_bound_source_validation_fails(engine,tmp_path,monkeypatch):
    from autonomous_math.novelty import model_review,primary_sources
    snapshot=atlas(engine.record("target"));r=review.update_reviews(snapshot,tmp_path,online=False)["records"][0]
    ai={"status":"complete","outcome":"unresolved","sources_revision":primary_sources.SOURCE_REVISION,
        "revision":model_review.REVIEW_REVISION,"evidence_key":primary_sources.current_evidence_key(r,snapshot["theorems"]["target"],tmp_path),
        "trace_path":"retained/trace.json"}
    review.record_ai_review(snapshot,tmp_path,"target",r["fingerprint"],ai)
    before=(tmp_path/review.REVIEW_FILE).read_bytes()
    monkeypatch.setattr(model_review,"validate_completed_review",lambda *a,**kw:{})
    current=review.get_reviews(snapshot,tmp_path)
    assert current["counts"]["ai_complete"]==1 and current["records"][0]["ai_review"]["evidence_current"]
    def changed(*a,**kw):raise ValueError("Checked comparison source bytes changed")
    monkeypatch.setattr(model_review,"validate_completed_review",changed)
    current=review.get_reviews(snapshot,tmp_path)
    assert current["counts"]["ai_complete"]==0 and current["counts"]["ai_pending"]==1
    assert current["records"][0]["ai_review"]["refresh_pending"]
    assert current["records"][0]["ai_review"]["trace_path"]=="retained/trace.json"
    assert (tmp_path/review.REVIEW_FILE).read_bytes()==before


def test_stale_ai_worker_cannot_look_running(engine, tmp_path):
    (tmp_path / "novelty_review_worker.json").write_text(json.dumps({"state": "running", "heartbeat": 1}))
    result = review.get_reviews(atlas(), tmp_path)
    assert result["automation"]["state"] == "stopped"
    assert "stale" in result["automation"]["error"]


def test_async_ai_save_preserves_newer_unrelated_assessments(engine, tmp_path):
    first, newer = engine.record("first"), engine.record("newer")
    old = atlas(first)
    current = atlas(first, newer)
    reviews = review.update_reviews(current, tmp_path, online=False)["records"]
    by_id = {item["id"]: item for item in reviews}
    completed = {"status": "complete", "outcome": "unresolved", "summary": "Saved newer work"}
    review.record_ai_review(current, tmp_path, "newer", by_id["newer"]["fingerprint"], completed)
    result = review.record_ai_review(old, tmp_path, "first", by_id["first"]["fingerprint"],
                                    {"status": "running"})
    assert next(item for item in result["records"] if item["id"] == "newer")["ai_review"] == completed


@pytest.mark.parametrize("state", ["error", "running"])
def test_exact_comparison_retires_obsolete_ai_work_without_losing_attempt(engine, tmp_path, state):
    snapshot = atlas(engine.record("rescaled"))
    current = review.update_reviews(snapshot, tmp_path, online=False)["records"][0]
    attempt = {"status": state, "error": "Model deadline", "trace_path": "preserved/trace.json", "attempts": 1}
    review.record_ai_review(snapshot, tmp_path, "rescaled", current["fingerprint"], attempt)
    engine.statuses["rescaled"] = "routine_consequence"
    engine.policy.write_text("policy-with-exact-rescaling")
    result = review.update_reviews(snapshot, tmp_path, online=False)
    saved = result["records"][0]
    assert saved["status"] == "routine_consequence"
    assert saved["ai_review"]["superseded"]
    assert all(saved["ai_review"][key] == value for key, value in attempt.items())
    assert result["counts"]["ai_errors"] == result["counts"]["ai_running"] == result["counts"]["ai_pending"] == 0
    assert result["counts"]["ai_superseded"] == 1
    # A later changed comparison policy must not silently discard the attempt
    # or permanently suppress a still-required retry.
    engine.statuses["rescaled"] = "awaiting_review"
    engine.policy.write_text("policy-requiring-more-evidence")
    result = review.update_reviews(snapshot, tmp_path, online=False)
    assert not result["records"][0]["ai_review"].get("superseded")
    assert result["counts"]["ai_errors" if state == "error" else "ai_running"] == 1


def test_inflight_ai_completion_cannot_reopen_a_deterministically_resolved_result(engine, tmp_path):
    snapshot = atlas(engine.record("rescaled"))
    current = review.update_reviews(snapshot, tmp_path, online=False)["records"][0]
    engine.statuses["rescaled"] = "routine_consequence"
    engine.policy.write_text("policy-with-exact-rescaling")
    complete = {"status": "complete", "outcome": "unresolved", "summary": "Old model context", "attempts": 1}
    result = review.record_ai_review(snapshot, tmp_path, "rescaled", current["fingerprint"], complete)
    assert result["records"][0]["status"] == "routine_consequence"
    assert result["records"][0]["ai_review"] == complete
    assert result["counts"]["ai_complete"] == 1


def assessment(record, status="potential_contribution"):
    return {"id": record["id"], "fingerprint": record["fingerprint"], "status": status,
            "reviewer": "Named assessor", "summary": "A proposed improvement requiring expert examination.",
            "contribution": "A candidate stronger bound in the explicit graph class, compared below.",
            "closest_results": [{"title": "Specific prior theorem", "url": "https://example.org/paper",
                "citation": "Author, theorem 2", "relationship": "Prior bound in the same domain",
                "comparison": "The proposed coefficient is smaller under the stated common premise."}],
            "checks": [{"label": label, "status": "pass", "detail": "The assessor compared the exact bound and common domain."}
                       for label in sorted(review.REQUIRED_CHECKS)],
            "uncertainties": ["Prior coverage and mathematical significance still require expert review."]}


def test_read_is_network_free_does_not_classify_or_create_files(engine, tmp_path, monkeypatch):
    monkeypatch.setattr(review, "_search_crossref", lambda *args: pytest.fail("Read must not search"))
    directory = tmp_path / "absent"
    result = review.get_reviews(atlas(engine.record("a")), directory)
    assert result["counts"]["awaiting_review"] == 1 and not directory.exists()
    assert not engine.classified
    assert result["records"][0]["contribution"] == "not yet established"


def test_empty_search_is_complete_and_never_promotes_novelty(engine, tmp_path, monkeypatch):
    calls = []
    monkeypatch.setattr(review, "_search_crossref", lambda *args: calls.append(args) or [])
    data = atlas(engine.record("a"), engine.record("b"))
    result = review.update_reviews(data, tmp_path)
    assert len(calls) == 1  # Identical bibliographic query, two exact proof identities.
    assert all(r["search"]["status"] == "complete" and not r["search"]["results"] for r in result["records"])
    assert result["counts"]["potential_contribution"] == 0
    assert result["counts"]["awaiting_review"] == 2
    before = copy.deepcopy(engine.classified)
    review.get_reviews(data, tmp_path)
    review.update_reviews(data, tmp_path)
    assert engine.classified == before and len(calls) == 1


def test_max_searches_and_newest_unresolved_priority(engine, tmp_path, monkeypatch):
    queries = []
    monkeypatch.setattr(review, "_search_crossref", lambda q, timeout: queries.append(q) or [])
    data = atlas(engine.record("old", "order", 1), engine.record("new", "size", 4),
                 engine.record("second", "max_degree", 3), engine.record("third", "min_degree", 2))
    result = review.update_reviews(data, tmp_path, max_searches=2)
    assert len(queries) == 2 and "size" in queries[0] and "max degree" in queries[1]
    assert sum(r["search"]["status"] == "complete" for r in result["records"]) == 2
    review.update_reviews(data, tmp_path, max_searches=0)
    assert len(queries) == 2


def test_failed_request_is_error_not_empty_and_retries_after_delay(engine, tmp_path, monkeypatch):
    now, calls = [1000], []
    monkeypatch.setattr(review.time, "time", lambda: now[0])
    def search(*args):
        calls.append(args)
        if len(calls) == 1:
            raise TimeoutError("Provider timeout")
        return []
    monkeypatch.setattr(review, "_search_crossref", search)
    data = atlas(engine.record("a"))
    first = review.update_reviews(data, tmp_path)
    assert first["counts"]["search_errors"] == 1
    assert first["records"][0]["search"]["error"] == "Provider timeout"
    assert first["records"][0]["search"]["status"] == "error"
    review.update_reviews(data, tmp_path)
    assert len(calls) == 1
    now[0] += review.SEARCH_RETRY_SEC + 1
    last = review.update_reviews(data, tmp_path)
    assert len(calls) == 2 and last["records"][0]["search"]["status"] == "complete"


def test_successful_query_cache_expires_but_offline_does_not_refresh(engine, tmp_path, monkeypatch):
    now, calls = [1000], []
    monkeypatch.setattr(review.time, "time", lambda: now[0])
    monkeypatch.setattr(review, "_search_crossref", lambda *args: calls.append(args) or [])
    data = atlas(engine.record("a"))
    review.update_reviews(data, tmp_path)
    now[0] += review.SEARCH_CACHE_TTL_SEC + 1
    review.update_reviews(data, tmp_path, online=False)
    assert len(calls) == 1
    review.update_reviews(data, tmp_path)
    assert len(calls) == 2


def test_known_and_routine_do_not_search_but_keep_existing_search_evidence(engine, tmp_path, monkeypatch):
    calls = []
    monkeypatch.setattr(review, "_search_crossref", lambda *args: calls.append(args) or [])
    data = atlas(engine.record("a"), engine.record("b", "size"))
    engine.statuses.update(a="known_result", b="routine_consequence")
    initial = review.update_reviews(data, tmp_path)
    assert not calls and all(r["search"]["status"] == "not_required" for r in initial["records"])
    assert initial["counts"]["known_result"] == initial["counts"]["routine_consequence"] == 1
    assert all(set(parents) == {"a", "b"} for _, parents in engine.classified)


def test_receipt_rejection_ast_mismatch_and_unvalidated_parents_are_excluded(engine, tmp_path):
    good, bad, wrong, empirical = (engine.record(name) for name in ("good", "bad", "wrong", "empirical"))
    Path(bad["lean_proof"]["receipt_path"]).unlink()
    wrong["conjecture"]["rhs_expr"]["value"] = 99
    empirical["status"] = "EMPIRICAL_SURVIVOR"
    result = review.update_reviews(atlas(good, bad, wrong, empirical), tmp_path, online=False)
    assert [r["id"] for r in result["records"]] == ["good"]
    assert engine.classified == [("good", {"good"})]


def test_stop_prevents_calls_and_initial_stop_does_not_write(engine, tmp_path, monkeypatch):
    directory = tmp_path / "absent"
    data = atlas(engine.record("a"))
    monkeypatch.setattr(review, "_search_crossref", lambda *args: pytest.fail("Stopped must not search"))
    review.update_reviews(data, directory, stop_requested=lambda: True)
    assert not directory.exists()
    stopped = [False]
    calls = []
    def search(*args):
        calls.append(args); stopped[0] = True
        return []
    monkeypatch.setattr(review, "_search_crossref", search)
    review.update_reviews(atlas(engine.record("a"), engine.record("b", "size")), tmp_path,
                          stop_requested=lambda: stopped[0])
    assert len(calls) == 1


def test_sidecar_lock_is_separate_and_nonblocking(engine, tmp_path):
    data = atlas(engine.record("a"))
    with writer_lock(tmp_path):
        review.update_reviews(data, tmp_path, online=False)
    with (tmp_path / ".novelty_reviews.lock").open("a+") as locked:
        fcntl.flock(locked, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(RuntimeError, match="novelty review writer"):
            review.update_reviews(data, tmp_path, online=False)


def test_corrupt_sidecar_is_not_silently_overwritten(engine, tmp_path):
    path = tmp_path / review.REVIEW_FILE
    path.write_text("{broken")
    with pytest.raises(ValueError):
        review.update_reviews(atlas(engine.record("a")), tmp_path, online=False)
    assert path.read_text() == "{broken"


def test_manual_potential_requires_completed_search_and_remains_nonexpert(engine, tmp_path, monkeypatch):
    monkeypatch.setattr(review, "_search_crossref", lambda *args: [])
    data = atlas(engine.record("a"))
    pending = review.update_reviews(data, tmp_path, online=False)["records"][0]
    with pytest.raises(ValueError, match="completed source search"):
        review.save_assessment(data, tmp_path, assessment(pending))
    checked = review.update_reviews(data, tmp_path)["records"][0]
    saved = review.save_assessment(data, tmp_path, assessment(checked))
    record = saved["records"][0]
    assert record["status"] == "potential_contribution"
    assert record["assessment"]["reviewer"] == "Named assessor"
    assert record["expert_review"] == {"status": "pending", "reviewer": None, "notes": None}
    assert review.get_reviews(data, tmp_path)["records"][0]["status"] == "potential_contribution"
    assert review.update_reviews(data, tmp_path, online=False)["records"][0]["status"] == "potential_contribution"


@pytest.mark.parametrize("result", ["fail", "unknown"])
def test_manual_potential_rejects_failed_or_unknown_exclusion_checks(engine, tmp_path, result):
    data = atlas(engine.record("a"))
    record = review.update_reviews(data, tmp_path, online=False)["records"][0]
    proposed = assessment(record); proposed["checks"][0]["status"] = result
    with pytest.raises(ValueError, match="three exclusion checks"):
        review.save_assessment(data, tmp_path, proposed)


@pytest.mark.parametrize("known", ["known_result", "routine_consequence"])
def test_manual_potential_cannot_override_mechanical_known_comparison(engine, tmp_path, known):
    engine.statuses["a"] = known
    data = atlas(engine.record("a"))
    record = review.update_reviews(data, tmp_path, online=False)["records"][0]
    with pytest.raises(ValueError, match="conflicts"):
        review.save_assessment(data, tmp_path, assessment(record))


@pytest.mark.parametrize("field", ["reviewer", "contribution", "closest_results", "uncertainties"])
def test_manual_assessment_requires_substantive_named_comparison(engine, tmp_path, field):
    data = atlas(engine.record("a"))
    record = review.get_reviews(data, tmp_path)["records"][0]
    proposed = assessment(record, status="awaiting_review")
    proposed[field] = [] if field in {"closest_results", "uncertainties"} else ""
    with pytest.raises(ValueError):
        review.save_assessment(data, tmp_path, proposed)


def test_source_change_invalidates_manual_assessment_and_old_fingerprint(engine, tmp_path, monkeypatch):
    monkeypatch.setattr(review, "_search_crossref", lambda *args: [])
    original = engine.record("a"); data = atlas(original)
    record = review.update_reviews(data, tmp_path)["records"][0]
    review.save_assessment(data, tmp_path, assessment(record))
    receipt_path = Path(original["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    source = Path(receipt["source_path"]); source.write_text("Changed valid fixture proof")
    assert not review.get_reviews(data, tmp_path)["records"]  # Stale source hash rejected.
    receipt["source_sha256"] = sha256(source); receipt_path.write_text(json.dumps(receipt))
    current = review.get_reviews(data, tmp_path)["records"][0]
    assert current["fingerprint"] != record["fingerprint"]
    assert current["status"] == "awaiting_review" and "assessment" not in current
    with pytest.raises(ValueError, match="currently validated"):
        review.save_assessment(data, tmp_path, assessment(record))


def test_potential_evidence_survives_failed_refresh_offline_and_recovery(engine, tmp_path, monkeypatch, clock):
    fail = [False]
    def search(*args):
        if fail[0]:
            raise TimeoutError("Provider unavailable")
        return []
    monkeypatch.setattr(review, "_search_crossref", search)
    data = atlas(engine.record("a"))
    checked = review.update_reviews(data, tmp_path)["records"][0]
    saved = review.save_assessment(data, tmp_path, assessment(checked))["records"][0]
    evidence = copy.deepcopy(saved["assessment"])
    clock[0][0] += review.SEARCH_CACHE_TTL_SEC + 1
    stale = review.get_reviews(data, tmp_path)["records"][0]
    assert stale["status"] == "awaiting_review" and "stale" in stale["assessment_gate"]
    fail[0] = True
    failed = review.update_reviews(data, tmp_path)["records"][0]
    assert failed["search"]["status"] == "error"
    assert failed["status"] == "awaiting_review" and "error" in failed["assessment_gate"]
    assert failed["assessment"] == evidence
    offline = review.update_reviews(data, tmp_path, online=False)["records"][0]
    read = review.get_reviews(data, tmp_path)["records"][0]
    assert offline["assessment"] == read["assessment"] == evidence
    assert offline["status"] == read["status"] == "awaiting_review"
    clock[0][0] += review.SEARCH_RETRY_SEC + 1
    fail[0] = False
    recovered = review.update_reviews(data, tmp_path)["records"][0]
    assert recovered["search"]["status"] == "complete"
    assert recovered["status"] == "potential_contribution" and recovered["assessment_gate"] is None
    assert recovered["assessment"] == evidence and recovered["reviewed_at"] == saved["reviewed_at"]


def test_named_evidence_survives_automatic_conflict_and_legacy_sidecar(engine, tmp_path, monkeypatch):
    monkeypatch.setattr(review, "_search_crossref", lambda *args: [])
    data = atlas(engine.record("a"))
    checked = review.update_reviews(data, tmp_path)["records"][0]
    review.save_assessment(data, tmp_path, assessment(checked))
    path = tmp_path / review.REVIEW_FILE
    legacy = json.loads(path.read_text()); legacy["records"][0]["assessment"].pop("evidence")
    path.write_text(json.dumps(legacy))
    engine.policy.write_text("policy-v2"); engine.statuses["a"] = "known_result"
    changed = review.get_reviews(data, tmp_path)["records"][0]
    assert changed["status"] == "awaiting_review" and changed["assessment"]["evidence"]["status"] == "potential_contribution"
    conflicting = review.update_reviews(data, tmp_path, online=False)["records"][0]
    assert conflicting["status"] == "known_result" and "known result" in conflicting["assessment_gate"]
    assert conflicting["assessment"]["reviewer"] == "Named assessor"
    engine.policy.write_text("policy-v3"); engine.statuses["a"] = "awaiting_review"
    recovered = review.update_reviews(data, tmp_path, online=False)["records"][0]
    assert recovered["status"] == "potential_contribution"
    assert recovered["assessment"]["evidence"] == conflicting["assessment"]["evidence"]


def test_validated_receipt_check_replaces_classifier_note_and_exports_without_duplicate_labels(engine, tmp_path, monkeypatch):
    from autonomous_math.novelty import review_classification
    original = review_classification.classify_record
    def classify(record, data):
        result = original(record, data)
        result["checks"].append({"label": "receipt_binding", "status": "info", "detail": "Caller must validate receipt."})
        return result
    monkeypatch.setattr(review_classification, "classify_record", classify)
    data = atlas(engine.record("a"))
    current = review.update_reviews(data, tmp_path, online=False)["records"][0]
    receipt_checks = [check for check in current["checks"] if check["label"] == "receipt_binding"]
    assert len(receipt_checks) == 1 and receipt_checks[0]["status"] == "pass"
    proposed = assessment(current, status="awaiting_review")
    proposed["checks"].extend(current["checks"])
    saved = review.save_assessment(data, tmp_path, proposed)["records"][0]
    labels = [check["label"] for check in saved["checks"]]
    assert len(labels) == len(set(labels))
    exported = dict(saved, reviewer="Named assessor")
    assert review.save_assessment(data, tmp_path, exported)["records"][0]["status"] == "awaiting_review"


def test_mismatched_conjecture_id_cannot_be_used_as_checked_parent(engine, tmp_path):
    good, wrong = engine.record("good"), engine.record("wrong")
    wrong["conjecture"]["id"] = "other"
    path = Path(wrong["lean_proof"]["receipt_path"])
    receipt = json.loads(path.read_text()); receipt["conjecture"] = wrong["conjecture"]
    path.write_text(json.dumps(receipt))
    result = review.update_reviews(atlas(good, wrong), tmp_path, online=False)
    assert [record["id"] for record in result["records"]] == ["good"]
    assert engine.classified == [("good", {"good"})]


def test_policy_change_reclassifies_only_on_update(engine, tmp_path):
    data = atlas(engine.record("a"))
    review.update_reviews(data, tmp_path, online=False)
    engine.policy.write_text("policy-v2"); engine.statuses["a"] = "known_result"
    assert review.get_reviews(data, tmp_path)["records"][0]["status"] == "awaiting_review"
    assert len(engine.classified) == 1
    assert review.update_reviews(data, tmp_path, online=False)["records"][0]["status"] == "known_result"
    assert len(engine.classified) == 2


def test_new_and_invalidated_parent_contexts_do_not_reuse_stale_classification(engine, tmp_path):
    first, second = engine.record("a"), engine.record("b")
    engine.statuses["a"] = "routine_consequence"
    initial = atlas(first)
    review.update_reviews(initial, tmp_path, online=False)
    expanded = atlas(first, second)
    assert review.get_reviews(expanded, tmp_path)["records"][0]["status"] == "awaiting_review"
    assert len(engine.classified) == 1
    review.update_reviews(expanded, tmp_path, online=False)
    assert len(engine.classified) == 3
    Path(second["lean_proof"]["receipt_path"]).unlink()
    assert review.get_reviews(expanded, tmp_path)["records"][0]["status"] == "awaiting_review"
    review.update_reviews(expanded, tmp_path, online=False)
    assert engine.classified[-1] == ("a", {"a"})


def test_registry_source_change_invalidates_cached_comparison(engine, tmp_path, monkeypatch):
    from autonomous_math.novelty import literature_crosscheck
    registry = tmp_path / "registry_policy.py"; registry.write_text("registry-v1")
    monkeypatch.setattr(literature_crosscheck, "__file__", str(registry))
    data = atlas(engine.record("a")); engine.statuses["a"] = "known_result"
    review.update_reviews(data, tmp_path, online=False)
    registry.write_text("registry-v2")
    assert review.get_reviews(data, tmp_path)["records"][0]["status"] == "awaiting_review"
    review.update_reviews(data, tmp_path, online=False)
    assert len(engine.classified) == 2


def test_persisted_potential_label_alone_is_not_an_assessment(engine, tmp_path):
    data = atlas(engine.record("a"))
    review.update_reviews(data, tmp_path, online=False)
    path = tmp_path / review.REVIEW_FILE
    saved = json.loads(path.read_text()); saved["records"][0]["status"] = "potential_contribution"
    path.write_text(json.dumps(saved))
    assert review.get_reviews(data, tmp_path)["records"][0]["status"] == "awaiting_review"
    saved["records"][0]["automatic_status"] = "potential_contribution"
    saved["records"][0]["automatic_assessment"]["status"] = "potential_contribution"
    path.write_text(json.dumps(saved))
    assert review.get_reviews(data, tmp_path)["records"][0]["status"] == "awaiting_review"


def test_automatic_classifier_cannot_promote_potential(engine, tmp_path):
    engine.statuses["a"] = "potential_contribution"
    with pytest.raises(ValueError, match="Automatic comparison cannot"):
        review.update_reviews(atlas(engine.record("a")), tmp_path, online=False)
    assert not (tmp_path / review.REVIEW_FILE).exists()


@pytest.fixture
def clock(monkeypatch):
    now, waits = [1000.0], []
    monkeypatch.setattr(review.time, "time", lambda: now[0])
    monkeypatch.setattr(review.time, "monotonic", lambda: now[0])
    def sleep(seconds):
        waits.append(seconds); now[0] += seconds
    monkeypatch.setattr(review.time, "sleep", sleep)
    return now, waits


def test_requests_are_paced_across_batches_and_invocations(engine, tmp_path, monkeypatch, clock):
    starts = []
    monkeypatch.setattr(review, "_search_crossref", lambda *args: starts.append(review.time.time()) or [])
    data = atlas(engine.record("a", "order"), engine.record("b", "size"), engine.record("c", "max_degree"))
    review.update_reviews(data, tmp_path, max_searches=2)
    review.update_reviews(data, tmp_path, max_searches=1)
    assert starts == [1000, 1001, 1002]
    assert all(wait <= 0.05 for wait in clock[1])


def test_rate_limit_stops_batch_and_provider_cooldown_survives_distinct_queries(engine, tmp_path, monkeypatch, clock):
    starts = []
    def search(*args):
        starts.append(review.time.time())
        if len(starts) == 1:
            raise HTTPError("https://api.crossref.org/works", 429, "Too many requests", {"Retry-After": "120"}, None)
        return []
    monkeypatch.setattr(review, "_search_crossref", search)
    data = atlas(engine.record("a", "order"), engine.record("b", "size"))
    first = review.update_reviews(data, tmp_path, max_searches=5)
    assert len(starts) == 1
    assert [record["search"]["status"] for record in first["records"]] == ["error", "pending"]
    stored = json.loads((tmp_path / review.REVIEW_FILE).read_text())
    assert stored["provider_retry_at"] == 1120
    data["theorems"]["c"] = engine.record("c", "max_degree", iteration=99)
    blocked = review.update_reviews(data, tmp_path, max_searches=5)
    assert len(starts) == 1
    assert blocked["records"][-1]["search"]["status"] == "pending"
    # Assessment writes also retain cooldown; an ordinary named assessment
    # changes review fields but cannot bypass the public-provider rate limit.
    record = blocked["records"][0]
    review.save_assessment(data, tmp_path, assessment(record, status="awaiting_review"))
    assert json.loads((tmp_path / review.REVIEW_FILE).read_text())["provider_retry_at"] == 1120
    clock[0][0] = 1121
    review.update_reviews(data, tmp_path, max_searches=1)
    assert len(starts) == 2


def test_rate_limit_retry_after_date_and_default_minimum(clock):
    from email.utils import formatdate
    dated = HTTPError("https://api.crossref.org", 429, "Slow down", {"Retry-After": formatdate(1180, usegmt=True)}, None)
    assert review._rate_limit_retry_at(dated) == 1180
    missing = HTTPError("https://api.crossref.org", 429, "Slow down", {}, None)
    assert review._rate_limit_retry_at(missing) == 1060


class Response:
    def __init__(self, data):
        self.raw = json.dumps(data).encode()
    def __enter__(self):
        return self
    def __exit__(self, *args):
        pass
    def read(self, size):
        return self.raw[:size]


def test_crossref_reads_public_metadata_with_real_software_identity(monkeypatch):
    called = []
    payload = {"status": "ok", "message": {"items": [{"title": ["A coding theorem"],
        "DOI": "10.1234/example", "published": {"date-parts": [[2020, 1, 2]]}}]}}
    def open_url(request, timeout):
        called.append((request, timeout)); return Response(payload)
    monkeypatch.setattr(review.urllib.request, "urlopen", open_url)
    results = review._search_crossref("coding distance", 3)
    assert results == [{"title": "A coding theorem", "url": "https://doi.org/10.1234/example", "year": 2020, "doi": "10.1234/example"}]
    request, timeout = called[0]
    assert timeout == 3 and "query.bibliographic=coding+distance" in request.full_url
    assert "MathFoundry" in request.get_header("User-agent") and "@" not in request.get_header("User-agent")


@pytest.mark.parametrize("payload", [None, {"status": "ok", "message": {}},
    {"status": "ok", "message": {"items": [None]}},
    {"status": "ok", "message": {"items": [{"title": ["Paper"], "DOI": "10.1/x", "published": None}]}}])
def test_invalid_crossref_metadata_is_error_not_successful_absence(monkeypatch, payload):
    monkeypatch.setattr(review.urllib.request, "urlopen", lambda *args, **kwargs: Response(payload))
    with pytest.raises(ValueError):
        review._search_crossref("coding", 3)


@pytest.mark.parametrize('mechanical_status', ['known_result', 'routine_consequence'])
def test_completed_extension_is_history_after_current_exact_comparison_resolves_it(engine, tmp_path, mechanical_status):
    snapshot = atlas(engine.record('resolved'))
    record = review.update_reviews(snapshot, tmp_path, online=False)['records'][0]
    prior = {'status': 'complete', 'outcome': 'possible_extension', 'summary': 'Earlier provisional comparison',
             'trace_path': 'retained/old/trace.json', 'challenge': {'status': 'complete', 'verdict': 'cleared_relative_advance'}}
    review.record_ai_review(snapshot, tmp_path, 'resolved', record['fingerprint'], prior)
    engine.statuses['resolved'] = mechanical_status
    engine.policy.write_text('policy-v2-resolves-exact-comparison')
    current = review.update_reviews(snapshot, tmp_path, online=False)
    result = current['records'][0]
    assert result['status'] == mechanical_status and result['ai_review']['superseded']
    assert all(result['ai_review'][key] == value for key, value in prior.items())
    assert current['counts']['ai_possible_extensions'] == current['counts']['ai_challenge_completed'] == 0
    assert current['counts']['ai_pending'] == 0 and current['counts']['ai_superseded'] == 1
