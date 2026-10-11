"""Receipt-bound literature reviews kept separately from the mathematical atlas.

Crossref supplies bibliographic leads, not theorem comparisons or novelty
certificates. Only an explicitly saved assessment can propose a contribution;
expert endorsement and confirmed originality are never inferred here.
"""
from __future__ import annotations

import copy
from contextlib import contextmanager
from email.utils import parsedate_to_datetime
import fcntl
import hashlib
import json
import math
from pathlib import Path
import time
import urllib.error
import urllib.parse
import urllib.request

from autonomous_math.core.ast import Conjecture
from autonomous_math.research_state import atomic_save_json, sha256, validate_receipt


REVIEW_FILE = "novelty_reviews.json"
SEARCH_RETRY_SEC = 60
SEARCH_CACHE_TTL_SEC = 7 * 24 * 60 * 60
STATUSES = {"awaiting_review", "known_result", "routine_consequence", "potential_contribution"}
AUTOMATIC_STATUSES = STATUSES - {"potential_contribution"}
REQUIRED_CHECKS = {"restatement", "specialization", "routine_consequence"}
PROVIDER = "Crossref public REST API"
PROVIDER_DOCS = "https://www.crossref.org/documentation/retrieve-metadata/rest-api/access-and-authentication/"


@contextmanager
def _review_lock(directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / ".novelty_reviews.lock").open("a+") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError("Another novelty review writer owns this directory") from exc
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def _load(directory):
    path = Path(directory) / REVIEW_FILE
    if not path.exists():
        return {"schema_version": 1, "updated_at": None, "records": [], "search_cache": {}}
    data = json.loads(path.read_text())
    if (not isinstance(data, dict) or data.get("schema_version") != 1
            or not isinstance(data.get("records"), list) or not isinstance(data.get("search_cache", {}), dict)):
        raise ValueError("Invalid novelty review sidecar")
    return data


def _fingerprint(record, receipt, receipt_path):
    content = {"conjecture": record["conjecture"], "receipt_schema_version": receipt["schema_version"],
               "receipt_sha256": sha256(Path(receipt_path)), "source_sha256": receipt["source_sha256"],
               "challenge_sha256": receipt["challenge_sha256"], "workspace_sha256": receipt["workspace_sha256"]}
    return hashlib.sha256(json.dumps(content, sort_keys=True, allow_nan=False).encode()).hexdigest()


def _query(conjecture):
    terms = {
        "parity_code_distance": "binary adjacency kernel code minimum distance",
        "parity_code_dimension": "binary adjacency matrix GF2 kernel dimension",
        "unique_neighbor_radius": "unique neighbor expansion stopping sets Tanner codes",
        "spectral_radius": "spectral radius", "graph_energy": "graph energy",
        "estrada_index": "Estrada index", "chromatic_number": "chromatic number",
        "clique_number": "clique number", "independence_number": "independence number",
    }
    variables = conjecture.lhs_expr.variables | conjecture.rhs_expr.variables
    variables |= getattr(conjecture.guard_predicate, "variables", set())
    if variables & {"parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"}:
        from autonomous_math.novelty.primary_sources import literature_topics
        terms_by_topic = {
            "griesmer": "binary linear codes Griesmer bound minimum distance dimension",
            "singleton": "linear codes Singleton bound dimension minimum distance",
            "plotkin": "binary linear codes Plotkin bound minimum distance dimension",
            "hamming": "binary linear codes Hamming sphere packing bound",
            "zero_forcing": "zero forcing maximum nullity arbitrary field graph maximum degree connected",
            "stopping": "linear codes stopping distance parity check Tanner graph",
            "expander": "expander codes unique neighbor expansion minimum distance",
        }
        topics = literature_topics({}, variables, conjecture.to_dict())
        if topics:
            return " ".join(terms_by_topic[t] for t in topics[:2] if t in terms_by_topic)[:400]
    if variables & {"parity_code_distance", "unique_neighbor_radius"}:
        return "binary linear codes stopping distance minimum distance parity check row weight two"
    if "parity_code_dimension" in variables:
        return "binary linear code dimension parity check matrix rank nullity"
    return ("finite simple graph " + " ".join(terms.get(name, name.replace("_", " "))
            for name in sorted(variables)))[:400]


def _pending_search(query):
    return {"status": "pending", "provider": PROVIDER, "query": query,
            "searched_at": None, "error": None, "results": []}


def _assessment_fields(data):
    if not isinstance(data, dict) or not isinstance(data.get("status"), str) or data["status"] not in STATUSES:
        raise ValueError("Assessment requires a supported review status")
    for field in ("id", "fingerprint", "reviewer", "summary", "contribution"):
        if not isinstance(data.get(field), str) or not data[field].strip():
            raise ValueError(f"Assessment requires nonempty {field}")
    closest = data.get("closest_results")
    if not isinstance(closest, list) or not closest:
        raise ValueError("Assessment requires at least one source comparison")
    for result in closest:
        if not isinstance(result, dict):
            raise ValueError("Invalid source comparison")
        for field in ("title", "url", "citation", "relationship", "comparison"):
            if not isinstance(result.get(field), str) or not result[field].strip():
                raise ValueError(f"Source comparison requires nonempty {field}")
        url = urllib.parse.urlsplit(result["url"])
        if url.scheme not in {"http", "https"} or not url.netloc or url.username or url.password:
            raise ValueError("Source comparisons require public HTTP(S) URLs")
    checks = data.get("checks")
    if not isinstance(checks, list) or any(not isinstance(check, dict) for check in checks):
        raise ValueError("Assessment requires structured comparison checks")
    labels = [check.get("label") for check in checks]
    if any(not isinstance(label, str) for label in labels) or len(set(labels)) != len(labels) or not REQUIRED_CHECKS <= set(labels):
        raise ValueError("Assessment requires distinct restatement, specialization, routine_consequence checks")
    for check in checks:
        if (not isinstance(check.get("label"), str) or check.get("status") not in {"pass", "fail", "unknown"}
                or not isinstance(check.get("detail"), str) or not check["detail"].strip()):
            raise ValueError("Each comparison check requires a result and specific detail")
    uncertainties = data.get("uncertainties")
    if (not isinstance(uncertainties, list) or not uncertainties
            or any(not isinstance(item, str) or not item.strip() for item in uncertainties)):
        raise ValueError("Assessment requires explicit remaining uncertainties")
    if data["status"] == "potential_contribution":
        if any(check["status"] != "pass" for check in checks if check["label"] in REQUIRED_CHECKS):
            raise ValueError("Potential contribution requires all three exclusion checks to pass")
        if data["contribution"].strip().lower() == "not yet established":
            raise ValueError("Potential contribution requires a specific claimed advance")
    return {key: copy.deepcopy(data[key]) for key in
            ("status", "summary", "contribution", "closest_results", "checks", "uncertainties")}


def _apply_assessment(record):
    """Gate the displayed status without discarding a named comparison's evidence."""
    record.update(copy.deepcopy(record["automatic_assessment"]))
    record["assessment_gate"] = None
    assessment = record.get("assessment")
    if assessment:
        fields = _assessment_fields(assessment["evidence"])
        reason = None
        if fields["status"] == "potential_contribution":
            search = record["search"]
            searched_at = search.get("searched_at")
            if record["automatic_status"] in {"known_result", "routine_consequence"}:
                reason = "The current automated comparison identifies a known result or routine consequence."
            elif not record.get("classification_revision"):
                reason = "The checked-parent context or comparison policy needs refresh."
            elif search.get("status") != "complete":
                reason = "A completed source search is required; current search status is " + search.get("status", "pending") + "."
            elif (type(searched_at) not in {int, float} or not math.isfinite(searched_at)
                    or time.time() - searched_at >= SEARCH_CACHE_TTL_SEC):
                reason = "The source search is stale and needs refresh."
        if reason:
            record["assessment_gate"] = reason
        else:
            record.update(fields)
    # The current receipt validation replaces any classifier/assessment note
    # with the same label, keeping exported checklists unambiguous and reusable.
    record["checks"] = [{"label": "receipt_binding", "status": "pass",
        "detail": "Current source, challenge, dependencies and compiler validate; receipt AST equals the committed AST."},
        *(check for check in record.get("checks", []) if check.get("label") != "receipt_binding")]
    _apply_ai_review_gate(record)


def _apply_ai_review_gate(record):
    """Retain old attempts without advertising resolved work as an active failure."""
    ai = record.get("ai_review")
    if not ai:
        return
    ai.pop("superseded", None)
    ai.pop("superseded_reason", None)
    if (ai.get("status") == "complete" and ai.get("outcome") == "possible_extension"
            and record.get("automatic_status") in {"known_result", "routine_consequence"}):
        ai.update(superseded=True,
            superseded_reason="A current exact checked comparison resolves this earlier provisional extension as known or routine. Its model assessment is retained as history.")
        return
    if ai.get("status") not in {"running", "error"}:
        return
    if record.get("automatic_status") in {"known_result", "routine_consequence"}:
        ai.update(superseded=True,
            superseded_reason="An exact checked comparison now resolves this result. The earlier model attempt is retained as history; no retry is needed.")
    elif record.get("assessment"):
        ai.update(superseded=True,
            superseded_reason="A saved assessment now covers this result. The earlier model attempt is retained as history.")


def _records(atlas, saved, classify=False, directory=None):
    previous = {record.get("id"): record for record in saved["records"] if isinstance(record, dict)}
    fingerprints, reviews, validated = {}, [], {}
    for identifier, record in sorted(atlas.get("theorems", {}).items()):
        if record.get("status") != "LEAN_CERTIFIED" or record.get("id") != identifier:
            continue
        path = (record.get("lean_proof") or {}).get("receipt_path", "")
        receipt, _ = validate_receipt(path, identifier, fingerprints)
        if not receipt or not receipt.get("conjecture") or receipt["conjecture"] != record.get("conjecture"):
            continue
        if receipt["conjecture"].get("id") != identifier:
            continue
        validated[identifier] = (record, receipt, _fingerprint(record, receipt, path))
    classified_atlas = dict(atlas, theorems={identifier: item[0] for identifier, item in validated.items()})
    from autonomous_math.novelty import review_classification, literature_crosscheck, routine_filter
    context = sorted((identifier, item[2]) for identifier, item in validated.items())
    revision = hashlib.sha256(json.dumps([sha256(Path(review_classification.__file__)),
        sha256(Path(literature_crosscheck.__file__)), sha256(Path(routine_filter.__file__)), context], sort_keys=True).encode()).hexdigest()
    for identifier, (record, receipt, fingerprint) in validated.items():
        conjecture = Conjecture.from_dict(receipt["conjecture"])
        prior = previous.get(identifier)
        unchanged = prior and prior.get("fingerprint") == fingerprint
        automatic = (prior or {}).get("automatic_assessment", {})
        cached = (unchanged and prior.get("automatic_status") in AUTOMATIC_STATUSES
                  and isinstance(automatic, dict) and automatic.get("status") == prior["automatic_status"]
                  and prior.get("classification_revision") == revision)
        if cached:
            classified = {key: copy.deepcopy(automatic.get(key)) for key in
                ("status", "summary", "contribution", "closest_results", "checks", "uncertainties")}
        elif classify:
            classified = review_classification.classify_record(record, classified_atlas)
        else:
            classified = {"status": "awaiting_review", "summary": "The checked proof awaits a saved mathematical literature comparison.",
                "contribution": "not yet established", "closest_results": [], "checks": [],
                "uncertainties": ["No literature assessment is saved for this exact proof.",
                                  "Kernel certification establishes correctness, not originality."]}
        if not isinstance(classified, dict) or classified.get("status") not in AUTOMATIC_STATUSES:
            raise ValueError("Automatic comparison cannot assert a potential contribution")
        review = {"id": identifier, "statement": conjecture.to_latex(), "fingerprint": fingerprint,
                  **classified, "search": _pending_search(_query(conjecture)),
                  "automatic_status": classified["status"], "automatic_assessment": copy.deepcopy(classified),
                  "classification_revision": revision if classify or cached else None,
                  "expert_review": {"status": "pending", "reviewer": None, "notes": None}, "reviewed_at": None}
        # Reuse only a proof/context/policy-bound automatic comparison. Reads
        # leave changed contexts pending; updates calculate their classification.
        if classified["status"] in {"known_result", "routine_consequence"}:
            review["search"]["status"] = "not_required"
        if unchanged:
            ai_review = prior.get("ai_review")
            if isinstance(ai_review, dict) and ai_review.get("status") in {"running", "complete", "error"}:
                review["ai_review"] = copy.deepcopy(ai_review)
            search = prior.get("search", {})
            if search.get("query") == review["search"]["query"] and search.get("status") in {"pending", "complete", "error", "not_required"}:
                review["search"] = copy.deepcopy(search)
                if classified["status"] in {"known_result", "routine_consequence"} and search["status"] == "pending":
                    review["search"]["status"] = "not_required"
            assessment = prior.get("assessment")
            if isinstance(assessment, dict):
                try:
                    # Existing sidecars kept the evidence in active display
                    # fields. Migrate it once; subsequent gating never erases it.
                    evidence = assessment.get("evidence", dict(prior, reviewer=assessment.get("reviewer")))
                    fields = _assessment_fields(evidence)
                    if evidence["id"] != identifier or evidence["fingerprint"] != fingerprint:
                        raise ValueError("Named assessment does not match the current proof")
                    retained = copy.deepcopy(assessment)
                    retained["evidence"] = dict(fields, id=identifier, fingerprint=fingerprint,
                                                reviewer=evidence["reviewer"])
                    review.update(assessment=retained, reviewed_at=prior.get("reviewed_at"))
                except ValueError:
                    pass
        _apply_assessment(review)
        if directory is not None and review.get("ai_review", {}).get("status") == "complete":
            from autonomous_math.novelty.primary_sources import SOURCE_REVISION, current_evidence_key, source_refresh_due
            from autonomous_math.novelty.model_review import REVIEW_REVISION, validate_completed_review
            ai = review["ai_review"]
            key = current_evidence_key(review, record, directory)
            current = (ai.get("sources_revision") == SOURCE_REVISION and ai.get("revision") == REVIEW_REVISION
                       and ai.get("evidence_key") == key)
            ai.update(evidence_current=current, refresh_pending=not current and not ai.get("superseded"))
            if current:
                try:
                    validate_completed_review(review,classified_atlas,directory,fingerprints=fingerprints)
                    ai.pop("evidence_error",None)
                except (ValueError,OSError) as exc:
                    ai.update(evidence_current=False,refresh_pending=not ai.get("superseded"),evidence_error=str(exc)[:400])
            review["source_refresh_due"] = source_refresh_due(review,record,directory)
            review["source_evidence_key"] = key
        reviews.append(review)
    return reviews


def _public(records, updated_at):
    counts = {status: sum(record["status"] == status for record in records) for status in sorted(STATUSES)}
    counts["search_errors"] = sum(record["search"]["status"] == "error" for record in records)
    for state in ("running", "complete", "error"):
        counts["ai_errors" if state == "error" else "ai_" + state] = sum(
            record.get("ai_review", {}).get("status") == state
            and not record["ai_review"].get("superseded") and not record["ai_review"].get("refresh_pending") for record in records)
    counts["ai_superseded"] = sum(bool(record.get("ai_review", {}).get("superseded")) for record in records)
    counts["ai_pending"] = sum(record["status"] == "awaiting_review" and (not record.get("ai_review") or bool(record["ai_review"].get("refresh_pending")))
                               and not record.get("assessment") for record in records)
    counts["ai_unresolved"] = sum(record.get("ai_review", {}).get("status") == "complete"
        and not record["ai_review"].get("refresh_pending") and record["ai_review"].get("outcome") == "unresolved" for record in records)
    current = [record["ai_review"] for record in records if record.get("ai_review")
               and not record["ai_review"].get("refresh_pending") and not record["ai_review"].get("superseded")]
    counts["ai_possible_extensions"] = sum(ai.get("status") == "complete" and ai.get("outcome") == "possible_extension"
        and ai.get("challenge", {}).get("verdict") == "cleared_relative_advance" for ai in current)
    counts["ai_challenge_completed"] = sum(ai.get("challenge", {}).get("status") == "complete" for ai in current)
    counts["ai_challenge_errors"] = sum(ai.get("status") == "error"
        and any(item.get("stage") == "challenge" and item.get("status") in {"error", "rejected"}
                for item in ai.get("requests", [])) for ai in current)
    return {"schema_version": 1, "updated_at": updated_at, "counts": counts, "records": records}


def get_reviews(atlas, directory):
    """Return current receipt-bound reviews without network access or file writes."""
    saved = _load(directory)
    result = _public(_records(atlas, saved, directory=directory), saved["updated_at"])
    path = Path(directory) / "novelty_review_worker.json"
    result["automation"] = json.loads(path.read_text()) if path.exists() else {"state": "stopped"}
    if (result["automation"].get("state") in {"running", "idle"}
            and time.time() - result["automation"].get("heartbeat", 0) > 15):
        result["automation"]["state"] = "stopped"
        result["automation"]["error"] = "The automated review worker heartbeat is stale. Reviews resume with the research runner."
    return result


def record_ai_review(atlas, directory, identifier, fingerprint, ai_review):
    """Persist model triage separately; it cannot grant an originality status."""
    if ai_review.get("status") not in {"running", "complete", "error"}:
        raise ValueError("Invalid AI review state")
    if ai_review["status"] == "complete" and ai_review.get("outcome") not in {
            "known_result", "routine_consequence", "unresolved", "possible_extension"}:
        raise ValueError("AI triage cannot establish a potential contribution")
    with _review_lock(directory):
        saved = _load(directory)
        if (Path(directory) / "cumulative_discovery_atlas.json").exists():
            from autonomous_math.research_state import load_snapshot
            atlas = load_snapshot(directory)
        records = _records(atlas, saved, classify=True, directory=directory)
        record = next((item for item in records if item["id"] == identifier), None)
        if not record or record["fingerprint"] != fingerprint:
            raise ValueError("AI review does not match the current validated proof")
        record["ai_review"] = copy.deepcopy(ai_review)
        _apply_ai_review_gate(record)
        # Only this target belongs to the asynchronous worker. Never replace
        # another review with data from an earlier atlas snapshot.
        merged = {item["id"]: item for item in saved["records"]}
        prior = merged.get(identifier)
        if prior and prior.get("fingerprint") != fingerprint:
            raise ValueError("Saved review now belongs to a different proof")
        merged[identifier] = record
        result = _public(list(merged.values()), time.time())
        atomic_save_json(dict(saved, **result), Path(directory) / REVIEW_FILE)
        return result


def _search_crossref(query, timeout_sec):
    parameters = urllib.parse.urlencode({"query.bibliographic": query, "rows": 5,
        "select": "DOI,title,published,URL"})
    request = urllib.request.Request("https://api.crossref.org/works?" + parameters,
        headers={"Accept": "application/json", "User-Agent": "MathFoundry/1.0 (local theorem literature review)"})
    with urllib.request.urlopen(request, timeout=timeout_sec) as response:
        raw = response.read(262145)
    if len(raw) > 262144:
        raise ValueError("Crossref response exceeds the bounded metadata size")
    data = json.loads(raw)
    if (not isinstance(data, dict) or data.get("status") != "ok"
            or not isinstance(data.get("message"), dict) or not isinstance(data["message"].get("items"), list)):
        raise ValueError("Crossref did not return a valid works response")
    results = []
    for item in data["message"]["items"][:5]:
        if not isinstance(item, dict):
            raise ValueError("Invalid Crossref work metadata")
        title = item.get("title", [])
        doi = item.get("DOI")
        if not isinstance(title, list) or not title or not isinstance(title[0], str) or not isinstance(doi, str):
            continue
        published = item.get("published", {})
        if not isinstance(published, dict):
            raise ValueError("Invalid Crossref publication date metadata")
        date = published.get("date-parts", [])
        if not isinstance(date, list):
            raise ValueError("Invalid Crossref publication date parts")
        year = date[0][0] if date and isinstance(date[0], list) and date[0] and type(date[0][0]) is int else None
        results.append({"title": title[0][:500], "url": "https://doi.org/" + urllib.parse.quote(doi, safe="/"),
                        "year": year, "doi": doi[:300]})
    return results


def _wait_for_request_slot(next_request_at, stop_requested):
    deadline = time.monotonic() + min(1, max(0, next_request_at - time.time()))
    while time.monotonic() < deadline:
        if stop_requested and stop_requested():
            return False
        time.sleep(min(0.05, max(0, deadline - time.monotonic())))
    return not (stop_requested and stop_requested())


def _rate_limit_retry_at(error):
    value = error.headers.get("Retry-After") if error.headers else None
    now, delay = time.time(), SEARCH_RETRY_SEC
    if value:
        try:
            seconds = float(value)
            if math.isfinite(seconds):
                delay = max(delay, seconds)
        except ValueError:
            try:
                delay = max(delay, parsedate_to_datetime(value).timestamp() - now)
            except (ValueError, TypeError, OverflowError):
                pass
    return now + delay


def update_reviews(atlas, directory, max_searches=2, online=True, timeout_sec=3, stop_requested=None):
    """Classify current checked proofs and persist at most max_searches scholarly calls.

    The socket timeout bounds each Crossref network operation. Failed requests
    remain errors and retry after a delay; metadata absence never implies novelty.
    """
    if type(max_searches) is not int or max_searches < 0:
        raise ValueError("max_searches must be a nonnegative integer")
    if not math.isfinite(timeout_sec) or timeout_sec <= 0:
        raise ValueError("timeout_sec must be finite and positive")
    if stop_requested and stop_requested():
        return get_reviews(atlas, directory)
    with _review_lock(directory):
        saved = _load(directory)
        records = _records(atlas, saved, classify=True, directory=directory)
        cache = copy.deepcopy(saved.get("search_cache", {}))
        retry_at = saved.get("provider_retry_at", 0)
        next_request_at = saved.get("next_request_at", 0)
        searches = 0
        order = sorted(records, key=lambda record: (-atlas["theorems"][record["id"]].get("discovered_iteration", 0), record["id"]))
        for record in order:
            if stop_requested and stop_requested():
                break
            if record["status"] in {"known_result", "routine_consequence"}:
                continue
            query = record["search"]["query"]
            cached = cache.get(query)
            fresh = cached and cached.get("status") == "complete" and (
                isinstance(cached.get("searched_at"), (int, float))
                and time.time() - cached["searched_at"] < SEARCH_CACHE_TTL_SEC)
            if cached and (fresh or time.time() < cached.get("retry_at", 0)):
                record["search"] = {key: copy.deepcopy(value) for key, value in cached.items() if key != "retry_at"}
                continue
            if not online or searches >= max_searches or time.time() < retry_at:
                continue
            if not _wait_for_request_slot(next_request_at, stop_requested):
                break
            searches += 1
            search = dict(_pending_search(query), searched_at=time.time())
            next_request_at = time.time() + 1
            rate_limited = False
            try:
                search.update(status="complete", results=_search_crossref(query, timeout_sec))
            except InterruptedError:
                raise
            except urllib.error.HTTPError as exc:
                search.update(status="error", error=str(exc)[:1000])
                if exc.code == 429:
                    retry_at = _rate_limit_retry_at(exc)
                    rate_limited = True
            except (OSError, ValueError, TimeoutError) as exc:
                search.update(status="error", error=str(exc)[:1000])
            record["search"] = search
            cache[query] = dict(search, **({"retry_at": max(retry_at, time.time() + SEARCH_RETRY_SEC)} if search["status"] == "error" else {}))
            if rate_limited:
                break
        # A refreshed search can fail or recover during this very update. Apply
        # its current gate now, before returning or persisting the active status.
        for record in records:
            _apply_assessment(record)
        updated_at = time.time()
        result = _public(records, updated_at)
        atomic_save_json(dict(result, search_cache=cache, provider_retry_at=retry_at,
                             next_request_at=next_request_at), Path(directory) / REVIEW_FILE)
        return result


def save_assessment(atlas, directory, assessment):
    """Save a named, source-comparing assessment bound to an unchanged checked proof.

    Potential contribution is a review hypothesis, never expert endorsement or
    confirmed originality. Automatic known/routine checks cannot be overridden.
    """
    fields = _assessment_fields(assessment)
    with _review_lock(directory):
        saved = _load(directory)
        records = _records(atlas, saved, classify=True, directory=directory)
        record = next((record for record in records if record["id"] == assessment["id"]), None)
        if not record or record["fingerprint"] != assessment["fingerprint"]:
            raise ValueError("Assessment is not bound to a currently validated exact proof")
        if fields["status"] == "potential_contribution":
            if record["automatic_status"] in {"known_result", "routine_consequence"}:
                raise ValueError("Potential contribution conflicts with an automated known/routine comparison")
            if record["search"].get("status") != "complete":
                raise ValueError("Potential contribution requires a completed source search")
        now = time.time()
        record.update(reviewed_at=now, assessment={"reviewer": assessment["reviewer"].strip(),
            "reviewer_kind": assessment.get("reviewer_kind", "unspecified"), "assessed_at": now,
            "evidence": dict(fields, id=record["id"], fingerprint=record["fingerprint"],
                             reviewer=assessment["reviewer"].strip())})
        _apply_assessment(record)
        if record["assessment_gate"]:
            raise ValueError(record["assessment_gate"])
        result = _public(records, now)
        atomic_save_json(dict(result, search_cache=saved.get("search_cache", {}),
            provider_retry_at=saved.get("provider_retry_at", 0), next_request_at=saved.get("next_request_at", 0)),
            Path(directory) / REVIEW_FILE)
        return result
