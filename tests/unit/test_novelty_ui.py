"""Exercise originality rendering boundaries without a browser dependency."""
from pathlib import Path
import shutil
import subprocess

import pytest


HTML = Path(__file__).parents[2] / "autonomous_math/dashboard/static/index.html"


def run_ui(assertions: str):
    node = shutil.which("node")
    if not node:
        pytest.skip("Node is required to exercise dashboard JavaScript")
    source = HTML.read_text()
    functions = source[source.index("      function safeLink("):source.index("      function proofRows()")]
    helpers = source[source.index("      const esc ="):source.index("      const fmt =")]
    formatters = source[source.index("      const symbols ="):source.index("      const statusMeta =")] + source[source.index("      function relation("):source.index("      function statement(")]
    harness = r'''
    const assert = require("node:assert/strict");
    const elements = new Map();
    const $ = (id) => {
      if (!elements.has(id)) elements.set(id, {
        value: id === "review-filter" ? "all" : "", innerHTML: "", textContent: "", scrollTop: 0, scrollLeft: 0, dataset: {}, hidden: false,
        classList: {toggle() {}, add() {}, remove() {}}, querySelectorAll() {return [];}, focus() {this.focused = true;}
      });
      return elements.get(id);
    };
    const document = {activeElement: null};
    const state = {snapshot: {theorems: [], novelty_reviews: {schema_version:1, records:[], counts:{}}}, selectedReview:null, reviewSignature:null};
    const records = () => state.snapshot.theorems;
    const fmt = String, date = String, json = JSON.stringify;
    const isCertified = (r) => r.status === "LEAN_CERTIFIED";
    const statement = (r) => esc(r.statement || r.id);
    let exported, requested, proofReply, apiError, lastToast;
    const api = async (url) => {requested = url; if (apiError) throw apiError; return proofReply;};
    const toast = (message) => {lastToast = message;};
    const download = (name, body, type) => {exported = {name, body: body instanceof Uint8Array ? body : JSON.parse(body), type};};
    const review = (id, status = "awaiting_review") => ({id, status, statement:"k + d ≤ n + 1", summary:"A useful formalization", contribution:"A checked proof", closest_results:[], checks:[], uncertainties:[], search:{status:"complete", results:[]}, expert_review:{status:"pending"}});
    '''
    subprocess.run([node, "-e", helpers + formatters + harness + functions + "(async () => {" + assertions + "})().catch(error => {console.error(error); process.exitCode = 1;});"], check=True, capture_output=True, text=True)


def test_review_distinguishes_missing_search_failure_and_empty_search():
    run_ui(r'''
    const r = review("proof-a");
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /No sources were returned/);
    assert.match($("review-inspector").innerHTML, /does not establish originality/);
    assert.doesNotMatch(reviewBadge("UNKNOWN_IN_LITERATURE"), /Potential original contribution/);
    assert.match(reviewBadge("potential_contribution"), /Potential original contribution — review needed/);
    r.search = {status:"error", error:"Provider timed out", results:[]};
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /Provider timed out/);
    assert.doesNotMatch($("review-inspector").innerHTML, /No sources were returned/);
    state.snapshot.novelty_reviews = {schema_version:1, status:"unavailable", error:"Review file is unreadable", records:[], counts:{}};
    renderOriginality();
    assert.match($("originality-service-state").textContent, /Review file is unreadable/);
    assert.equal($("review-count-known").textContent, "—");
    assert.doesNotMatch($("review-inspector").innerHTML, /Provider timed out/);
    ''')


def test_review_escapes_untrusted_evidence_and_rejects_non_web_links():
    run_ui(r'''
    const r = review("<script>evil</script>");
    r.summary = '<img src=x onerror="evil()">';
    r.contribution = "<svg onload=evil()>";
    r.closest_results = [{title:"<script>evil()</script>", url:"javascript:evil()", citation:"<img>", comparison:"<iframe>"}];
    r.search = {status:"complete", query:"<script>query</script>", results:[{title:"<svg>source</svg>", url:"file:///etc/passwd"}]};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    const markup = $("review-inspector").innerHTML + $("review-list").innerHTML;
    assert.doesNotMatch(markup, /<script>|<img|<svg|<iframe/);
    assert.doesNotMatch(markup, /href="(?:javascript:|file:)/);
    assert.match(markup, /&lt;script&gt;/);
    assert.match(safeLink('https://example.org/?q="hello"', '<img>'), /&lt;img&gt;/);
    assert.equal(safeLink("data:text/html,evil"), "");
    assert.equal(safeLink("javascript:evil()"), "");
    assert.match(safeLink("https://doi.org/10.1/test"), /rel="noopener noreferrer"/);
    ''')


def test_refresh_preserves_review_selection_and_filter_and_exports_exact_record():
    run_ui(r'''
    const a = review("a", "known_result"), b = review("b", "awaiting_review");
    b.assessment = {reviewer:"Automated assessor", reviewer_kind:"ai_agent", assessed_at:"2026-10-08"};
    state.snapshot.novelty_reviews.records = [a, b];
    state.snapshot.theorems = [{id:"b", status:"LEAN_CERTIFIED", conjecture:{exact:"statement"}, lean_proof:{receipt_path:"receipt.json"}}];
    state.selectedReview = "b";
    $("review-filter").value = "awaiting_review";
    $("review-search").value = "useful";
    $("review-list").scrollTop = 90;
    $("review-list").scrollLeft = 20;
    renderOriginality();
    renderOriginality();
    assert.equal(state.selectedReview, "b");
    assert.equal($("review-filter").value, "awaiting_review");
    assert.equal($("review-search").value, "useful");
    assert.equal($("review-list").scrollTop, 90);
    assert.equal($("review-list").scrollLeft, 20);
    assert.match($("review-inspector").innerHTML, /Recorded assessment by Automated assessor/);
    assert.match($("review-inspector").innerHTML, /Pending external assessment/);
    assert.deepEqual(reviewRows().map(r => r.id), ["b"]);
    proofReply = {found:true, theorem_id:"b", code:"theorem b : True := by trivial", file_name:"b.lean", receipt:{conjecture_id:"b", conjecture:{exact:"statement"}}};
    await exportReviewPacket();
    assert.equal(exported.name, "b.originality-review.json");
    assert.equal(exported.body.review.id, "b");
    assert.equal(exported.body.theorem.conjecture.exact, "statement");
    assert.match(exported.body.purpose, /does not certify mathematical novelty/);
    assert.equal(requested, "/api/lean_code/b");
    assert.equal(exported.body.proof_receipt.conjecture_id, "b");
    assert.equal(exported.body.lean_source, "theorem b : True := by trivial");
    ''')


def test_packet_export_requires_matching_validated_source_and_receipt():
    run_ui(r'''
    const r = review("proof/x");
    state.snapshot.novelty_reviews.records = [r];
    state.snapshot.theorems = [{id:r.id, status:"LEAN_CERTIFIED", conjecture:{exact:"statement"}}];
    state.selectedReview = r.id;
    proofReply = {found:true, theorem_id:r.id, code:"theorem x : True := by trivial", receipt:{conjecture_id:r.id, conjecture:{exact:"different statement"}}};
    await exportReviewPacket();
    assert.equal(requested, "/api/lean_code/proof%2Fx");
    assert.equal(exported, undefined);
    assert.match($("review-export-status").textContent, /was not exported/);
    apiError = new Error("Receipt validation failed");
    await exportReviewPacket();
    assert.equal(exported, undefined);
    assert.match(lastToast, /Receipt validation failed/);
    ''')


def test_poll_clears_inspector_if_selected_review_leaves_filtered_results():
    run_ui(r'''
    const a = review("a", "awaiting_review"), b = review("b", "awaiting_review");
    state.snapshot.novelty_reviews.records = [a, b];
    state.selectedReview = "a";
    $("review-filter").value = "awaiting_review";
    renderOriginality();
    a.status = "known_result";
    renderOriginality();
    assert.equal(state.selectedReview, "b");
    b.status = "known_result";
    renderOriginality();
    assert.equal(state.selectedReview, null);
    assert.match($("review-inspector").innerHTML, /No matching reviews/);
    assert.doesNotMatch($("review-inspector").innerHTML, /What this contributes/);
    ''')


def test_internal_references_require_checked_proofs_and_exclusion_labels_are_unambiguous():
    run_ui(r'''
    const r = review("reviewed-result", "routine_consequence");
    r.closest_results = [
      {title:"Checked parent", theorem_id:"parent", url:null},
      {title:"Unverified conjecture", theorem_id:"unverified", url:null},
      {title:"Missing reference", theorem_id:"absent", url:null}
    ];
    r.checks = [
      {label:"restatement", status:"pass"},
      {label:"specialization", status:"fail"},
      {label:"routine_consequence", status:"unknown"},
      {label:"receipt_validation", status:"pass"}
    ];
    state.snapshot.novelty_reviews.records = [r];
    state.snapshot.theorems = [
      {id:"parent", status:"LEAN_CERTIFIED"},
      {id:"unverified", status:"EMPIRICAL_SURVIVOR"}
    ];
    renderOriginality();
    const markup = $("review-inspector").innerHTML;
    assert.match(markup, /data-open-proof="parent">Inspect checked reference/);
    assert.doesNotMatch(markup, /data-open-proof="(?:unverified|absent)"/);
    assert.match(markup, /<strong>Restatement<\/strong><span class="badge reference">Ruled out/);
    assert.match(markup, /<strong>Specialization<\/strong><span class="badge reference">Detected/);
    assert.match(markup, /<strong>Routine consequence<\/strong><span class="badge reference">Not established/);
    assert.match(markup, /<strong>receipt validation<\/strong><span class="badge reference">pass/);
    ''')


def test_ai_queue_shows_reported_worker_state_counts_and_retry():
    run_ui(r'''
    const active = review("active"), failed = review("failed");
    active.ai_review = {status:"running", model:"configured-model", reasoning_effort:"high"};
    failed.ai_review = {status:"error", error:"Source provider unavailable", retry_at:2000};
    state.snapshot.novelty_reviews = {schema_version:1, records:[active, failed],
      counts:{ai_pending:2, ai_running:1, ai_complete:4, ai_errors:1, ai_unresolved:3},
      automation:{state:"running", current_id:"active", model:"configured-model", reasoning_effort:"high", heartbeat:1000}};
    renderOriginality();
    assert.equal($("ai-queue-state").textContent, "Running");
    assert.equal($("ai-queue-model").textContent, "configured-model · high");
    assert.equal($("ai-count-pending").textContent, "2");
    assert.equal($("ai-count-complete").textContent, "4");
    assert.equal($("ai-count-unresolved").textContent, "3");
    assert.equal($("ai-queue-current").hidden, false);
    assert.equal($("ai-queue-current").dataset.openReview, "active");
    assert.match($("ai-queue-detail").textContent, /Reviewing active.*1000/);
    assert.match($("ai-queue-error").textContent, /Retry ready; queued automatically/);
    state.snapshot.novelty_reviews.automation = {state:"stopped"};
    renderOriginality();
    assert.equal($("ai-queue-state").textContent, "Stopped");
    assert.equal($("ai-queue-current").hidden, true);
    state.snapshot.novelty_reviews = {status:"unavailable", schema_version:1, records:[], error:"Review store unavailable"};
    renderOriginality();
    assert.equal($("ai-queue-state").textContent, "Queue unavailable");
    assert.equal($("ai-count-complete").textContent, "—");
    ''')


def test_ai_assessment_is_provisional_and_does_not_change_mathematical_status():
    run_ui(r'''
    const r = review("result");
    r.automatic_status = "awaiting_review";
    r.automatic_assessment = {summary:"No exact deterministic match"};
    r.ai_review = {status:"complete", outcome:"known_result", summary:"A possible source match",
      contribution:"Formalization of a related bound", comparisons:[{source_id:"paper-1", title:"Known theorem", url:"https://example.org/paper", quote:"The bound holds.", comparison:"The hypotheses appear to agree."}],
      checks:[{label:"restatement", status:"fail", detail:"AI suggests equivalent claims."}],
      uncertainties:["The full theorem and its premises need independent checking."],
      model:"review-model", reasoning_effort:"high", usage:{input_tokens:100, output_tokens:20, cached_input_tokens:40}, duration_ms:2300, attempts:1};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    const markup = $("review-inspector").innerHTML;
    assert.equal(r.status, "awaiting_review");
    assert.match(markup, /Originality not established/);
    assert.match(markup, /Deterministic screening/);
    assert.match(markup, /AI suggests a known result/);
    assert.match(markup, /automated assessment is provisional/);
    assert.match(markup, /does not establish publication priority, originality, or expert endorsement/);
    assert.match(markup, /Source excerpt cited by AI/);
    assert.match(markup, /120 recorded tokens/);
    assert.doesNotMatch(markup, /Potential original contribution — review needed/);
    r.ai_review.outcome = "unresolved";
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /AI assessment complete; originality unresolved/);
    ''')


def test_ai_queue_filters_preserve_selection_and_remove_completed_running_rows():
    run_ui(r'''
    const a = review("a"), b = review("b");
    a.ai_review = {status:"running"};
    b.ai_review = {status:"complete", outcome:"unresolved", summary:"Specific source comparison"};
    state.snapshot.novelty_reviews.records = [a, b];
    $("review-filter").value = "ai_running";
    renderOriginality();
    assert.equal(state.selectedReview, "a");
    renderOriginality();
    assert.equal(state.selectedReview, "a");
    a.ai_review = {status:"complete", outcome:"known_result"};
    renderOriginality();
    assert.equal(state.selectedReview, null);
    assert.match($("review-inspector").innerHTML, /No matching reviews/);
    $("review-filter").value = "ai_unresolved";
    $("review-search").value = "specific source";
    renderOriginality();
    assert.equal(state.selectedReview, "b");
    assert.deepEqual(reviewRows().map(r => r.id), ["b"]);
    ''')


def test_ai_evidence_and_error_output_remain_escaped_with_safe_links():
    run_ui(r'''
    const r = review("ai-output");
    r.ai_review = {status:"complete", outcome:"unresolved", summary:"<script>bad()</script>", contribution:"<img src=x onerror=bad()>",
      comparisons:[{title:"<iframe>bad</iframe>", source_id:"<img>", url:"javascript:bad()", quote:"<script>quoted</script>", comparison:"<svg onload=bad()>"}],
      checks:[{label:"restatement", status:"unknown", detail:"<img>"}], uncertainties:["<svg>"], model:"<img>", reasoning_effort:"<iframe>"};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    const markup = $("review-inspector").innerHTML;
    assert.doesNotMatch(markup, /<script>|<img|<iframe|<svg|href="javascript:/);
    assert.match(markup, /&lt;script&gt;quoted/);
    r.ai_review = {status:"error", error:"<img>provider timeout", retry_at:2000};
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /&lt;img&gt;provider timeout/);
    assert.match($("review-inspector").innerHTML, /Retry ready; queued automatically/);
    assert.doesNotMatch($("review-inspector").innerHTML, /AI assessment complete/);
    ''')


def test_missing_ai_record_is_queued_only_for_eligible_unresolved_results():
    run_ui(r'''
    const queued = review("queued"), named = review("named"), known = review("known", "known_result");
    named.assessment = {reviewer:"Named assessor"};
    state.snapshot.novelty_reviews.records = [queued, named, known];
    $("review-filter").value = "ai_pending";
    renderOriginality();
    assert.deepEqual(reviewRows().map(r => r.id), ["queued"]);
    assert.equal($("ai-count-pending").textContent, "1");
    assert.match($("review-list").innerHTML, /AI queued/);
    assert.match($("review-inspector").innerHTML, /Queued for an AI mathematical comparison/);
    assert.match($("review-inspector").innerHTML, /AI mathematical assessment/);
    assert.doesNotMatch($("review-inspector").innerHTML, /AI literature assessment/);
    queued.ai_review = {status:"running"};
    $("review-filter").value = "ai_running";
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /checked source evidence/);
    assert.deepEqual(reviewRows().map(r => r.id), ["queued"]);
    ''')


def test_ai_progress_leads_classification_and_errors_filter_is_actionable():
    source = HTML.read_text()
    assert source.index('id="ai-queue-heading"') < source.index('id="review-count-awaiting"')
    assert '$("ai-errors-filter").addEventListener("click", filterAIReviewErrors)' in source
    run_ui(r'''
    const failed = review("failed"), done = review("done");
    failed.ai_review = {status:"error", error:"Bounded deadline exceeded", retry_at:0};
    done.ai_review = {status:"complete", outcome:"routine_consequence", summary:"A checked implication."};
    state.snapshot.novelty_reviews.records = [failed, done];
    state.snapshot.novelty_reviews.counts = {ai_pending:34, ai_running:1, ai_complete:5, ai_errors:1, ai_unresolved:2};
    renderOriginality();
    assert.equal($("ai-queue-progress").textContent, "5 of 41 AI assessments complete · 36 outstanding");
    assert.equal($("ai-errors-filter").disabled, false);
    assert.match($("ai-queue-error").textContent, /1 AI assessment failed.*Retry ready; queued automatically.*errors · inspect/);
    assert.doesNotMatch($("ai-queue-error").textContent, /Bounded deadline exceeded/);
    $("review-search").value = "unrelated search";
    $("review-filter").value = "ai_complete";
    filterAIReviewErrors();
    assert.equal($("review-search").value, "");
    assert.equal($("review-filter").value, "ai_errors");
    assert.equal($("review-filter").focused, true);
    assert.equal(state.selectedReview, "failed");
    assert.deepEqual(reviewRows().map(r => r.id), ["failed"]);
    renderOriginality();
    assert.equal(state.selectedReview, "failed");
    assert.match($("review-inspector").innerHTML, /Bounded deadline exceeded/);
    ''')


def test_ai_queue_error_banner_summarizes_failures_without_dumping_stderr():
    run_ui(r'''
    const first = review("first"), second = review("second");
    const rawError = "Codex stderr\nInterrupted request\n" + "raw diagnostics\n".repeat(100);
    first.ai_review = {status:"error", error:rawError, retry_at:0};
    second.ai_review = {status:"error", error:rawError, retry_at:2000};
    state.snapshot.novelty_reviews.records = [first, second];
    state.snapshot.novelty_reviews.automation = {state:"running", error:rawError};
    renderOriginality();
    const banner = $("ai-queue-error").textContent;
    assert.equal(banner, "2 AI assessments failed. Retry ready; queued automatically. Select “errors · inspect” for details.");
    assert.equal($("ai-queue-error").hidden, false);
    assert.doesNotMatch(banner, /Codex stderr|Interrupted request|raw diagnostics|\n/);
    assert.match($("review-inspector").innerHTML, /Codex stderr/);
    state.snapshot.novelty_reviews.records = [];
    renderOriginality();
    assert.equal($("ai-queue-error").textContent, "The automated reviewer reported an error. See the reviewer state above.");
    delete state.snapshot.novelty_reviews.automation.error;
    renderOriginality();
    assert.equal($("ai-queue-error").hidden, true);
    ''')


def test_completed_ai_summary_is_primary_without_changing_originality_status():
    run_ui(r'''
    const r = review("completed");
    r.summary = "Legacy deterministic awaiting-review prose";
    r.ai_review = {status:"complete", outcome:"routine_consequence", summary:"AI found an &lt;escaped&gt; <b>routine</b> implication", comparisons:[], checks:[], uncertainties:[]};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    const list = $("review-list").innerHTML, proof = proofOriginalitySummary(r.id), detail = $("review-inspector").innerHTML;
    for (const markup of [list, proof]) {
      assert.match(markup, /AI suggests a routine consequence · provisional/);
      assert.match(markup, /Originality not established/);
      assert.match(markup, /&lt;b&gt;routine&lt;\/b&gt;/);
      assert.doesNotMatch(markup, /Legacy deterministic awaiting-review prose|<b>routine/);
    }
    assert.ok(detail.indexOf("AI mathematical assessment · provisional") < detail.indexOf("Independent assessment status"));
    assert.equal(r.status, "awaiting_review");
    ''')


def test_ai_checked_comparisons_open_only_currently_certified_references():
    run_ui(r'''
    const r = review("target");
    r.ai_review = {status:"complete", outcome:"unresolved", comparisons:[
      {title:"Checked parent", theorem_id:"checked", url:null, comparison:"Useful evidence"},
      {title:"Unverified parent", theorem_id:"unverified", url:null},
      {title:"Missing parent", theorem_id:"missing", url:"javascript:bad()"}
    ]};
    state.snapshot.novelty_reviews.records = [r];
    state.snapshot.theorems = [{id:"checked", status:"LEAN_CERTIFIED"}, {id:"unverified", status:"EMPIRICAL_SURVIVOR"}];
    renderOriginality();
    const markup = $("review-inspector").innerHTML;
    assert.match(markup, /data-open-proof="checked">Inspect checked reference/);
    assert.doesNotMatch(markup, /data-open-proof="(?:unverified|missing)"|href="javascript:/);
    ''')


def test_retry_cooldown_updates_on_refresh_without_a_record_change():
    run_ui(r'''
    Date.now = () => 1000 * 1000;
    const r = review("retry");
    r.ai_review = {status:"error", error:"Model deadline exceeded", retry_at:2000};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /Retry after 2000 \(cooldown\)/);
    assert.match($("ai-queue-error").textContent, /Retry after 2000 \(cooldown\)/);
    Date.now = () => 2001 * 1000;
    renderOriginality();
    assert.match($("review-inspector").innerHTML, /Retry ready; queued automatically/);
    assert.doesNotMatch($("review-inspector").innerHTML, /Retry after 2000/);
    assert.match($("ai-queue-error").textContent, /Retry ready; queued automatically/);
    ''')


def test_superseded_attempt_is_history_not_an_active_error_or_retry():
    run_ui(r'''
    const r = review("covered", "routine_consequence");
    r.ai_review = {status:"error", error:"Prior failed attempt", retry_at:0, superseded:true, superseded_reason:"An exact checked comparison now covers this result."};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    assert.equal(aiReviewFor(r).status, "not_required");
    assert.equal($("ai-count-errors").textContent, "0");
    assert.equal($("ai-errors-filter").disabled, true);
    assert.equal($("ai-queue-error").hidden, true);
    assert.match($("review-inspector").innerHTML, /Review no longer queued/);
    assert.match($("review-inspector").innerHTML, /previous attempt is retained in diagnostics/);
    assert.doesNotMatch($("review-inspector").innerHTML, /Retry ready|Retry after/);
    assert.match($("review-inspector").innerHTML, /Prior failed attempt/);
    assert.equal(r.ai_review.status, "error");
    $("review-filter").value = "ai_errors";
    assert.deepEqual(reviewRows(), []);
    r.ai_review = {status:"complete", outcome:"routine_consequence", superseded:true};
    assert.equal(aiReviewFor(r).status, "complete");
    assert.equal(matchesAIReview(r, "ai_complete"), true);
    ''')


def test_source_coverage_and_locators_are_explicit_escaped_and_refreshable():
    run_ui(r'''
    const r = review("coverage");
    r.ai_review = {status:"complete", outcome:"possible_extension", summary:"An extension may be possible.",
      source_coverage:{local_mathlib:2, primary_literature:0, bibliographic_metadata:3, checked_local_theorem:1,
        limitations:["<script>unsafe limitation</script>"], unavailable:[{url:"<img>", reason:"Access blocked"}]},
      comparisons:[{source_type:"local_mathlib", title:"Mathlib theorem", locator:"Mathlib/Graph.lean:L10-L20 <svg>", version:"pinned <b>commit</b>", source_sha256:"a".repeat(64), text_sha256:"b".repeat(64), url:"javascript:evil()", quote:"checked excerpt"}]};
    state.snapshot.novelty_reviews.records = [r];
    renderOriginality();
    let markup = $("review-inspector").innerHTML;
    assert.match(markup, /Possible extension · provisional; independent review needed/);
    assert.match(markup, /Primary literature excerpts: <strong>0/);
    assert.match(markup, /Mathlib declaration excerpts: <strong>2/);
    assert.match(markup, /No primary-literature text coverage/);
    assert.match(markup, /Mathlib\/Graph.lean:L10-L20 &lt;svg&gt;/);
    assert.doesNotMatch(markup, /<script>|<img>|<svg>|<b>commit|href="javascript:/);
    assert.equal(r.status, "awaiting_review");
    r.ai_review.source_coverage.primary_literature = 1;
    renderOriginality();
    markup = $("review-inspector").innerHTML;
    assert.match(markup, /Primary literature excerpts: <strong>1/);
    assert.doesNotMatch(markup, /No primary-literature text coverage/);
    assert.equal(state.selectedReview, "coverage");
    assert.match(sourceProvenanceMarkup({}), /Evidence gap: exact locator, source version, source hash not recorded/);
    ''')


def test_complete_research_packet_download_uses_bound_server_export():
    source = HTML.read_text()
    assert 'data-packet-context="review"' in source
    assert 'data-packet-context="proof"' in source
    run_ui(r'''
    const r = review("packet");
    state.snapshot.theorems = [{id:r.id, status:"LEAN_CERTIFIED", conjecture:{id:r.id}, lean_proof:{receipt_path:"checked"}}];
    state.snapshot.novelty_reviews.records = [r];
    proofReply = {found:true, theorem_id:r.id, manifest:{theorem_id:r.id}, archive_base64:Buffer.from("PK\x03\x04zip-fixture").toString("base64")};
    await exportResearchPacket(r.id, "proof");
    assert.equal(requested, "/api/research_packet/packet");
    assert.equal(exported.name, "packet.research.zip");
    assert.equal(exported.type, "application/zip");
    assert.ok(exported.body instanceof Uint8Array);
    assert.match($("proof-export-status").textContent, /Markdown, JSON, exact Lean source, receipt provenance/);
    assert.match($("proof-export-status").textContent, /^Research packet ready; download requested/);
    exported = undefined;
    proofReply.theorem_id = "other";
    await exportResearchPacket(r.id);
    assert.equal(exported, undefined);
    assert.match($("review-export-status").textContent, /not exported.*did not match/);
    ''')


def test_changed_source_evidence_is_queued_and_historical_assessment_is_not_current():
    run_ui(r'''
    const r = review("refresh");
    r.ai_review = {status:"complete", outcome:"possible_extension", summary:"Old possible-extension assessment",
      evidence_current:false, refresh_pending:true, source_coverage:{primary_literature:1,local_mathlib:2}};
    state.snapshot.novelty_reviews.records = [r];
    $("review-filter").value = "ai_pending";
    renderOriginality();
    assert.equal(aiReviewFor(r).status, "pending");
    assert.deepEqual(reviewRows().map(row => row.id), ["refresh"]);
    assert.equal($("ai-count-complete").textContent, "0");
    assert.equal($("ai-count-pending").textContent, "1");
    assert.match($("review-list").innerHTML, /Evidence refresh queued/);
    assert.doesNotMatch($("review-list").innerHTML, /Old possible-extension assessment|AI suggests a possible extension/);
    assert.match($("review-inspector").innerHTML, /Previous source coverage/);
    assert.match($("review-inspector").innerHTML, /retained earlier assessment/);
    assert.equal(r.ai_review.status, "complete");
    assert.equal(r.status, "awaiting_review");
    ''')


def test_proposal_commentary_stays_labeled_and_escaped():
    run_ui(r'''
    const markup = proofCommentaryMarkup({writeup:{model_commentary:'<img src=x>Prospective claim', commentary_scope:'Not part of the <b>checked statement</b>'}});
    assert.match(markup, /Model commentary · not certified/);
    assert.match(markup, /&lt;img src=x&gt;/);
    assert.doesNotMatch(markup, /<img|<b>/);
    assert.equal(proofCommentaryMarkup({}), "");
    ''')


def test_proof_writeup_uses_existing_readable_ast_and_guard_renderers():
    run_ui(r'''
    const r = {conjecture:{lhs_expr:{node_type:"invariant",name:"parity_code_distance"},rel:"==",rhs_expr:{node_type:"binary_op",op:"+",left:{node_type:"invariant",name:"unique_neighbor_radius"},right:{node_type:"constant",value:1}},guard_predicate:{predicate_type:"comparison",invariant:"max_degree",op:"<=",threshold:2}},writeup:{what:"Raw \\Delta LaTeX stays in exported evidence",context:"Specific <b>mathematical context</b>",why:"A scoped implication."}};
    const markup = proofWriteupMarkup(r, {});
    assert.match(markup, /Lean proves .*d₂\(G\).* = .*u\(G\).*1/);
    assert.match(markup, /under the guard Δ\(G\) ≤ 2/);
    assert.match(markup, /Specific &lt;b&gt;mathematical context&lt;\/b&gt;/);
    assert.doesNotMatch(markup, /Raw|LaTeX|<b>/);
    ''')
