"""Trust boundary, repair loop, service protocol and subprocess cleanup checks."""
import json
import os
from pathlib import Path
import subprocess
import time

import pytest

from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.prover.codex_synthesis import (
    CodexProofSynthesizer, DISABLED_FEATURES, PROOF_SCHEMA, SynthesisError,
    terminate_process_group, validate_json_schema, validate_proof_candidate, validate_synthesis_response,
)
from autonomous_math.prover.lean_prover import LeanProofSearch, LeanToolchain, _target_axiom_report
from autonomous_math.prover.trusted_lean import render_challenge
from autonomous_math.research_state import ALLOWED_AXIOMS, validate_receipt


def goal(identifier="generated_order_nonnegative", guard=None):
    return Conjecture.create(id=identifier, lhs=InvariantNode("order"), rel=">=",
                            rhs=ConstantNode(0), guard=guard)


def fake_cli(tmp_path, body="exact Nat.cast_nonneg _", mode="ok"):
    path = tmp_path / "fake_codex"
    path.write_text("#!/usr/bin/env python3\n" + f'''
import json, subprocess, sys, time
from pathlib import Path
args=sys.argv[1:]
answer=Path(args[args.index('--output-last-message')+1])
prompt=sys.stdin.read()
if {mode!r} == 'timeout':
    child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'])
    (answer.parent/'child.pid').write_text(str(child.pid))
    time.sleep(60)
if {mode!r} == 'error':
    print('fixture service failure',file=sys.stderr)
    sys.exit(7)
proof={body!r}
if {mode!r} == 'repair' and 'round_1' in str(answer):
    proof='exact not_a_real_lemma'
data={{'outcome':'proof','proof_body':proof,'imports':[],'explanation':'The number of vertices is nonnegative. This foundational property supports checked bound composition.','counterexample':None}}
if {mode!r} == 'legacy':
    data.pop('outcome'); data.pop('counterexample')
if {mode!r} == 'bad_counterexample':
    data.update(outcome='counterexample',proof_body='',counterexample={{'order':65,'edges':[]}})
schema=json.loads(Path(args[args.index('--output-schema')+1]).read_text())
if 'missing_lemmas' in schema.get('properties',{{}}):
    data['missing_lemmas']=[]
answer.write_text('not-json' if {mode!r} == 'malformed' else json.dumps(data))
print(json.dumps({{'type':'thread.started','thread_id':'fixture-thread','model':'fixture-model'}}))
print(json.dumps({{'type':'turn.completed','usage':{{'input_tokens':17,'output_tokens':9}}}}))
''')
    path.chmod(0o755)
    return path


@pytest.mark.parametrize("body", [
    "sorry", "admit", "exact sorryAx _ true", "theorem replacement : True := by trivial",
    "exact True.intro\nend Escape\naxiom forged : False", "#eval IO.println 1",
    "run_tac liftIO (IO.println 1)", "native_decide", "decide +native",
    "decide +revert +native", "decide (config := { native := true })", "exact eval% (True.intro)",
    "decide -- hide native option\n +native", "set_option maxHeartbeats 0",
    "exact True.intro /-", "open scoped BigOperators", "exact True.intro\x00",
])
def test_generated_body_cannot_escape_or_enlarge_trust(body):
    with pytest.raises(ValueError):
        validate_proof_candidate({"proof_body": body, "imports": [], "explanation": ""}, ())


def test_only_narrow_explicit_imports_and_local_proof_arguments_are_allowed():
    body = "have h : (0 : ℕ) ≤ 0 := by omega\nexact_mod_cast h"
    data = {"proof_body": body, "imports": ["Mathlib.Tactic"], "explanation": "A known fact."}
    with pytest.raises(ValueError, match="allowlist"):
        validate_proof_candidate(data, ())
    assert validate_proof_candidate(data, ("Mathlib.Tactic",))["proof_body"] == body
    with pytest.raises(ValueError):
        validate_proof_candidate({**data, "theorem": "False"}, ("Mathlib.Tactic",))


def response(outcome="proof", proof_body="exact Nat.cast_nonneg _", counterexample=None, imports=None):
    return {"outcome": outcome, "proof_body": proof_body, "imports": imports or [],
            "explanation": "The host checks the mathematical evidence.", "counterexample": counterexample}


def test_strict_cli_contract_does_not_accept_legacy_fixture_fields():
    legacy = {"proof_body": "exact Nat.cast_nonneg _", "imports": [], "explanation": ""}
    with pytest.raises(ValueError, match="required"):
        validate_synthesis_response(legacy, ())
    assert validate_proof_candidate(legacy, ())["outcome"] == "proof"
    assert validate_synthesis_response(response(), ())["counterexample"] is None


@pytest.mark.parametrize("data", [
    response(outcome="unknown", proof_body="", counterexample={"order": 0, "edges": []}),
    response(outcome="unknown", proof_body="  "),
    response(outcome="counterexample", proof_body=""),
    response(outcome="counterexample", proof_body="", counterexample={"order": 2, "edges": [[0, 1]]}, imports=["Mathlib.Tactic"]),
    response(outcome="counterexample", counterexample={"order": 2, "edges": [[0, 1]]}),
    response(counterexample={"order": 2, "edges": [[0, 1]]}),
    response(proof_body=""),
    {**response(), "outcome": "refuted"},
    {**response(), "explanation": "x" * 4001},
])
def test_outcomes_cannot_mix_proof_counterexample_and_unknown_fields(data):
    with pytest.raises(ValueError):
        validate_synthesis_response(data, ("Mathlib.Tactic",))


@pytest.mark.parametrize("graph", [
    {"order": True, "edges": []}, {"order": -1, "edges": []}, {"order": 65, "edges": []},
    {"order": 2, "edges": [[0]]}, {"order": 2, "edges": [[0, 1, 2]]},
    {"order": 2, "edges": [[False, 1]]}, {"order": 2, "edges": [[0, 1.0]]},
    {"order": 2, "edges": [[0, 64]]}, {"order": 2, "edges": [[-1, 0]]},
    {"order": 2, "edges": [[0, 1]] * 2017}, {"order": 2, "edges": [], "invariants": {"order": 0}},
])
def test_counterexample_response_graph_is_bounded_structured_data(graph):
    with pytest.raises(ValueError):
        validate_synthesis_response(response("counterexample", "", graph), ())


def test_nonproof_contract_accepts_only_unknown_or_explicit_unverified_graph():
    assert validate_synthesis_response(response("unknown", ""), ())["outcome"] == "unknown"
    graph = {"order": 2, "edges": [[0, 1]]}
    assert validate_synthesis_response(response("counterexample", "", graph), ())["counterexample"] == graph
    with pytest.raises(ValueError, match="outcome proof"):
        validate_proof_candidate(response("counterexample", "", graph), ())


def test_response_protocol_and_schema_are_bound_in_provider_fingerprint(tmp_path, monkeypatch):
    import autonomous_math.prover.codex_synthesis as module
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path))
    config = synth.configuration()
    assert config["response_protocol"] == "proof-counterexample-unknown-helpers-v2"
    assert set(config["schema"]["required"]) == {"outcome", "proof_body", "imports", "explanation", "counterexample", "missing_lemmas"}
    initial = synth.configuration_fingerprint()
    changed = json.loads(json.dumps(module.PROOF_SCHEMA))
    changed["properties"]["explanation"]["maxLength"] = 3999
    monkeypatch.setattr(module, "PROOF_SCHEMA", changed)
    assert synth.configuration_fingerprint() != initial


@pytest.mark.parametrize("outcome, graph", [("unknown", None), ("counterexample", {"order": 2, "edges": [[0, 1]]})])
def test_generator_requests_explicit_outcomes_without_treating_graph_as_lean_body(tmp_path, monkeypatch, outcome, graph):
    synth = CodexProofSynthesizer(cli_path=tmp_path / "unused")
    captured = []
    def request(prompt, schema, directory, deadline):
        captured.append((prompt, schema))
        return response(outcome, "", graph), {"artifact_path": str(directory)}
    monkeypatch.setattr(synth, "request_json", request)
    data, _ = synth.generate_candidate("trusted target", [], tmp_path / "request", time.monotonic() + 5)
    assert data["outcome"] == outcome and not data["proof_body"]
    assert set(captured[0][1]["required"]) == set(PROOF_SCHEMA["required"]) | {"missing_lemmas"}
    assert "host recomputes" in captured[0][0] and "return unknown instead of an empty proof" in captured[0][0]


class NoCompilerToolchain:
    is_available = False

    def __init__(self, directory):
        self.workspace_dir = directory

    def ensure_workspace_built(self):
        return True

    def run_lean_code(self, *args, **kwargs):
        raise AssertionError("Nonproof outcomes must not invoke the compiler")


class OutcomeSynthesizer:
    max_rounds, timeout_per_request, allowed_imports = 3, 10, ()

    def __init__(self, answers, after_request=None):
        self.answers, self.requests, self.after_request = iter(answers), [], after_request

    def generate_candidate(self, challenge, feedback, directory, deadline):
        directory.mkdir(parents=True)
        data = next(self.answers)
        self.requests.append(list(feedback))
        if self.after_request:
            self.after_request()
        return data, {"artifact_path": str(directory), "status": "RESPONSE_VALIDATED"}


def nonproof_search(tmp_path, monkeypatch, answers, budget=60, after_request=None):
    synth = OutcomeSynthesizer(answers, after_request)
    prover = LeanProofSearch(toolchain=NoCompilerToolchain(tmp_path / "unused-workspace"),
        max_attempts=0, synthesizer=synth, total_timeout_sec=budget)
    monkeypatch.setattr(prover, "search_key", lambda _: "strict-protocol-fixture")
    return prover, synth


def false_order_goal(guard=None):
    return Conjecture.create(id="counterexample_flow", lhs=InvariantNode("order"), rel="<=",
                            rhs=ConstantNode(0), guard=guard)


def test_verified_structured_counterexample_returns_refuted_without_lean_receipt(tmp_path, monkeypatch):
    from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier
    prover, synth = nonproof_search(tmp_path, monkeypatch, [response("counterexample", "", {"order": 1, "edges": []})])
    result = prover.prove_conjecture(false_order_goal(), tmp_path / "proof")
    assert result.status == "REFUTED" and not result.is_machine_checked and not result.is_proven
    assert len(synth.requests) == 1 and result.attempts_count == 0
    assert not result.receipt_path and not result.verified_file_path and not result.proof_origin
    assert result.to_dict()["counterexample_certificate"] == result.counterexample_certificate
    certificate = CounterexampleCertificate.from_dict(result.counterexample_certificate)
    assert CounterexampleCertificateVerifier().verify(certificate, false_order_goal())
    trace = result.synthesis_attempts[0]
    assert trace["status"] == "COUNTEREXAMPLE_VERIFIED"
    assert json.loads(Path(trace["counterexample_path"]).read_text()) == result.counterexample_certificate
    assert not list((tmp_path / "proof").rglob("*.receipt.json"))


def test_unknown_stops_without_repeated_request_or_prose_refutation(tmp_path, monkeypatch):
    answer = response("unknown", "")
    answer["explanation"] = "A triangle allegedly contradicts the target; this prose is not a certificate."
    prover, synth = nonproof_search(tmp_path, monkeypatch, [answer])
    result = prover.prove_conjecture(false_order_goal(), tmp_path / "proof")
    assert result.status == "UNRESOLVED" and not result.counterexample_certificate
    assert len(synth.requests) == 1 and result.synthesis_attempts[0]["status"] == "MODEL_UNKNOWN"
    assert result.attempts_count == 0 and not list((tmp_path / "proof").rglob("counterexample.json"))


def test_prover_dispatch_never_accepts_a_legacy_three_field_response(tmp_path, monkeypatch):
    legacy = {"proof_body": "exact Nat.cast_nonneg _", "imports": [], "explanation": ""}
    prover, synth = nonproof_search(tmp_path, monkeypatch, [legacy, response("unknown", "")])
    result = prover.prove_conjecture(goal(), tmp_path / "proof")
    assert result.status == "UNRESOLVED" and not result.counterexample_certificate and len(synth.requests) == 2
    assert result.synthesis_attempts[0]["status"] == "PROOF_BODY_REJECTED" and result.attempts_count == 0


@pytest.mark.parametrize("graph, guarded", [
    ({"order": 0, "edges": []}, False),  # Does not violate order <= 0.
    ({"order": 2, "edges": [[0, 1], [1, 0]]}, False),  # Duplicate undirected edge.
    ({"order": 3, "edges": [[0, 1], [1, 2], [0, 2]]}, True),  # Not a tree.
])
def test_invalid_graph_guard_or_nonviolation_repairs_without_refutation(tmp_path, monkeypatch, graph, guarded):
    prover, synth = nonproof_search(tmp_path, monkeypatch, [response("counterexample", "", graph), response("unknown", "")])
    candidate = false_order_goal(GuardPredicate("is_tree") if guarded else None)
    result = prover.prove_conjecture(candidate, tmp_path / "proof")
    assert result.status == "UNRESOLVED" and not result.counterexample_certificate and len(synth.requests) == 2
    assert [t["status"] for t in result.synthesis_attempts] == ["COUNTEREXAMPLE_REJECTED", "MODEL_UNKNOWN"]
    assert result.diagnostics[0]["phase"] == "model_counterexample" and not result.diagnostics[0]["compiler_launched"]
    assert synth.requests[1][-1]["error"] and not list((tmp_path / "proof").rglob("counterexample.json"))


@pytest.mark.parametrize("when", ["before", "during"])
def test_counterexample_verification_respects_shared_deadline_before_certification(tmp_path, monkeypatch, when):
    import autonomous_math.prover.lean_prover as module
    import autonomous_math.sieve.model_counterexamples as helper
    clock = [100.0]
    monkeypatch.setattr(module.time, "monotonic", lambda: clock[0])
    actual = helper.verify_model_counterexample
    def verify(data, conjecture):
        assert when == "during", "Expired requests must not start graph verification"
        certificate = actual(data, conjecture)
        clock[0] += 20
        return certificate
    monkeypatch.setattr(helper, "verify_model_counterexample", verify)
    def returned():
        if when == "before":
            clock[0] += 20
    prover, synth = nonproof_search(tmp_path, monkeypatch,
        [response("counterexample", "", {"order": 1, "edges": []})], budget=10, after_request=returned)
    result = prover.prove_conjecture(false_order_goal(), tmp_path / "proof")
    assert result.status == "UNRESOLVED" and not result.counterexample_certificate and len(synth.requests) == 1
    assert result.synthesis_attempts[0]["status"] == "COUNTEREXAMPLE_INCONCLUSIVE"
    assert result.diagnostics[-1]["phase"] == "shared_budget"
    assert not list((tmp_path / "proof").rglob("counterexample.json"))


def test_counterexample_verifier_cancellation_propagates(tmp_path, monkeypatch):
    import autonomous_math.sieve.model_counterexamples as helper
    def cancelled(*args):
        raise InterruptedError("caller cancelled graph verification")
    monkeypatch.setattr(helper, "verify_model_counterexample", cancelled)
    prover, _ = nonproof_search(tmp_path, monkeypatch, [response("counterexample", "", {"order": 1, "edges": []})])
    with pytest.raises(InterruptedError):
        prover.prove_conjecture(false_order_goal(), tmp_path / "proof")
    assert not list((tmp_path / "proof").rglob("counterexample.json"))


@pytest.mark.parametrize("body", [
    "have h : (0 : ℕ) ≤ 0 := by\n  omega\nexact_mod_cast h",
    "  have h : (0 : ℕ) ≤ 0 := by\n    omega\n  exact_mod_cast h",
    "\n  by\n    have h : (0 : ℕ) ≤ 0 := by\n      omega\n    exact_mod_cast h\n",
])
def test_body_dedents_uniform_indentation_and_optional_by_preserving_nested_blocks(body):
    expected = "have h : (0 : ℕ) ≤ 0 := by\n  omega\nexact_mod_cast h"
    data = validate_proof_candidate({"proof_body": body, "imports": [], "explanation": ""}, ())
    assert data["proof_body"] == expected


@pytest.mark.parametrize("body", [
    "  exact True.intro\n  end Escape\n  axiom forged : False",
    "  by\n    exact True.intro\n    theorem forged : False := by trivial",
])
def test_dedentation_does_not_admit_top_level_escapes(body):
    with pytest.raises(ValueError, match="declaration"):
        validate_proof_candidate({"proof_body": body, "imports": [], "explanation": ""}, ())


def test_real_compiler_accepts_uniformly_indented_multiline_model_body(tmp_path):
    body = "  have h : (0 : ℕ) ≤ Fintype.card V := by\n    exact Nat.zero_le _\n  exact_mod_cast h"
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path, body=body), max_rounds=1)
    result = LeanProofSearch(max_attempts=0, timeout_per_attempt=30,
        synthesizer=synth, total_timeout_sec=60).prove_conjecture(goal(), output_dir=tmp_path / "proof")
    assert result.is_proven, result.diagnostics
    assert result.attempts_count == 1
    assert result.verified_lean_code.endswith("  have h : (0 : ℕ) ≤ Fintype.card V := by\n    exact Nat.zero_le _\n  exact_mod_cast h\n")
    receipt, error = validate_receipt(result.receipt_path, goal().id)
    assert receipt and not error
    assert set(receipt["axioms"]) <= ALLOWED_AXIOMS


def test_schema_validator_rejects_invalid_nested_candidate_proposals():
    schema = {"type": "object", "additionalProperties": False,
        "properties": {"goals": {"type": "array", "items": {"$ref": "#/$defs/goal"}, "maxItems": 2}},
        "required": ["goals"], "$defs": {"goal": {"type": "object", "additionalProperties": False,
            "properties": {"relation": {"type": "string", "enum": ["<=", ">="]}}, "required": ["relation"]}}}
    validate_json_schema({"goals": [{"relation": "<="}]}, schema)
    for invalid in [{"goals": [{"relation": "admit"}]}, {"goals": [{"relation": "<=", "axiom": True}]},
                    {"goals": [None]}, {"goals": [{"relation": "<="}] * 3}, {}]:
        with pytest.raises(ValueError):
            validate_json_schema(invalid, schema)


def test_dead_group_macos_permission_race_does_not_hide_timeout(monkeypatch):
    process = subprocess.Popen(["/usr/bin/true"], start_new_session=True)
    process.wait()
    def denied(*args):
        raise PermissionError("fixture dead-group EPERM")
    monkeypatch.setattr(os, "killpg", denied)
    terminate_process_group(process)


def test_macos_exiting_group_cannot_execute_and_need_not_be_signalled(monkeypatch):
    process = subprocess.Popen(["/usr/bin/true"], start_new_session=True)
    process.wait()
    def denied(*args):
        raise PermissionError("fixture exiting-group EPERM")
    monkeypatch.setattr(os, "killpg", denied)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: subprocess.CompletedProcess(
        a, 0, stdout=f"123 {process.pid} ?E\n"))
    terminate_process_group(process)


def test_live_group_permission_failure_is_not_suppressed(monkeypatch):
    process = subprocess.Popen(["/bin/sleep", "60"], start_new_session=True)
    try:
        with monkeypatch.context() as patch:
            def denied(*args):
                raise PermissionError("fixture live-group EPERM")
            patch.setattr(os, "killpg", denied)
            with pytest.raises(PermissionError):
                terminate_process_group(process)
        assert process.poll() is None
    finally:
        terminate_process_group(process)


def test_authenticated_request_records_usage_and_enforces_actual_cli_flags(tmp_path):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path))
    data, trace = synth.request_json("A bounded test", PROOF_SCHEMA, tmp_path / "request", time.monotonic() + 5)
    assert data["proof_body"] == "exact Nat.cast_nonneg _"
    assert trace["actual_model"] == "fixture-model"
    assert trace["usage"] == {"input_tokens": 17, "output_tokens": 9}
    assert trace["status"] == "RESPONSE_VALIDATED" and trace["exit_code"] == 0
    args = trace["command"]
    assert args[args.index("--sandbox") + 1] == "read-only"
    assert "--ignore-user-config" in args and "--ephemeral" in args
    assert "agents.enabled=false" in args and "mcp_servers={}" in args
    for feature in DISABLED_FEATURES:
        assert any(args[i:i+2] == ["--disable", feature] for i in range(len(args)-1))
    configured = trace["configuration"]["configured_model"]
    if configured:
        assert args[args.index("--model") + 1] == configured
    assert not synth.active_process_groups()
    assert (tmp_path / "request/trace.json").is_file()
    with pytest.raises(SynthesisError, match="overwrite"):
        synth.request_json("again", PROOF_SCHEMA, tmp_path / "request", time.monotonic() + 5)


@pytest.mark.parametrize("override", [None, "low"])
def test_model_and_effort_selection_reaches_cli_and_evidence(tmp_path, monkeypatch, override):
    config_dir = tmp_path / "codex_config"
    config_dir.mkdir()
    config_file = config_dir / "config.toml"
    original = 'model = "configured-model"\nmodel_reasoning_effort = "xhigh"\n'
    config_file.write_text(original)
    monkeypatch.setenv("CODEX_HOME", str(config_dir))
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    synth = CodexProofSynthesizer(workspace_dir=workspace, cli_path=fake_cli(tmp_path),
                                 model="selected-model", reasoning_effort=override)
    baseline = CodexProofSynthesizer(workspace_dir=workspace, cli_path=synth.cli_path,
                                    model="selected-model")
    _, trace = synth.request_json("test", PROOF_SCHEMA, tmp_path / "request", time.monotonic() + 5)
    config = trace["configuration"]
    assert config["configured_reasoning_effort"] == "xhigh"
    assert config["reasoning_effort_override"] == override
    assert config["reasoning_effort"] == (override or "xhigh")
    command = trace["command"]
    assert command[command.index("--model") + 1] == "selected-model"
    effort_flags = [arg for arg in command if arg.startswith("model_reasoning_effort=")]
    assert effort_flags == ["model_reasoning_effort=" + json.dumps(override or "xhigh")]
    assert (synth.configuration_fingerprint() != baseline.configuration_fingerprint()) == bool(override)
    assert config_file.read_text() == original


@pytest.mark.parametrize("effort", ["", "fastest", True, 7])
def test_invalid_effort_is_rejected_before_request(effort):
    with pytest.raises(ValueError, match="reasoning effort"):
        CodexProofSynthesizer(reasoning_effort=effort)


@pytest.mark.parametrize("mode", ["error", "malformed", "legacy"])
def test_service_failure_retains_evidence_and_never_returns_a_proof(tmp_path, mode):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path, mode=mode))
    with pytest.raises(SynthesisError) as failure:
        synth.request_json("test", PROOF_SCHEMA, tmp_path / mode, time.monotonic() + 5)
    assert failure.value.trace["status"] == "FAILED"
    assert (tmp_path / mode / "trace.json").is_file()
    assert not synth.active_process_groups()


def test_malformed_structured_counterexample_retains_rejection_feedback(tmp_path):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path, mode="bad_counterexample"))
    with pytest.raises(SynthesisError) as failure:
        synth.generate_candidate("trusted target", [], tmp_path / "bad", time.monotonic() + 5)
    assert failure.value.trace["status"] == "COUNTEREXAMPLE_REJECTED"
    assert (tmp_path / "bad/answer.json").is_file() and (tmp_path / "bad/trace.json").is_file()
    assert not synth.active_process_groups()


def process_running(pid):
    result = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True, timeout=2)
    return bool(result.stdout.strip()) and not result.stdout.strip().startswith("Z")


@pytest.mark.skipif(os.name != "posix", reason="The local research runtime uses POSIX process groups")
def test_timeout_kills_codex_and_its_descendants(tmp_path):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path, mode="timeout"), timeout_per_request=0.3)
    started = time.monotonic()
    with pytest.raises(SynthesisError) as failure:
        synth.request_json("test", PROOF_SCHEMA, tmp_path / "timeout", started + 5)
    assert time.monotonic() - started < 3
    assert failure.value.trace["status"] == "TIMEOUT"
    child = int((tmp_path / "timeout/child.pid").read_text())
    assert not process_running(child)
    assert not synth.active_process_groups()


def test_budget_exhaustion_and_pinned_workspace_outputs_fail_closed(tmp_path):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path), workspace_dir=tmp_path / "workspace")
    synth.workspace_dir.mkdir()
    with pytest.raises(SynthesisError, match="budget"):
        synth.request_json("test", PROOF_SCHEMA, tmp_path / "expired", time.monotonic() - 1)
    with pytest.raises(SynthesisError, match="build workspace"):
        synth.request_json("test", PROOF_SCHEMA, synth.workspace_dir / "forbidden", time.monotonic() + 5)
    assert not (synth.workspace_dir / "forbidden").exists()


@pytest.mark.parametrize("fake_trace", ["probe depends on axioms: [propext]", "'native_forge' depends on axioms: [propext]"])
def test_real_kernel_native_axiom_and_forged_trace_never_certify(tmp_path, fake_trace):
    challenge, name = render_challenge(goal("native_forge"))
    body = (f'trace "{fake_trace}"\n'
            '  have h : (0 : ℕ) ≤ 0 := by decide +native\n'
            '  exact_mod_cast (le_trans h (Nat.zero_le (Fintype.card V)))')
    result = LeanProofSearch(max_attempts=1, timeout_per_attempt=30).prove_challenge(
        challenge.replace("sorry", body), output_dir=tmp_path)
    assert not result.is_proven
    assert result.diagnostics[0]["exit_code"] == 0, result.diagnostics
    assert "_native.decide.ax" in result.diagnostics[0]["stdout"]
    assert not list(tmp_path.glob("*.receipt.json"))
    if fake_trace.startswith("probe"):
        assert not set(result.diagnostics[0]["axioms"]).issubset(ALLOWED_AXIOMS)
    else:
        assert result.diagnostics[0]["axiom_audit_error"]


def test_exact_final_target_report_is_required():
    assert _target_axiom_report("probe depends on axioms: [bad]\n'x' does not depend on any axioms\n", "x") == ([], None)
    for stdout in ["'other' depends on axioms: [propext]\n", "'x' depends on axioms: [propext]\nextra",
                   "'x' malformed\n'x' does not depend on any axioms\n",
                   "'x' depends on axioms: [propext]\n'x' depends on axioms: [Classical.choice]\n"]:
        assert _target_axiom_report(stdout, "x")[1]


def test_real_compiler_repairs_generated_body_and_only_then_issues_receipt(tmp_path):
    synth = CodexProofSynthesizer(cli_path=fake_cli(tmp_path, mode="repair"), max_rounds=2)
    result = LeanProofSearch(max_attempts=0, timeout_per_attempt=30,
        synthesizer=synth, total_timeout_sec=90).prove_conjecture(goal(), output_dir=tmp_path / "proof")
    assert result.is_proven, result.diagnostics
    assert result.proof_origin == "codex_synthesis" and result.attempts_count == 2
    assert len(result.synthesis_attempts) == 2
    assert [record["status"] for record in result.synthesis_attempts] == ["KERNEL_REJECTED", "KERNEL_ACCEPTED"]
    receipt, error = validate_receipt(result.receipt_path, goal().id)
    assert receipt and not error
    assert receipt["conjecture"] == goal().to_dict()
    assert receipt["explanation_status"] == "MODEL_GENERATED_UNREVIEWED"
    second = Path(result.synthesis_attempts[1]["artifact_path"])
    assert "not_a_real_lemma" in (second / "prompt.txt").read_text()
    assert (second / "compiler.json").is_file()


def test_fixed_tactic_success_does_not_request_a_model(tmp_path):
    class ForbiddenSynth:
        max_rounds, timeout_per_request = 2, 10
        def configuration_fingerprint(self): return "no-service-test"
        def generate_candidate(self, *args): raise AssertionError("Fixed success must skip synthesis")
    result = LeanProofSearch(max_attempts=1, timeout_per_attempt=30,
        synthesizer=ForbiddenSynth()).prove_conjecture(goal(), output_dir=tmp_path)
    assert result.is_proven and result.proof_origin == "fixed_tactic"
    assert not result.synthesis_attempts


def test_guarded_reuse_applies_only_identical_guard():
    tree = GuardPredicate("is_tree")
    connected = GuardPredicate("is_connected")
    receipt = {"theorem_name": "tree_fact", "conjecture": goal(guard=tree).to_dict()}
    assert all(" h_guard" in t for t in LeanProofSearch._reuse_tactics([receipt], goal(guard=tree)))
    assert all("(by first | aesop | linarith)" in t for t in LeanProofSearch._reuse_tactics([receipt], goal(guard=connected)))
    assert all("(by first | aesop | linarith)" in t for t in LeanProofSearch._reuse_tactics([receipt], goal()))
    universal = {"theorem_name": "universal_fact", "conjecture": goal().to_dict()}
    assert any("universal_fact G" in t and "h_guard" not in t for t in LeanProofSearch._reuse_tactics([universal], goal(guard=tree)))
    trivial = GuardPredicate("conjunction", guards=[GuardPredicate("universal")])
    receipt = {"theorem_name": "trivial_guard_fact", "conjecture": goal(guard=trivial).to_dict()}
    assert all("h_guard" not in t for t in LeanProofSearch._reuse_tactics([receipt], goal(guard=trivial)))


def test_native_spectral_receipt_reuse_preserves_trusted_scope(tmp_path):
    from autonomous_math.prover.flywheel import LemmaFlywheel
    spectral = Conjecture.create(id="native_spectral_nonnegative", lhs=InvariantNode("graph_energy"),
                                 rel=">=", rhs=ConstantNode(0))
    flywheel = LemmaFlywheel(storage_path=tmp_path / "lemmas.json")
    prover = LeanProofSearch(max_attempts=4, timeout_per_attempt=30, flywheel=flywheel)
    first = prover.prove_conjecture(spectral, output_dir=tmp_path / "first")
    assert first.is_proven, first.diagnostics
    previous = first.verified_file_path.read_text()
    assert "open scoped BigOperators" in previous
    second = prover.prove_conjecture(spectral.model_copy(update={"id": "reused_spectral_nonnegative"}), output_dir=tmp_path / "second")
    assert second.is_proven, second.diagnostics
    assert "have " in second.successful_tactic or "exact native_spectral_nonnegative G" == second.successful_tactic
    assert second.verified_file_path.read_text().count("open scoped BigOperators") == 1
    assert validate_receipt(second.receipt_path)[0]
