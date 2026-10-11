"""Spectral comparison controls use fixtures, never Lean or model requests."""
import copy
import hashlib
import json
from pathlib import Path
import time

import pytest

from autonomous_math.core.ast import (
    BinaryOpNode as B, ConstantNode as C, Conjecture, GuardPredicate as G,
    InvariantNode as I, UnaryOpNode as U,
)
from autonomous_math.novelty import frontier, model_review, primary_sources
from autonomous_math.novelty.review_classification import classify_record
from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
from autonomous_math.research_state import sha256
from tests.unit.test_model_review import (
    corpus, atlas, answer, Synthesizer, PairedSynthesizer, extension_pack,
)


@pytest.fixture(autouse=True)
def fixture_sources_only(monkeypatch):
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": [], "coverage": {"primary_literature": 0, "unavailable": []}, "evidence_key": None})
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *args: None)


def spectral_theorem(corpus, identifier, left, relation, right, guard=None):
    """Bind the structured fixture target to its fixture receipt, without Lean."""
    row = corpus.theorem(identifier, "graph_energy", guard)
    row["conjecture"] = Conjecture.create(
        id=identifier, lhs=left, rel=relation, rhs=right, guard=guard,
    ).to_dict()
    path = Path(row["lean_proof"]["receipt_path"])
    receipt = json.loads(path.read_text())
    receipt["conjecture"] = copy.deepcopy(row["conjecture"])
    receipt["lean_binary_sha256"] = "b" * 64
    path.write_text(json.dumps(receipt))
    return row


def energy_bound():
    return B("*", B("*", C(2), I("average_degree")),
             B("+", C(1), B("max", C(0), B("-", C(1), I("normalized_laplacian_spectral_gap")))))


def irregularity_bound():
    n_minus_one = B("-", I("order"), C(1))
    left = B("*", n_minus_one, U("sqr", I("signless_laplacian_spectral_radius")))
    right = B("*", C(4), B("+",
        B("*", n_minus_one, U("sqr", I("average_degree"))),
        U("sqr", B("-", I("max_degree"), I("average_degree")))))
    return left, right


def primary_fixture(tmp_path, identifier, text, *, readable=False, topic="signless_irregularity", baselines=()):
    path, pages = tmp_path / f"{identifier}.txt", tmp_path / f"{identifier}.pages.json"
    path.write_text(text)
    pages.write_text(json.dumps([{"page": 0, "text": text}]))
    return {
        "source_id": identifier, "source_type": "primary_literature", "is_target": False,
        "theorem_id": None, "title": "Synthetic complete primary comparison control", "url": None,
        "source_path": str(path), "source_sha256": sha256(path), "text": text,
        "text_sha256": hashlib.sha256(text.encode()).hexdigest(), "page": 0, "excerpt_start": 0,
        "cache_files": [{"kind": "extracted_pages", "path": pages.name, "sha256": sha256(pages)}],
        "evidence_kind": "body_statement", "statement_kind": "lemma", "math_readable": readable,
        "topics": [topic], "selection": "Complete bound with definitions and all hypotheses",
        "comparison_baselines": list(baselines),
        "construction": "real simple-graph adjacency or signless-Laplacian spectrum",
        "comparison_role": "stronger_applicable_baseline",
        "locator": "Synthetic page 0", "version": sha256(path),
    }


@pytest.mark.parametrize("kind", ["energy", "irregularity"])
@pytest.mark.parametrize("strengthened_guard", [False, True])
def test_spectral_restatement_or_stronger_guard_is_not_an_original_candidate(corpus, kind, strengthened_guard):
    guard = G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
        G(invariant="order", op=">=", threshold=2)]) if kind == "energy" else None
    left, right = (I("graph_energy"), energy_bound()) if kind == "energy" else irregularity_bound()
    parent = spectral_theorem(corpus, "exact_parent", left, ">=", right, guard)
    target_guard = guard
    if strengthened_guard:
        target_guard = G(predicate_type="conjunction", guards=[
            *([guard] if guard else []), G(invariant="order", op=">=", threshold=3)])
    target = spectral_theorem(corpus, "alleged_advance", right, "<=", left, target_guard)
    parent["discovered_iteration"], target["discovered_iteration"] = 1, 2
    target["conjecture"]["metadata"] = {"explanation": "A model claims this is a new improvement."}
    result = classify_record(target, atlas(parent, target))
    assert result["status"] == "routine_consequence"
    detected = "specialization" if strengthened_guard else "restatement"
    assert next(check for check in result["checks"] if check["label"] == detected)["status"] == "fail"
    assert result["closest_results"][0]["theorem_id"] == "exact_parent"


def test_rms_primary_corollary_completes_routine_with_exact_quotes_and_bindings(corpus, tmp_path, monkeypatch):
    left, right = irregularity_bound()
    target = spectral_theorem(corpus, "irregularity_target", left, ">=", right)
    data, record = atlas(target), corpus.review(target)
    source = primary_fixture(tmp_path, "primary_rms", (
        "Lemma 3.20. For a nonempty k-uniform hypergraph, the signless incidence "
        "spectral radius is at least k times the root mean square degree. "
        "For a simple graph k=2 and Q=D+A. This synthetic text controls exact quote binding."
    ))
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": [source], "coverage": {"primary_literature": 1}, "evidence_key": None})
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *args: None)
    pack = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    response = answer(pack, "routine_consequence", 1, "routine_consequence")
    response["comparisons"][0]["comparison"] = (
        "For n>=2, Cauchy-Schwarz on the n-1 remaining degree deviations gives "
        "mean(d^2)>=a^2+(Delta-a)^2/(n-1); apply the quoted k=2 RMS bound. "
        "Order zero and one make the target trivial. No novelty follows."
    )
    synthesizer = Synthesizer(response)
    directory = tmp_path / "novelty_attempts" / "rms_control"
    result = model_review.assess_review(record, target, data, synthesizer, directory, time.monotonic()+5)
    assert result["outcome"] == "routine_consequence" and "challenge" not in result
    assert len(synthesizer.calls) == 1
    assert result["comparisons"][0]["source_sha256"] == source["source_sha256"]
    assert result["comparisons"][0]["quote"] in source["text"]
    record["ai_review"] = result
    replayed = model_review.validate_completed_review(record, data, tmp_path)
    assert replayed["assessment"]["outcome"] == "routine_consequence"
    Path(source["source_path"]).write_text(source["text"] + "changed")
    with pytest.raises(ValueError, match="source bytes changed"):
        model_review.validate_completed_review(record, data, tmp_path)


def test_unverified_pdf_math_cannot_clear_a_spectral_improvement(corpus, tmp_path, monkeypatch):
    target = spectral_theorem(corpus, "energy_target", I("graph_energy"), ">=", energy_bound(), G("is_regular"))
    data, record = atlas(target), corpus.review(target)
    source = primary_fixture(tmp_path, "primary_energy", (
        "Theorem 4. Let A be the real adjacency matrix of a finite simple graph. "
        "The graph energy satisfies the stated spectral lower bound under the complete hypotheses."
    ), topic="energy_lower_bounds")
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": [source], "coverage": {"primary_literature": 1}, "evidence_key": None})
    pack = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    response = answer(pack, "possible_extension", 1, "related_context")
    response["contribution"] = "This synthetic favorable response alleges a tighter energy lower bound, without verified extracted mathematics or strictness evidence."
    for check in response["checks"]:
        check["status"] = "pass"
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved" and result["model_outcome"] == "possible_extension"
    assert result["comparisons"][0]["quote"] in source["text"]


def test_complete_strong_baseline_metadata_reaches_assessment_and_identical_challenge(corpus, tmp_path, monkeypatch):
    # The existing valid coding fixture exercises the two-request adapter. The
    # extra spectral record tests transport, not a spectral originality claim.
    target, data, record, pack, response = extension_pack(corpus, tmp_path)
    source = primary_fixture(tmp_path, "primary_strong_spectral", (
        "Lemma 3.20. Q is the signless incidence matrix over the real field. "
        "For ordinary simple graphs Q=D+A and k=2; the RMS-degree lower bound applies."
    ))
    pack["sources"].append(source)
    pack["source_coverage"]["primary_literature"] += 1
    monkeypatch.setattr(model_review, "build_review_source_pack", lambda *args, **kwargs: copy.deepcopy(pack))
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *args: None)
    critic = answer(pack, "routine_consequence", 1, "routine_consequence")
    synthesizer = PairedSynthesizer([response, critic])
    directory = tmp_path / "novelty_attempts" / "transport_control"
    result = model_review.assess_review(record, target, data, synthesizer, directory, time.monotonic()+5)
    assert result["outcome"] == "routine_consequence"
    assert len(synthesizer.calls) == 2 and all(call[2] for call in synthesizer.calls)
    assert json.loads(synthesizer.calls[0][0].split("\n", 1)[1]) == pack
    assert json.loads(synthesizer.calls[1][0].split("\n", 1)[1])["source_pack"] == pack
    assert source == json.loads((directory / "source_pack.json").read_text())["sources"][-1]
    assert "complete guard" in synthesizer.calls[0][0]
    assert "strongest supplied" in synthesizer.calls[1][0]
    record["ai_review"] = result
    assert model_review.validate_completed_review(record, data, tmp_path)["assessment"]["outcome"] == "routine_consequence"


def test_native_request_adapter_preserves_complete_bound_guard_and_field(corpus, tmp_path, monkeypatch):
    target = spectral_theorem(corpus, "native_transport_target", I("graph_energy"), ">=", energy_bound(),
        G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
            G(invariant="order", op=">=", threshold=2)]))
    data, record = atlas(target), corpus.review(target)
    source = primary_fixture(tmp_path, "primary_native_energy", (
        "Theorem 2. For a connected regular simple graph on at least two vertices, "
        "A is its real adjacency matrix and L_norm=I-A/k. Graph energy is the sum "
        "of absolute real adjacency eigenvalues; the complete competing bound is stated here."
    ), topic="normalized_energy_bridge")
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": [source], "coverage": {"primary_literature": 1}, "evidence_key": None})
    pack = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    response = answer(pack, "routine_consequence", 1, "routine_consequence")
    response["comparisons"][0]["generalization"] = None
    cli = tmp_path / "fake_review_cli"
    cli.write_text("#!/usr/bin/env python3\nimport json,sys\nfrom pathlib import Path\n"
        "args=sys.argv[1:]\noutput=Path(args[args.index('--output-last-message')+1])\n"
        "(output.parent/'received_prompt.txt').write_text(sys.stdin.read())\n"
        f"output.write_text({json.dumps(response)!r})\n"
        "print(json.dumps({'type':'turn.completed','usage':{'input_tokens':2,'output_tokens':1}}))\n")
    cli.chmod(0o755)
    config_directory, workspace = tmp_path / "fake_config", tmp_path / "fake_workspace"
    config_directory.mkdir()
    workspace.mkdir()
    (config_directory / "config.toml").write_text('model="fixture-model"\nmodel_reasoning_effort="xhigh"\n')
    monkeypatch.setenv("CODEX_HOME", str(config_directory))
    synthesizer = CodexProofSynthesizer(workspace_dir=workspace, cli_path=cli)
    directory = tmp_path / "novelty_attempts" / "native_transport"
    result = model_review.assess_review(record, target, data, synthesizer, directory, time.monotonic()+5)
    received = (directory / "received_prompt.txt").read_text()
    assert received == (directory / "prompt.txt").read_text()
    assert json.loads(received.split("\n", 1)[1]) == pack
    trace = json.loads((directory / "trace.json").read_text())
    disabled = {trace["command"][i+1] for i, value in enumerate(trace["command"][:-1]) if value == "--disable"}
    assert {"shell_tool", "unified_exec"} <= disabled
    assert 'web_search="disabled"' in trace["command"]
    assert result["outcome"] == "routine_consequence" and len(result["requests"]) == 1
    assert result["usage_accounting"]["missing_usage_count"] == 0
    assert not synthesizer.active_process_groups()


@pytest.mark.parametrize("change", ["ast", "proof_bytes", "receipt_hash"])
def test_selected_checked_spectral_parent_cannot_be_rebound(corpus, tmp_path, change):
    parent = spectral_theorem(corpus, "checked_energy_parent", I("graph_energy"), ">=", energy_bound(), G("is_regular"))
    target = spectral_theorem(corpus, "energy_child", I("graph_energy"), ">=", C(0))
    target["lean_proof"]["used_lemma_ids"] = [parent["id"]]
    data, record = atlas(target, parent), corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data)
    assert pack["sources"][1]["theorem_id"] == parent["id"]
    directory = tmp_path / "novelty_attempts" / "parent_control"
    result = model_review.assess_review(record, target, data,
        Synthesizer(answer(pack, "routine_consequence", 1, "routine_consequence")), directory, time.monotonic()+5)
    record["ai_review"] = result
    receipt_path = Path(parent["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    if change == "ast":
        parent["conjecture"]["guard_predicate"] = None
    elif change == "proof_bytes":
        Path(receipt["source_path"]).write_text("A different checked-parent claim.")
    else:
        receipt["source_sha256"] = "0" * 64
        receipt_path.write_text(json.dumps(receipt))
    with pytest.raises(ValueError):
        model_review.validate_completed_review(record, data, tmp_path)


@pytest.mark.parametrize("kind", ["energy", "irregularity"])
def test_foundation_identity_requires_exact_current_receipt_and_ast(corpus, kind):
    if kind == "energy":
        identifier = "model_f1abeb346d4f50c57240"
        guard = G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
            G(invariant="order", op=">=", threshold=2)])
        parent = spectral_theorem(corpus, identifier, I("graph_energy"), ">=", energy_bound(), guard)
    else:
        identifier = "model_e1bd2d98ab50c3dcff7c"
        left, right = irregularity_bound()
        parent = spectral_theorem(corpus, identifier, left, ">=", right)
    data = atlas(parent)
    valid = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)
    assert len(valid["parents"]) == 1
    binding = valid["parents"][0]["binding"]
    receipt = json.loads(Path(parent["lean_proof"]["receipt_path"]).read_text())
    assert binding["parent_id"] == identifier
    for field in ("source_sha256", "challenge_sha256", "workspace_sha256", "lean_binary_sha256", "theorem_name"):
        assert binding[field] == receipt[field]
    parent["conjecture"]["guard_predicate"] = G("is_bipartite").to_dict()
    changed = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)
    assert not changed["parents"]
    assert any(item["id"] == identifier and "statement differs" in item["reason"] for item in changed["omitted"])


def test_irregularity_rms_corollary_fails_strictness_against_stronger_published_bound():
    candidate = Conjecture.create(id="rms_corollary", lhs=I("signless_laplacian_spectral_radius"), rel=">=",
        rhs=B("*", C(2), U("sqrt", B("+", U("sqr", I("average_degree")),
            B("/", U("sqr", B("-", I("max_degree"), I("average_degree"))), B("-", I("order"), C(1)))))),
        guard=G(invariant="order", op=">=", threshold=2))
    # K1,3: the proposed/RMS bound is sqrt(12), whereas sum d^2/m=4.
    witness = {"order": 4, "edges": [[0, 1], [0, 2], [0, 3]]}
    parents = [{"quantity": "signless_laplacian_spectral_radius"}]
    with pytest.raises(ValueError, match="strongest applicable"):
        frontier.spectral_refinement_witness(candidate, witness, parents)


def test_energy_gap_restatement_fails_strictness_against_full_energy_baselines():
    candidate = Conjecture.create(id="energy_reexpression", lhs=I("graph_energy"), rel=">=", rhs=energy_bound(),
        guard=G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular")]))
    # C6: gap parent gives 6, beating only E>=2*dbar=4. Published 2m/rho
    # already gives 6, so this graph cannot establish a strict advance.
    witness = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    with pytest.raises(ValueError, match="strongest applicable"):
        frontier.spectral_refinement_witness(candidate, witness, [{"quantity": "graph_energy"}])


def test_genuine_finite_separation_is_retained_as_empirical_only():
    candidate = Conjecture.create(id="finite_control", lhs=I("graph_energy"), rel=">=", rhs=C(7))
    witness = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    result = frontier.spectral_refinement_witness(candidate, witness, [{"quantity": "graph_energy"}])
    assert result["status"] == "empirical_separation_only"
    comparison = result["comparisons"][0]
    assert comparison["proposed_lower_bound"] == 7
    assert comparison["strongest_lower_bound"] == pytest.approx(6)
    assert comparison["strictness_margin"] > comparison["numerical_tolerance"]
    assert set(comparison["applicable_baselines"]) == {
        "published_energy_twice_radius", "published_energy_size", "published_energy_size_over_radius",
        "certified_energy_gap_parent",
    }
    assert "floating" in result["method"]
    assert "No universal proof" in result["scope"]


@pytest.mark.parametrize("bound", [4, 4.0000001])
def test_equal_or_roundoff_sized_improvement_is_not_strict_separation(bound):
    candidate = Conjecture.create(id="non_strict_control", lhs=I("graph_energy"), rel=">=", rhs=C(bound))
    witness = {"order": 4, "edges": [[0, 1], [0, 3], [1, 2], [2, 3]]}
    with pytest.raises(ValueError, match="strongest applicable"):
        frontier.spectral_refinement_witness(candidate, witness, [{"quantity": "graph_energy"}])


def ready_refinement_pack(corpus, tmp_path, monkeypatch):
    """Synthetic checked fixture: test the comparison gate, not Lean correctness."""
    parent_guard = G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
        G(invariant="order", op=">=", threshold=2)])
    parent = spectral_theorem(corpus, "model_f1abeb346d4f50c57240", I("graph_energy"), ">=", energy_bound(), parent_guard)
    target_guard = G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
        G(invariant="order", op="==", threshold=6), G(invariant="max_degree", op="==", threshold=2)])
    target = spectral_theorem(corpus, "finite_refinement_control", I("graph_energy"), ">=", C(7), target_guard)
    data = atlas(target, parent)
    parents = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)["parents"]
    witness = {"order": 6, "edges": [[0, 1], [0, 5], [1, 2], [2, 3], [3, 4], [4, 5]]}
    sources = [primary_fixture(tmp_path, "published_radius", (
        "Theorem 1. For every finite simple graph over the real field, graph energy "
        "is at least twice the largest adjacency eigenvalue."
    ), readable=True, topic="energy_lower_bounds", baselines=("energy_spectral_radius",)),
        primary_fixture(tmp_path, "published_size_ratio", (
        "Theorem 2. For every finite simple graph having a positive adjacency spectral radius, "
        "graph energy is at least twice its edge count divided by that radius."
    ), readable=True, topic="energy_lower_bounds", baselines=("energy_edges_over_radius",)),
        primary_fixture(tmp_path, "published_root_size", (
        "Theorem 3. For every finite simple graph over the real field, graph energy "
        "is at least twice the square root of its edge count."
    ), readable=True, topic="energy_lower_bounds", baselines=("energy_sqrt_edges",))]
    candidate = Conjecture.from_dict(target["conjecture"])
    target["conjecture"]["metadata"]["spectral_refinement"] = {
        "role": "candidate_improvement", "parent_ids": [parent["id"]],
        "parent_bindings": [copy.deepcopy(parents[0]["binding"])], "strictness_witness": witness,
        "witness_validation": frontier.spectral_refinement_witness(candidate, witness, parents, sources),
        "originality": "unestablished",
    }
    receipt_path = Path(target["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    receipt["conjecture"] = copy.deepcopy(target["conjecture"])
    receipt_path.write_text(json.dumps(receipt))
    record = corpus.review(target)
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": copy.deepcopy(sources), "coverage": {"primary_literature": 3, "unavailable": []}, "evidence_key": None})
    monkeypatch.setattr(primary_sources, "current_evidence_key", lambda *args: None)
    pack = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    response = answer(pack, "possible_extension", 2, "related_context")
    for source in sources[1:]:
        comparison = copy.deepcopy(response["comparisons"][0])
        comparison.update(source_id=source["source_id"], quote=source["text"])
        response["comparisons"].append(comparison)
    response["contribution"] = "This synthetic control alleges a finite-domain improvement against both supplied bounds; it tests provisional review gates without any originality endorsement."
    for check in response["checks"]:
        check.update(status="pass", source_ids=[source["source_id"] for source in sources])
    return target, parent, data, record, pack, response


def test_review_gate_recomputes_finite_witness_and_retains_bounded_scope(corpus, tmp_path, monkeypatch):
    target, parent, data, record, pack, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    validation = pack["spectral_refinement_validation"]
    assert validation["status"] == "verified_empirical_refinement"
    assert validation["witness_validation"] == target["conjecture"]["metadata"]["spectral_refinement"]["witness_validation"]
    assert "no universal or originality claim" in validation["scope"]
    assert pack["sources"][1]["theorem_id"] == parent["id"]
    assert model_review._validate_assessment(response, pack)["outcome"] == "possible_extension"


@pytest.mark.parametrize("gap", ["uncompared", "unreadable", "unavailable", "no_baselines", "unknown_premises"])
def test_every_stronger_applicable_source_must_be_compared_or_flag_remains_unresolved(corpus, tmp_path, monkeypatch, gap):
    _, _, _, _, pack, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    if gap == "uncompared":
        response["comparisons"].pop()
        for check in response["checks"]:
            check["source_ids"] = ["published_radius"]
    elif gap == "unreadable":
        pack["sources"][-1]["math_readable"] = False
    elif gap == "unavailable":
        pack["source_coverage"]["unavailable"] = [{"url": "https://example.invalid/stronger", "reason": "Unavailable source control"}]
    elif gap == "no_baselines":
        for source in pack["sources"][2:]:
            source["comparison_role"] = "unclassified"
    else:
        response["comparisons"][-1]["premise_relation"] = "unknown"
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved" and result["model_outcome"] == "possible_extension"
    assert any("every supplied published bound" in uncertainty for uncertainty in result["uncertainties"])


@pytest.mark.parametrize("change", ["parent_binding", "stored_margin", "witness_graph", "helper_role"])
def test_favorable_words_do_not_override_parent_or_witness_gate(corpus, tmp_path, monkeypatch, change):
    target, _, data, _, _, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    metadata = target["conjecture"]["metadata"]["spectral_refinement"]
    if change == "parent_binding":
        metadata["parent_bindings"][0]["source_sha256"] = "0" * 64
    elif change == "stored_margin":
        metadata["witness_validation"]["comparisons"][0]["strictness_margin"] += 1
    elif change == "witness_graph":
        metadata["strictness_witness"]["edges"].pop()
    else:
        metadata["role"] = "helper_lemma"
    receipt_path = Path(target["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    receipt["conjecture"] = copy.deepcopy(target["conjecture"])
    receipt_path.write_text(json.dumps(receipt))
    record = corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    assert pack["spectral_refinement_validation"]["status"] == ("helper_only" if change == "helper_role" else "unresolved")
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved"
    assert result["comparisons"][0]["quote"] == response["comparisons"][0]["quote"]


def test_critic_demotion_and_current_parent_replay_use_the_same_strong_baselines(corpus, tmp_path, monkeypatch):
    target, parent, data, record, pack, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    critic = answer(pack, "routine_consequence", 2, "routine_consequence")
    critic["comparisons"][0]["comparison"] = "This synthetic critic finds a source-backed consequence rather than an advance."
    synthesizer = PairedSynthesizer([response, critic])
    directory = tmp_path / "novelty_attempts" / "spectral_challenge"
    result = model_review.assess_review(record, target, data, synthesizer, directory, time.monotonic()+5)
    assert result["preliminary_assessment"]["outcome"] == "possible_extension"
    assert result["outcome"] == "routine_consequence"
    assert result["challenge"]["verdict"] == "source_backed_derivation"
    assert json.loads(synthesizer.calls[1][0].split("\n", 1)[1])["source_pack"] == pack
    record["ai_review"] = result
    assert model_review.validate_completed_review(record, data, tmp_path)["assessment"]["outcome"] == "routine_consequence"
    parent["conjecture"]["guard_predicate"] = G("is_bipartite").to_dict()
    with pytest.raises(ValueError):
        model_review.validate_completed_review(record, data, tmp_path)


def test_current_parent_receipt_binding_is_rechecked_when_source_and_ast_are_identical(corpus, tmp_path):
    guard = G(predicate_type="conjunction", guards=[G("is_connected"), G("is_regular"),
        G(invariant="order", op=">=", threshold=2)])
    parent = spectral_theorem(corpus, "model_f1abeb346d4f50c57240", I("graph_energy"), ">=", energy_bound(), guard)
    target = spectral_theorem(corpus, "helper_binding_control", I("graph_energy"), ">=", C(0))
    data = atlas(target, parent)
    foundation = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)["parents"][0]
    target["conjecture"]["metadata"]["spectral_refinement"] = {
        "role": "helper_lemma", "parent_ids": [parent["id"]], "parent_bindings": [foundation["binding"]],
        "strictness_witness": None, "witness_validation": {"status": "helper_only"},
    }
    target_receipt_path = Path(target["lean_proof"]["receipt_path"])
    target_receipt = json.loads(target_receipt_path.read_text())
    target_receipt["conjecture"] = copy.deepcopy(target["conjecture"])
    target_receipt_path.write_text(json.dumps(target_receipt))
    record = corpus.review(target)
    pack = model_review.build_review_source_pack(record, target, data)
    assert pack["spectral_refinement_validation"]["status"] == "helper_only"
    directory = tmp_path / "novelty_attempts" / "fresh_parent_receipt"
    result = model_review.assess_review(record, target, data,
        Synthesizer(answer(pack, "routine_consequence", 1, "routine_consequence")), directory, time.monotonic()+5)
    record["ai_review"] = result
    assert model_review.validate_completed_review(record, data, tmp_path)["assessment"]["outcome"] == "routine_consequence"
    new_receipt = json.loads(Path(parent["lean_proof"]["receipt_path"]).read_text())
    new_receipt["workspace_sha256"] = "e" * 64
    new_receipt["lean_binary_sha256"] = "c" * 64
    new_path = tmp_path / "replayed_parent.receipt.json"
    new_path.write_text(json.dumps(new_receipt))
    parent["lean_proof"]["receipt_path"] = str(new_path)
    # Exact same theorem/source bytes are insufficient to preserve the old
    # declared receipt, compiler and workspace identity in refinement guidance.
    with pytest.raises(ValueError):
        model_review.validate_completed_review(record, data, tmp_path)


def save_fixture_metadata(target):
    receipt_path = Path(target["lean_proof"]["receipt_path"])
    receipt = json.loads(receipt_path.read_text())
    receipt["conjecture"] = copy.deepcopy(target["conjecture"])
    receipt_path.write_text(json.dumps(receipt))


def test_partial_proposal_snapshot_can_use_fresh_complete_comparators_without_rewriting_history(corpus, tmp_path, monkeypatch):
    target, _, data, _, pack, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    metadata = target["conjecture"]["metadata"]["spectral_refinement"]
    parents = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)["parents"]
    partial = [next(source for source in pack["sources"] if source["source_id"] == "published_radius")]
    metadata["witness_validation"] = frontier.spectral_refinement_witness(
        Conjecture.from_dict(target["conjecture"]), metadata["strictness_witness"], parents, partial)
    assert metadata["witness_validation"]["source_coverage_status"] == "unresolved"
    assert set(metadata["witness_validation"]["missing_comparator_sources"]) == {"energy_edges_over_radius", "energy_sqrt_edges"}
    before = copy.deepcopy(metadata)
    save_fixture_metadata(target)
    record = corpus.review(target)
    fresh = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    validation = fresh["spectral_refinement_validation"]
    assert validation["status"] == "verified_empirical_refinement"
    assert validation["witness_validation"]["source_coverage_status"] == "snapshot_comparators_present"
    assert len(validation["witness_validation"]["comparison_source_bindings"]) == 3
    assert target["conjecture"]["metadata"]["spectral_refinement"] == before
    assert model_review._validate_assessment(response, fresh)["outcome"] == "possible_extension"


def test_missing_comparator_token_remains_unresolved_even_if_the_supplied_quote_is_favorable(corpus, tmp_path, monkeypatch):
    target, _, data, _, pack, _ = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    partial = [next(source for source in pack["sources"] if source["source_id"] == "published_radius")]
    metadata = target["conjecture"]["metadata"]["spectral_refinement"]
    parents = frontier.spectral_refinement_frontier(data, "advanced_spectral", model_review.validate_receipt)["parents"]
    metadata["witness_validation"] = frontier.spectral_refinement_witness(
        Conjecture.from_dict(target["conjecture"]), metadata["strictness_witness"], parents, partial)
    save_fixture_metadata(target)
    record = corpus.review(target)
    monkeypatch.setattr(model_review, "prepare_sources", lambda *args, **kwargs: {
        "sources": copy.deepcopy(partial), "coverage": {"primary_literature": 1, "unavailable": []}, "evidence_key": None})
    fresh = model_review.build_review_source_pack(record, target, data, directory=tmp_path)
    assert fresh["spectral_refinement_validation"]["witness_validation"]["missing_comparator_sources"]
    response = answer(fresh, "possible_extension", 2, "related_context")
    response["contribution"] = "This favorable synthetic assessment lacks the other required comparator texts and cannot establish a relative advance."
    for check in response["checks"]:
        check["status"] = "pass"
    assert model_review._validate_assessment(response, fresh)["outcome"] == "unresolved"


@pytest.mark.parametrize("gap", ["unreadable", "uncompared", "unknown_premises"])
def test_required_comparator_token_cannot_hide_behind_an_unclassified_source(corpus, tmp_path, monkeypatch, gap):
    _, _, _, _, pack, response = ready_refinement_pack(corpus, tmp_path, monkeypatch)
    source = next(item for item in pack["sources"] if item["source_id"] == "published_root_size")
    source["comparison_role"] = "unclassified"
    if gap == "unreadable":
        source["math_readable"] = False
    elif gap == "uncompared":
        response["comparisons"].pop()
        for check in response["checks"]:
            check["source_ids"].remove("published_root_size")
    else:
        response["comparisons"][-1]["premise_relation"] = "unknown"
    result = model_review._validate_assessment(response, pack)
    assert result["outcome"] == "unresolved"
