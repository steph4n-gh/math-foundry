"""The clean project carries mathematical knowledge without old process history."""
import copy
import json
from pathlib import Path
import pytest
from autonomous_math.research_state import ROOT, _validated_seed, load_snapshot


def test_fresh_output_uses_validated_seed_without_run_history(tmp_path):
    atlas = load_snapshot(tmp_path)
    assert atlas["baseline_boundary_graphs"] == 23
    assert len(atlas["theorems"]) == 23
    assert atlas["total_iterations"] == atlas["total_refuted"] == atlas["total_conjectures_generated"] == 0
    assert {r["status"] for r in atlas["theorems"].values()} == {"REFUTED"}
    assert not atlas.get("flywheel_lemmas") and not atlas.get("random_state")
    atlas["theorems"].clear()
    assert len(load_snapshot(tmp_path)["theorems"]) == 23


@pytest.mark.parametrize("alteration", ["identity", "hash", "relation"])
def test_changed_seed_is_rechecked(alteration):
    data = json.loads((ROOT/'seed/counterexamples.json').read_text())
    record = data["records"][0]
    if alteration == "identity":
        record["counterexample"]["conjecture_id"] = "other_claim"
    elif alteration == "hash":
        record["counterexample"]["verification_hash"] = "0"*64
    else:
        record["conjecture"]["rel"] = ">="
    with pytest.raises(ValueError):
        _validated_seed(json.dumps(data).encode())


def test_evaluation_selects_only_common_starting_bounds(monkeypatch):
    import evaluate_self_improvement as evaluation
    data = json.loads((ROOT/'library/catalog.json').read_text())['theorems']
    receipts = {item['id']: {'conjecture': item['conjecture']} for item in data}
    atlas = {'theorems': {item['id']: {'status': 'LEAN_CERTIFIED'} for item in data},
             'flywheel_lemmas': [{'lemma_id': item['id'], 'receipt_path': item['id']} for item in data]}
    monkeypatch.setattr(evaluation, 'validate_receipt', lambda path, ident: (receipts[ident], None))
    selected = evaluation.initial_library(atlas)
    assert {item['lemma_id'] for item in selected} == {
        'chromatic_le_order', 'archetype_chi_ge_omega', 'composed_2cd2dd810fbb9720'}
