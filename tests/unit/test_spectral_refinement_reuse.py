"""Suggested foundations prioritize only the exact already-validated receipt."""
import copy

import pytest

from autonomous_math.conjecturing.model_proposals import proposal_statement_key
from autonomous_math.core.ast import Conjecture, ConstantNode, InvariantNode
from autonomous_math.prover.lean_prover import LeanProofSearch


def checked(identifier, value):
    candidate = Conjecture.create(id=identifier, lhs=ConstantNode(value), rel="<=",
                                 rhs=InvariantNode("graph_energy"))
    receipt = {"conjecture_id": identifier, "theorem_name": identifier, "conjecture": candidate.to_dict(),
               **{key: identifier + ":" + key for key in ("receipt_path", "source_sha256", "challenge_sha256",
                   "workspace_sha256", "lean_binary_sha256")}}
    binding = {key: receipt[key] for key in ("receipt_path", "theorem_name", "source_sha256", "challenge_sha256",
               "workspace_sha256", "lean_binary_sha256")}
    binding.update(parent_id=identifier, statement_key=proposal_statement_key(candidate))
    return receipt, binding


def fixture():
    library = [checked(f"aaa_{i}", i + 1)[0] for i in range(20)]
    parent, binding = checked("zzz_foundation", 21)
    target = Conjecture.create(id="new_refinement", lhs=ConstantNode(100), rel="<=",
        rhs=InvariantNode("graph_energy"), metadata={"spectral_refinement": {"parent_bindings": [binding]}})
    return target, library + [parent], binding


def test_exact_parent_binding_is_prioritized_without_exceeding_context_bound():
    target, library, _ = fixture()
    selected = LeanProofSearch()._select_reuse(target, library)
    assert selected[0]["conjecture_id"] == "zzz_foundation"
    assert len(selected) == LeanProofSearch.REUSE_LIMIT


@pytest.mark.parametrize("field", ["parent_id", "statement_key", "receipt_path", "theorem_name", "source_sha256",
                                  "challenge_sha256", "workspace_sha256", "lean_binary_sha256"])
def test_tampered_parent_binding_cannot_prioritize_a_declaration(field):
    target, library, binding = fixture()
    binding[field] = "tampered"
    assert all(r["conjecture_id"] != "zzz_foundation" for r in LeanProofSearch()._select_reuse(target, library))


def test_metadata_cannot_import_an_absent_receipt():
    target, library, _ = fixture()
    assert all(r["conjecture_id"] != "zzz_foundation" for r in LeanProofSearch()._select_reuse(target, library[:-1]))


def test_metadata_does_not_override_exact_statement_reuse():
    target, library, _ = fixture()
    exact, _ = checked("exact_existing", 100)
    selected = LeanProofSearch()._select_reuse(target, library + [exact])
    assert selected == [exact]
