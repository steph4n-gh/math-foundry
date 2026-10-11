from pathlib import Path
import pytest
from autonomous_math.prover.lean_prover import LeanToolchain, LeanProofSearch
from autonomous_math.core.ast import Conjecture, InvariantNode, BinaryOpNode, ConstantNode

def test_real_toolchain():
    tc=LeanToolchain()
    assert tc.is_available and tc.ensure_workspace_built()
    assert tc.workspace_dir.name=="certified_lean"

@pytest.mark.parametrize("name",["diameter","radius","girth","adjacency_spectrum","is_planar"])
def test_unsupported_invariant_cannot_be_certified(name,tmp_path):
    c=Conjecture.create(id="legacy_bound",lhs=InvariantNode(name),rel=">=",rhs=ConstantNode(0))
    r=LeanProofSearch().prove_conjecture(c,output_dir=tmp_path)
    assert not r.is_proven and "formalization" in r.error_message
    assert not list(tmp_path.glob("*.receipt.json"))

def test_broken_existing_proof(tmp_path):
    r=LeanProofSearch().prove_challenge("import Mathlib\ntheorem broken : False := by\n  trivial\n",output_dir=tmp_path)
    assert not r.is_proven and r.diagnostics

def test_tactics_contain_no_custom_graph_axioms():
    assert all("G.flywheel" not in t.tactic_code for t in LeanProofSearch().generate_candidate_scripts(""))
