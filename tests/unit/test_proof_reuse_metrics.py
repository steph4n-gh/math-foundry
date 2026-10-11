from autonomous_math.research_state import proof_reuse_summary


def test_reuse_counts_deduplicate_references_and_keep_old_receipts_unknown():
    atlas = {"theorems": {
        "old": {"status": "LEAN_CERTIFIED", "lean_proof": {}},
        "new": {"status": "LEAN_CERTIFIED", "lean_proof": {
            "reference_tracking": "source_identifier_references", "used_lemma_ids": ["old", "old", "new", "missing"],
            "proof_origin": "fixed_tactic"}, "conjecture": {"metadata": {"origin": "checked_transitivity"}}},
        "candidate": {"status": "EMPIRICAL_SURVIVOR", "lean_proof": {
            "reference_tracking": "source_identifier_references", "used_lemma_ids": ["old"]}},
    }}
    result = proof_reuse_summary(atlas)
    assert result["tracked_proofs"] == result["untracked_proofs"] == 1
    assert result["proofs_referencing_prior_lemmas"] == result["direct_reference_edges"] == 1
    assert result["lemma_use_counts"] == {"old": 1}
    assert result["model_free_compositions"] == 1


def test_untracked_receipt_is_not_counted_as_zero_reuse_observation():
    result = proof_reuse_summary({"theorems": {"old": {"status": "LEAN_CERTIFIED", "lean_proof": {"used_lemma_ids": ["old"]}}}})
    assert result["tracked_proofs"] == 0
    assert result["untracked_proofs"] == 1
    assert result["lemma_use_counts"] == {}
