import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem clique_le_max_degree_plus_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hn : G.cliqueNum ≤ G.maxDegree + 1 := by
    by_cases he : s.Nonempty
    · obtain ⟨v, hv⟩ := he
      have hsubset : s.erase v ⊆ G.neighborFinset v := by
        intro w hw
        rw [G.mem_neighborFinset]
        exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
      have hmax := G.degree_le_maxDegree v
      have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
      omega
    · have : G.cliqueNum = 0 := by
        rw [← hs.card_eq]
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
      omega
  exact_mod_cast hn

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith
theorem hull3d_clique_number_le_0_1_estrada_index_size_1_is_regular_281545d7bef9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.cliqueNum : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  sorry
