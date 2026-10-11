import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)
theorem hull3d_independence_number_le_1__1_order_clique_number_1_is_regular_4dc3b3af73f6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (((Fintype.card V : ℝ) - (G.cliqueNum : ℝ)) + (1 : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  obtain ⟨t, ht⟩ := (Gᶜ).exists_isNClique_cliqueNum
  have hinter : (s ∩ t).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have hadj : G.Adj a b :=
      hs.isClique (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1 hab
    have hcompl : Gᶜ.Adj a b :=
      ht.isClique (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2 hab
    exact ((G.compl_adj a b).mp hcompl).2 hadj
  have hsum : s.card + t.card ≤ Fintype.card V + 1 := by
    calc
      s.card + t.card = (s ∪ t).card + (s ∩ t).card :=
        (Finset.card_union_add_card_inter s t).symm
      _ ≤ Fintype.card V + 1 :=
        Nat.add_le_add (Finset.card_le_univ (s ∪ t)) hinter
  rw [hs.card_eq, ht.card_eq] at hsum
  have hreal : (G.cliqueNum : ℝ) + (Gᶜ.cliqueNum : ℝ) ≤
      (Fintype.card V : ℝ) + 1 := by
    exact_mod_cast hsum
  linarith
