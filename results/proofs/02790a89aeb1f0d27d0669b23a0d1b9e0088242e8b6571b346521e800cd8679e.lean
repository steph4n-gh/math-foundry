import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic





theorem hull3d_clique_number_le_0_0357143_0_triangle_count_radius_6_is_connected_ba575443a060 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.cliqueNum : ℝ) ≤ (((892857142857143 / 25000000000000000 : ℝ) * ((G.cliqueFinset 3).card : ℝ)) + (6 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hsub : s.powersetCard 3 ⊆ G.cliqueFinset 3 := by
    intro t ht
    obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    refine ⟨?_, htcard⟩
    intro v hv w hw hne
    exact hs.isClique (hts hv) (hts hw) hne
  have hcount : G.cliqueNum.choose 3 ≤ (G.cliqueFinset 3).card := by
    simpa only [Finset.card_powersetCard, hs.card_eq] using
      Finset.card_le_card hsub
  have hbound : ∀ n : ℕ, 28 * n ≤ n.choose 3 + 168 := by
    intro n
    induction n with
    | zero => norm_num [Nat.choose]
    | succ n ih =>
      by_cases hn : n < 8
      · interval_cases n <;> norm_num [Nat.choose]
      · have htwo : 28 ≤ n.choose 2 := by
          simpa [Nat.choose] using
            (Nat.choose_le_choose 2 (show 8 ≤ n by omega))
        change 28 * (n + 1) ≤ n.choose 2 + n.choose 3 + 168
        omega
  have hnat : 28 * G.cliqueNum ≤ (G.cliqueFinset 3).card + 168 :=
    (hbound G.cliqueNum).trans (Nat.add_le_add_right hcount 168)
  have hreal : (28 : ℝ) * (G.cliqueNum : ℝ) ≤
      ((G.cliqueFinset 3).card : ℝ) + 168 := by
    exact_mod_cast hnat
  have hnonneg : (0 : ℝ) ≤ ((G.cliqueFinset 3).card : ℝ) :=
    Nat.cast_nonneg _
  linarith only [hreal, hnonneg]

theorem hull3d_clique_number_le_0_1_0_triangle_count_radius_4_66667_is_connected_4d92cb1e01e5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.cliqueNum : ℝ) ≤ (((1 / 10 : ℝ) * ((G.cliqueFinset 3).card : ℝ)) + (4666666666666667 / 1000000000000000 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hsub : s.powersetCard 3 ⊆ G.cliqueFinset 3 := by
    intro t ht
    obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    refine ⟨?_, htcard⟩
    intro u hu v hv huv
    exact hs.isClique (hts hu) (hts hv) huv
  have htri : G.cliqueNum.choose 3 ≤ (G.cliqueFinset 3).card := by
    have h := Finset.card_le_card hsub
    simpa only [Finset.card_powersetCard, hs.card_eq] using h
  have hnum : ∀ n : ℕ, 10 * n ≤ n.choose 3 + 40 := by
    intro n
    induction n with
    | zero => norm_num [Nat.choose]
    | succ n ih =>
        by_cases hn : n < 5
        · interval_cases n <;> norm_num [Nat.choose]
        · have htwo : 10 ≤ n.choose 2 := by
            calc
              10 = Nat.choose 5 2 := by norm_num [Nat.choose]
              _ ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
          have hstep : (n + 1).choose 3 = n.choose 2 + n.choose 3 :=
            Nat.choose_succ_succ n 2
          rw [hstep]
          omega
  have hnat : 10 * G.cliqueNum ≤ (G.cliqueFinset 3).card + 40 :=
    (hnum G.cliqueNum).trans (Nat.add_le_add_right htri 40)
  have hreal : (10 : ℝ) * (G.cliqueNum : ℝ) ≤
      ((G.cliqueFinset 3).card : ℝ) + 40 := by
    exact_mod_cast hnat
  linarith

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))
theorem hull3d_clique_number_le_1_0_triangle_count_radius_2_is_connected_cd22e0a14a95 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.cliqueNum : ℝ) ≤ (((G.cliqueFinset 3).card : ℝ) + (2 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hsub : s.powersetCard 3 ⊆ G.cliqueFinset 3 := by
    intro t ht
    obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    refine ⟨?_, htcard⟩
    intro v hv w hw hne
    exact hs.isClique (hts hv) (hts hw) hne
  have htri : G.cliqueNum.choose 3 ≤ (G.cliqueFinset 3).card := by
    simpa only [Finset.card_powersetCard, hs.card_eq] using
      Finset.card_le_card hsub
  have hnum : ∀ n : ℕ, n ≤ n.choose 3 + 2 := by
    intro n
    induction n with
    | zero => norm_num [Nat.choose]
    | succ n ih =>
      by_cases hn : n < 2
      · interval_cases n <;> norm_num [Nat.choose]
      · have htwo : 1 ≤ n.choose 2 := by
          calc
            1 = Nat.choose 2 2 := by norm_num [Nat.choose]
            _ ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
        have hstep : (n + 1).choose 3 = n.choose 2 + n.choose 3 :=
          Nat.choose_succ_succ n 2
        rw [hstep]
        omega
  have hnat : G.cliqueNum ≤ (G.cliqueFinset 3).card + 2 :=
    (hnum G.cliqueNum).trans (Nat.add_le_add_right htri 2)
  exact_mod_cast hnat
