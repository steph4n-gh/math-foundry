import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem generative_chromatic_degree_pilot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  have hpartial : ∀ s : Finset V,
      ∃ c : V → Fin (G.maxDegree + 1),
        ∀ v ∈ s, ∀ w ∈ s, G.Adj v w → c v ≠ c w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩, ?_⟩
        intro v hv
        simp at hv
    | @insert a s ha ih =>
        obtain ⟨c, hc⟩ := ih
        have hcard : ((G.neighborFinset a).image c).card <
            (Finset.univ : Finset (Fin (G.maxDegree + 1))).card := by
          calc
            ((G.neighborFinset a).image c).card ≤
                (G.neighborFinset a).card := Finset.card_image_le
            _ = G.degree a := rfl
            _ ≤ G.maxDegree := G.degree_le_maxDegree a
            _ < (Finset.univ : Finset (Fin (G.maxDegree + 1))).card := by simp
        obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hdc : ∀ w, G.Adj a w → d ≠ c w := by
          intro w haw heq
          apply hd
          exact Finset.mem_image.mpr
            ⟨w, (G.mem_neighborFinset a w).mpr haw, heq.symm⟩
        refine ⟨fun v => if v = a then d else c v, ?_⟩
        intro v hv w hw hvw
        by_cases hva : v = a
        · subst v
          have hwa : w ≠ a := hvw.ne'
          simpa [hwa] using hdc w hvw
        · by_cases hwa : w = a
          · subst w
            simpa [hva] using (hdc v hvw.symm).symm
          · have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
            have hws : w ∈ s := (Finset.mem_insert.mp hw).resolve_left hwa
            simpa [hva, hwa] using hc v hvs w hws hvw
  obtain ⟨c, hc⟩ := hpartial Finset.univ
  have hcolor : G.Colorable (G.maxDegree + 1) :=
    ⟨SimpleGraph.Coloring.mk c (fun {v w} h =>
      hc v (Finset.mem_univ v) w (Finset.mem_univ w) h)⟩
  have hn : G.chromaticNumber.toNat ≤ G.maxDegree + 1 :=
    ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  exact_mod_cast hn

theorem hull_chromatic_number_le_1_size_1_658db08f8c3d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  have hmax : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  have hmaxR : (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hmax
  have h := generative_chromatic_degree_pilot G
  linarith

theorem composed_1f689b2150941b00 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  exact le_trans (archetype_chi_ge_omega G) (hull_chromatic_number_le_1_size_1_658db08f8c3d G)

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

theorem hull3d_clique_number_le_0_0_1_estrada_index_size_9_1_is_regular_300bb35a749b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.cliqueNum : ℝ) ≤ (((1 / 10 : ℝ) * (G.edgeFinset.card : ℝ)) + (91 / 10 : ℝ)) := by
  obtain ⟨d, hd⟩ := h_guard
  have hmax : (G.maxDegree : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast G.maxDegree_le_of_forall_degree_le d
      (fun v => (hd.degree_eq v).le)
  have hclique : (G.cliqueNum : ℝ) - 1 ≤ (d : ℝ) := by
    have hk := clique_le_max_degree_plus_one G
    linarith only [hk, hmax]
  have horder := composed_2cd2dd810fbb9720 G
  have hsum : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      using G.sum_degrees_eq_twice_card_edges
  have hprod : (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) ≤
      2 * (G.edgeFinset.card : ℝ) := by
    calc
      (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) ≤
          (G.cliqueNum : ℝ) * (d : ℝ) :=
        mul_le_mul_of_nonneg_left hclique (Nat.cast_nonneg _)
      _ ≤ (Fintype.card V : ℝ) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right horder (Nat.cast_nonneg _)
      _ = 2 * (G.edgeFinset.card : ℝ) := by exact_mod_cast hsum
  nlinarith only [hprod, sq_nonneg (2 * (G.cliqueNum : ℝ) - 21)]

theorem hull3d_clique_number_le_0_1_estrada_index_size_1_is_regular_281545d7bef9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.cliqueNum : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  have hdeg : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  have hdegR : (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hdeg
  have hclique := clique_le_max_degree_plus_one G
  linarith
theorem hull_clique_number_le_0_25_size_2_5_e8558e9f6029 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (((1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)) + (5 / 2 : ℝ)) := by
  sorry
