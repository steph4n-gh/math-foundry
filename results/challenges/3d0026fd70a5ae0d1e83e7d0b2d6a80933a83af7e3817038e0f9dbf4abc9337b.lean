import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic




open scoped BigOperators
theorem model_92debe23dc15135cb8a8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Gᶜ.cliqueNum : ℝ) * (((2 : ℝ) * (G.edgeFinset.card : ℝ)) + (Fintype.card V : ℝ))) ≥ ((Fintype.card V : ℝ) ^ 2) := by
  classical
  let w : V → ℝ := fun v => 1 / ((G.degree v : ℝ) + 1)
  have hpos (v : V) : 0 < (G.degree v : ℝ) + 1 := by positivity
  have haux : ∀ s : Finset V,
      ∃ t : Finset V, t ⊆ s ∧ Gᶜ.IsClique (t : Set V) ∧
        (∑ v ∈ s, w v) ≤ (t.card : ℝ) := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih
    by_cases hs : s = ∅
    · subst s
      exact ⟨∅, by simp, by simp, by simp⟩
    · obtain ⟨v, hv, hmin⟩ := s.exists_min_image (fun v : V => G.degree v)
        (Finset.nonempty_iff_ne_empty.mpr hs)
      let c : Finset V := insert v (G.neighborFinset v)
      let u : Finset V := s \ c
      have hus : u ⊆ s := Finset.sdiff_subset
      have hvu : v ∉ u := by simp [u, c]
      have hu : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr
        ⟨hus, fun h => hvu (h.symm ▸ hv)⟩
      obtain ⟨t, ht, htc, htw⟩ := ih u hu
      let b : Finset V := s \ u
      have hbc : b ⊆ c := by
        intro x hx
        have hxs : x ∈ s := (Finset.mem_sdiff.mp hx).1
        have hxnu : x ∉ u := (Finset.mem_sdiff.mp hx).2
        by_contra hxnc
        exact hxnu (Finset.mem_sdiff.mpr ⟨hxs, hxnc⟩)
      have hbcard : b.card ≤ G.degree v + 1 := by
        calc
          b.card ≤ c.card := Finset.card_le_card hbc
          _ = G.degree v + 1 := by
            change (insert v (G.neighborFinset v)).card = G.degree v + 1
            rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
              G.card_neighborFinset_eq_degree]
      have hbcardReal : (b.card : ℝ) ≤ (G.degree v : ℝ) + 1 := by
        exact_mod_cast hbcard
      have hblock : (∑ x ∈ b, w x) ≤ (1 : ℝ) := by
        calc
          (∑ x ∈ b, w x) ≤ ∑ _x ∈ b, 1 / ((G.degree v : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro x hx
            have hdx : G.degree v ≤ G.degree x :=
              hmin x (Finset.mem_sdiff.mp hx).1
            have hdxReal : (G.degree v : ℝ) + 1 ≤ (G.degree x : ℝ) + 1 := by
              exact_mod_cast (Nat.add_le_add_right hdx 1)
            change 1 / ((G.degree x : ℝ) + 1) ≤ 1 / ((G.degree v : ℝ) + 1)
            exact one_div_le_one_div_of_le (hpos v) hdxReal
          _ = (b.card : ℝ) * (1 / ((G.degree v : ℝ) + 1)) := by simp
          _ ≤ ((G.degree v : ℝ) + 1) * (1 / ((G.degree v : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hbcardReal (le_of_lt (one_div_pos.mpr (hpos v)))
          _ = 1 := mul_one_div_cancel (hpos v).ne'
      have hvnt : v ∉ t := fun h => hvu (ht h)
      refine ⟨insert v t, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxt
        · exact hv
        · exact hus (ht hxt)
      · rw [Finset.coe_insert]
        apply htc.insert
        intro x hx hne
        apply (SimpleGraph.compl_adj G v x).mpr
        refine ⟨hne, ?_⟩
        intro hadj
        exact (Finset.mem_sdiff.mp (ht hx)).2
          (Finset.mem_insert_of_mem ((G.mem_neighborFinset v x).mpr hadj))
      · have hsplit : (∑ x ∈ b, w x) + (∑ x ∈ u, w x) = ∑ x ∈ s, w x :=
          Finset.sum_sdiff hus
        calc
          (∑ x ∈ s, w x) = (∑ x ∈ b, w x) + (∑ x ∈ u, w x) := hsplit.symm
          _ ≤ (1 : ℝ) + (t.card : ℝ) := add_le_add hblock htw
          _ = ((insert v t).card : ℝ) := by
            rw [Finset.card_insert_of_notMem hvnt, Nat.cast_add, Nat.cast_one]
            ring
  obtain ⟨t, _, htc, htw⟩ := haux Finset.univ
  have hcw : (∑ v : V, w v) ≤ (Gᶜ.cliqueNum : ℝ) := by
    calc
      (∑ v : V, w v) ≤ (t.card : ℝ) := htw
      _ ≤ (Gᶜ.cliqueNum : ℝ) := by exact_mod_cast htc.card_le_cliqueNum
  have hcs : (Fintype.card V : ℝ) ^ 2 ≤
      (∑ v : V, w v) * (∑ v : V, ((G.degree v : ℝ) + 1)) := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset V)
      (r := fun _ : V => (1 : ℝ))
      (f := w)
      (g := fun v : V => (G.degree v : ℝ) + 1)
      (fun v _ => by
        change 0 ≤ 1 / ((G.degree v : ℝ) + 1)
        exact le_of_lt (one_div_pos.mpr (hpos v)))
      (fun v _ => le_of_lt (hpos v))
      (fun v _ => by
        change (1 : ℝ) ^ 2 ≤
          (1 / ((G.degree v : ℝ) + 1)) * ((G.degree v : ℝ) + 1)
        rw [one_div_mul_cancel (hpos v).ne']
        norm_num)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h
  have hsumdeg : (∑ v : V, ((G.degree v : ℝ) + 1)) =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) + (Fintype.card V : ℝ) := by
    rw [Finset.sum_add_distrib]
    have hdeg : (∑ v : V, (G.degree v : ℝ)) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hdeg]
    simp
  rw [hsumdeg] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hcw (by positivity))

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

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem model_886a365b7173b119a27a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Gᶜ.cliqueNum : ℝ) + (G.edgeFinset.card : ℝ)) ≥ (Fintype.card V : ℝ) := by
  classical
  let T : Finset V := G.edgeFinset.image (fun e : Sym2 V => e.out.1)
  let S : Finset V := Finset.univ \ T
  have hT : T.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hS : Gᶜ.IsClique (S : Set V) := by
    intro u hu v hv hne
    change u ≠ v ∧ ¬ G.Adj u v
    refine ⟨hne, ?_⟩
    intro huv
    have he : s(u, v) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr huv)
    have hm : (s(u, v) : Sym2 V).out.1 ∈ T :=
      Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v))) with h | h
    · apply (Finset.mem_sdiff.mp hu).2
      exact h ▸ hm
    · apply (Finset.mem_sdiff.mp hv).2
      exact h ▸ hm
  have hclique : S.card ≤ Gᶜ.cliqueNum := hS.card_le_cliqueNum
  have hcards : S.card + T.card = Fintype.card V := by
    simpa only [S, Finset.card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T))
  have hnat : Fintype.card V ≤ Gᶜ.cliqueNum + G.edgeFinset.card := by
    omega
  exact_mod_cast hnat

theorem model_8ce30216566f34c2605a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ)) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    let t : Finset V := Finset.univ \ s
    have hcover : G.edgeFinset ⊆ t.biUnion (fun v => G.incidenceFinset v) := by
      intro e
      refine Sym2.inductionOn e ?_
      intro v w he
      have hadj : G.Adj v w := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      by_cases hv : v ∈ s
      · have hw : w ∉ s := by
          intro hw
          exact ((SimpleGraph.compl_adj G v w).mp (hs.isClique hv hw hadj.ne)).2 hadj
        refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
        · simp [t, hw]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_right_iff] using hadj
      · refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
        · simp [t, hv]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_left_iff] using hadj
    have hn : G.edgeFinset.card ≤ t.card * G.maxDegree := by
      calc
        G.edgeFinset.card ≤ (t.biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ t, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ t, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ t, G.maxDegree :=
          Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
        _ = t.card * G.maxDegree := by simp
    have hcard : t.card + Gᶜ.cliqueNum = Fintype.card V := by
      simpa only [t, hs.card_eq, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcard_real : (t.card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have ht : (t.card : ℝ) = (Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ) := by
      linarith
    have hbound : (G.edgeFinset.card : ℝ) ≤ (t.card : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hn
    rw [ht] at hbound
    exact hbound
theorem model_c9e8fb9fc8b8b997104d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Gᶜ.cliqueNum : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Gᶜ.cliqueNum : ℝ) - (1 : ℝ)) * (((Gᶜ.cliqueNum : ℝ) * (((2 : ℝ) * (G.edgeFinset.card : ℝ)) + (Fintype.card V : ℝ))) - ((Fintype.card V : ℝ) ^ 2))) ≥ ((max (0 : ℝ) (((Gᶜ.cliqueNum : ℝ) * (G.cliqueNum : ℝ)) - (Fintype.card V : ℝ))) ^ 2) := by
  sorry
