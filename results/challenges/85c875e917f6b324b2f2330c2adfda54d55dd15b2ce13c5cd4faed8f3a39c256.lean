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

theorem model_a00de82f9ab8ab051b93 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Gᶜ.cliqueNum : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Gᶜ.cliqueNum : ℝ) - (1 : ℝ)) * (((Gᶜ.cliqueNum : ℝ) * (((2 : ℝ) * (G.edgeFinset.card : ℝ)) + (Fintype.card V : ℝ))) - ((Fintype.card V : ℝ) ^ 2))) ≥ ((((Gᶜ.cliqueNum : ℝ) * (G.chromaticNumber.toNat : ℝ)) - (Fintype.card V : ℝ)) ^ 2) := by
  sorry
