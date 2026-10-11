import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity

theorem parity_code_unique_neighbor_distance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 ≤ (cw.min' hcw : ℝ)
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hle : sw.min' hsw ≤ cw.min' hcw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [sw])
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
      have hxcode := (Finset.mem_filter.mp hx).2.2
      let S : Finset V := Finset.univ.filter (fun w => x w ≠ 0)
      have hSnonempty : S.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < hammingNorm x
        exact hammingNorm_pos_iff.mpr hxne
      have hSstop : S ∈ stops := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hSnonempty, ?_⟩
        rintro ⟨v, w, hw, hvw, hu⟩
        have hxw : x w ≠ 0 := (Finset.mem_filter.mp hw).2
        have heq : ∑ a ∈ G.neighborFinset v, x a = x w := by
          apply Finset.sum_eq_single w
          · intro a ha hne
            by_contra hxa
            have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩
            exact hne (hu a haS ((G.mem_neighborFinset v a).mp ha))
          · intro hnot
            exact (hnot ((G.mem_neighborFinset v w).mpr hvw)).elim
        have hzero : ∑ a ∈ G.neighborFinset v, x a = 0 := by
          simpa [Matrix.mulVecLin_apply] using congrFun hxcode v
        exact hxw (heq.symm.trans hzero)
      apply Finset.min'_le
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨S, hSstop, rfl⟩))
  have hn : sw.min' hsw - 1 + 1 ≤ cw.min' hcw := by omega
  exact_mod_cast hn

theorem hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  change (weights.min' hw : ℝ) ≤ (Fintype.card V : ℝ) + 1
  have h : weights.min' hw ≤ Fintype.card V + 1 :=
    Finset.min'_le _ _ (by simp [weights])
  exact_mod_cast h
theorem model_77a1528e1be7c262c434 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (min (2 : ℝ) ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) - (1 : ℝ))) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change min (2 : ℝ) ((cw.min' hcw : ℝ) - 1) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ)
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have haeq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hsmall : ∀ S ∈ stops, S.card ≤ 2 → cw.min' hcw ≤ S.card := by
    intro S hS hcard
    have hnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2.1
    have hstop : ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w) :=
      (Finset.mem_filter.mp hS).2.2
    let x : V → ZMod 2 := fun w => if w ∈ S then 1 else 0
    have hxnorm : hammingNorm x = S.card := by
      change (Finset.univ.filter (fun w => x w ≠ 0)).card = S.card
      congr 1
      ext w
      by_cases hw : w ∈ S <;> simp [x, hw]
    have hxne : x ≠ 0 := by
      apply hammingNorm_pos_iff.mp
      rw [hxnorm]
      exact hnonempty.card_pos
    have hxker : (G.adjMatrix (ZMod 2)).mulVecLin x = 0 := by
      funext v
      let T : Finset V := S.filter (fun w => G.Adj v w)
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hTle : T.card ≤ 2 := (Finset.card_le_card hTS).trans hcard
      have hnotone : T.card ≠ 1 := by
        intro h
        obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h
        have hwT : w ∈ T := by rw [hw]; simp
        have hwS : w ∈ S := (Finset.mem_filter.mp hwT).1
        have hvw : G.Adj v w := (Finset.mem_filter.mp hwT).2
        apply hstop
        refine ⟨v, w, hwS, hvw, ?_⟩
        intro u hu huv
        have huT : u ∈ T := Finset.mem_filter.mpr ⟨hu, huv⟩
        rw [hw] at huT
        exact Finset.mem_singleton.mp huT
      have hcases : T.card = 0 ∨ T.card = 2 := by omega
      have hcast : (T.card : ZMod 2) = 0 := by
        rcases hcases with hzero | htwo
        · rw [hzero]
          rfl
        · rw [htwo]
          exact ZMod.natCast_self 2
      have hfilter : (G.neighborFinset v).filter (fun w => w ∈ S) = T := by
        ext w
        simp [T, and_comm]
      have hsum : ∑ w ∈ G.neighborFinset v, x w = 0 := by
        calc
          ∑ w ∈ G.neighborFinset v, x w =
              ∑ w ∈ (G.neighborFinset v).filter (fun w => w ∈ S), (1 : ZMod 2) := by
                simp only [x, Finset.sum_filter]
          _ = ∑ w ∈ T, (1 : ZMod 2) := by rw [hfilter]
          _ = (T.card : ZMod 2) := by simp
          _ = 0 := hcast
      simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using hsum
    have hxwords : x ∈ words :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩
    have hxmem : hammingNorm x ∈ cw :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, hxwords, rfl⟩))
    have hbound : cw.min' hcw ≤ hammingNorm x := Finset.min'_le _ _ hxmem
    simpa only [hxnorm] using hbound
  by_cases hlarge : 3 ≤ sw.min' hsw
  · have hn : 2 ≤ sw.min' hsw - 1 := by omega
    have hr : (2 : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    exact (min_le_left _ _).trans hr
  · have hsmallmin : sw.min' hsw ≤ 2 := by omega
    have hle : cw.min' hcw ≤ sw.min' hsw := by
      have hm : sw.min' hsw ∈ sw := Finset.min'_mem sw hsw
      rcases Finset.mem_union.mp hm with hm | hm
      · have hs : sw.min' hsw = Fintype.card V + 1 := Finset.mem_singleton.mp hm
        rw [hs]
        exact Finset.min'_le _ _ (by simp [cw])
      · obtain ⟨S, hS, hScard⟩ := Finset.mem_image.mp hm
        have hScardle : S.card ≤ 2 := by omega
        calc
          cw.min' hcw ≤ S.card := hsmall S hS hScardle
          _ = sw.min' hsw := hScard
    have hn : cw.min' hcw ≤ sw.min' hsw - 1 + 1 := by omega
    have hr : (cw.min' hcw : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hn
    exact (min_le_right _ _).trans (by linarith)
