import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

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

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity
theorem model_09e1e211ed16a9f315c7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) + (((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))) * (((2 : ℝ) * ((Int.ceil (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) / (2 : ℝ))) : ℝ)) - ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ))))) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  let c : ℕ := cw.min' hcw
  let r : ℝ := ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  change (c : ℝ) ≥ r + ((G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ)) * (2 * (Int.ceil (r / 2) : ℝ) - r)
  have hbase : r ≤ (c : ℝ) := parity_code_unique_neighbor_distance G
  rcases Nat.even_or_odd G.minDegree with he | ho
  · obtain ⟨k, hk⟩ := he
    have hkreal : (G.minDegree : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hdiv : (G.minDegree : ℝ) / 2 = (k : ℝ) := by linarith only [hkreal]
    have hf : Int.floor ((G.minDegree : ℝ) / 2) = (k : ℤ) := by
      rw [hdiv, Int.floor_natCast]
    have hcoef : (G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) = 0 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    rw [hcoef]
    simpa only [zero_mul, add_zero] using hbase
  · have hoddcast : (G.minDegree : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr ho
    obtain ⟨k, hk⟩ := ho
    have hkreal : (G.minDegree : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have hf : Int.floor ((G.minDegree : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hkreal]
    have hcoef : (G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) = 1 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    have hnull : 0 < Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) := by
      by_contra hn
      have hz : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) = 0 := by omega
      have h := h_guard.2.2
      rw [hz] at h
      norm_num at h
    letI : Nontrivial (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) := Module.nontrivial_of_finrank_pos (R := ZMod 2) hnull
    obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
    have hxne : (x : V → ZMod 2) ≠ 0 := by
      intro h
      apply hx
      exact Subtype.ext h
    have hxword : (x : V → ZMod 2) ∈ words := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hxne, LinearMap.mem_ker.mp x.property⟩
    have hxmem : hammingNorm (x : V → ZMod 2) ∈ cw := by
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(x : V → ZMod 2), hxword, rfl⟩))
    have hc_card : c ≤ Fintype.card V := by
      exact (Finset.min'_le cw _ hxmem).trans hammingNorm_le_card_fintype
    obtain ⟨y, hy, hyc⟩ : ∃ y ∈ words, hammingNorm y = c := by
      rcases Finset.mem_union.mp (show c ∈ cw from Finset.min'_mem cw hcw) with h | h
      · have hs : c = Fintype.card V + 1 := Finset.mem_singleton.mp h
        omega
      · exact Finset.mem_image.mp h
    obtain ⟨v, hv⟩ : ∃ v, (x : V → ZMod 2) v ≠ 0 := by
      by_contra h
      apply hxne
      funext v
      exact not_not.mp (not_exists.mp h v)
    letI : Nonempty V := ⟨v⟩
    have hregular : G.IsRegularOfDegree G.minDegree := by
      obtain ⟨d, hd⟩ := h_guard.1
      have hmd : G.minDegree = d := hd.minDegree_eq
      rw [hmd]
      exact hd
    have hone : Matrix.mulVec (G.adjMatrix (ZMod 2)) (1 : V → ZMod 2) = 1 := by
      funext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2)) (Function.const V (1 : ZMod 2))) v = 1
      rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hregular, hoddcast, one_mul]
    have hyzero : Matrix.mulVec (G.adjMatrix (ZMod 2)) y = 0 := by
      simpa only [Matrix.mulVecLin_apply] using (Finset.mem_filter.mp hy).2.2
    have hsumzero : (∑ v, y v) = (0 : ZMod 2) := by
      have hs := (G.isSymm_adjMatrix (α := ZMod 2)).dotProduct_mulVec_comm (x := (1 : V → ZMod 2)) (y := y)
      rw [hyzero, hone] at hs
      simpa [dotProduct] using hs.symm
    have hweight : (hammingNorm y : ZMod 2) = ∑ v, y v := by
      calc
        (hammingNorm y : ZMod 2) = ∑ v ∈ Finset.univ.filter (fun v => y v ≠ 0), (1 : ZMod 2) := by
          simp [hammingNorm]
        _ = ∑ v ∈ Finset.univ.filter (fun v => y v ≠ 0), y v := by
          apply Finset.sum_congr rfl
          intro v hv
          have hne : y v ≠ 0 := (Finset.mem_filter.mp hv).2
          have hval : (y v).val = 1 := by
            have hp : 0 < (y v).val := ZMod.val_pos.mpr hne
            have hlt := ZMod.val_lt (y v)
            omega
          exact ((ZMod.val_eq_one (by decide) (y v)).mp hval).symm
        _ = ∑ v, y v := Finset.sum_filter_ne_zero (Finset.univ : Finset V)
    have hc_even : Even c := by
      rw [← hyc]
      exact ZMod.natCast_eq_zero_iff_even.mp (hweight.trans hsumzero)
    obtain ⟨m, hm⟩ := hc_even
    have hcreal : (c : ℝ) = (m : ℝ) + (m : ℝ) := by exact_mod_cast hm
    have hceil : Int.ceil (r / 2) ≤ (m : ℤ) := by
      apply Int.ceil_le.mpr
      push_cast
      linarith only [hbase, hcreal]
    have hceilreal : (Int.ceil (r / 2) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hceil
    rw [hcoef]
    simp only [one_mul]
    linarith only [hceilreal, hcreal]
