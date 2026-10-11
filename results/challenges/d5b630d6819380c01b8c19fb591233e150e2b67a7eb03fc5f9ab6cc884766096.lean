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

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity

theorem chung_normalized_laplacian_gap_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) ≤ ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - (1 : ℝ))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hsmall : Fintype.card V ≤ 1 := by omega
    have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hsmall
    linarith only [h_guard, hsmallR]
  have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hden : 0 < (Fintype.card V : ℝ) - 1 := by linarith only [hnR]
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  dsimp only
  by_cases hconn : G.Connected
  · rw [if_pos hconn, dif_pos hn]
    let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
    let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
    have hM : M.IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
    have hp : M.PosSemidef :=
      (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
    let f : Fin (Fintype.card V) → ℝ := hM.eigenvalues₀
    let e : Fin (Fintype.card V) ≃ V :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
    let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
    change f k ≤ (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)
    have heig (i : Fin (Fintype.card V)) : hM.eigenvalues (e i) = f i := by
      simp only [Matrix.IsHermitian.eigenvalues, e, f, Equiv.symm_apply_apply]
    have hnn (i : Fin (Fintype.card V)) : 0 ≤ f i := by
      rw [← heig i, hM.eigenvalues_eq (e i)]
      simpa only [RCLike.re_to_real] using
        hp.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e i)))
    have hsum : (∑ i : Fin (Fintype.card V), f i) = M.trace := by
      calc
        _ = ∑ v : V, hM.eigenvalues v :=
          Fintype.sum_equiv e f hM.eigenvalues (fun i => (heig i).symm)
        _ = M.trace := hM.trace_eq_sum_eigenvalues.symm
    have hdet : M.det = 0 := by
      simp only [M, Matrix.det_mul, G.det_lapMatrix_eq_zero ℝ, mul_zero, zero_mul]
    have hprod : (∏ v : V, hM.eigenvalues v) = 0 := by
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        (hM.det_eq_prod_eigenvalues.symm.trans hdet)
    obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hz : f (e.symm v) = 0 := by
      rw [← heig (e.symm v), Equiv.apply_symm_apply]
      exact hv
    have hlz : e.symm v ≤ l := by
      change (e.symm v).val ≤ Fintype.card V - 1
      have hlt := (e.symm v).isLt
      omega
    have hlast : f l = 0 := by
      apply le_antisymm
      · calc
          f l ≤ f (e.symm v) := hM.eigenvalues₀_antitone hlz
          _ = 0 := hz
      · exact hnn l
    have hdiag (v : V) : M v v ≤ (1 : ℝ) := by
      have hentry : M v v =
          (Real.sqrt (G.degree v : ℝ))⁻¹ * (G.degree v : ℝ) *
            (Real.sqrt (G.degree v : ℝ))⁻¹ := by
        simp [M, D, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
      rw [hentry]
      by_cases hzero : (G.degree v : ℝ) = 0
      · simp [hzero]
      · have hsqrt : Real.sqrt (G.degree v : ℝ) ≠ 0 :=
          (Real.sqrt_ne_zero (Nat.cast_nonneg _)).mpr hzero
        calc
          _ = (Real.sqrt (G.degree v : ℝ))⁻¹ *
              (Real.sqrt (G.degree v : ℝ) * Real.sqrt (G.degree v : ℝ)) *
                (Real.sqrt (G.degree v : ℝ))⁻¹ := by
            rw [Real.mul_self_sqrt (Nat.cast_nonneg (G.degree v))]
          _ = 1 := by
            rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul, mul_inv_cancel₀ hsqrt]
          _ ≤ 1 := le_rfl
    have htrace : M.trace ≤ (Fintype.card V : ℝ) := by
      calc
        M.trace = ∑ v : V, M v v := rfl
        _ ≤ ∑ _v : V, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hdiag v)
        _ = (Fintype.card V : ℝ) := by simp
    let s : Finset (Fin (Fintype.card V)) := Finset.univ.erase l
    have hscard : s.card = Fintype.card V - 1 := by simp [s]
    have hs : (∑ i ∈ s, f i) = M.trace := by
      have h := Finset.sum_erase_add
        (Finset.univ : Finset (Fin (Fintype.card V))) f (Finset.mem_univ l)
      rw [hlast, add_zero] at h
      exact h.trans hsum
    have havg : ((Fintype.card V - 1 : ℕ) : ℝ) * f k ≤ M.trace := by
      calc
        _ = ∑ i ∈ s, f k := by
          simp only [Finset.sum_const, nsmul_eq_mul, hscard]
        _ ≤ ∑ i ∈ s, f i := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_ne : i ≠ l := (Finset.mem_erase.mp hi).1
          have hival : i.val ≠ Fintype.card V - 1 := by
            intro heq
            exact hi_ne (Fin.ext heq)
          have hik : i ≤ k := by
            change i.val ≤ Fintype.card V - 2
            have hlt := i.isLt
            omega
          exact hM.eigenvalues₀_antitone hik
        _ = M.trace := hs
    have hnat : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply (le_div_iff₀ hden).mpr
    calc
      f k * ((Fintype.card V : ℝ) - 1) =
          ((Fintype.card V - 1 : ℕ) : ℝ) * f k := by rw [hnat, mul_comm]
      _ ≤ M.trace := havg
      _ ≤ (Fintype.card V : ℝ) := htrace
  · rw [if_neg hconn]
    exact div_nonneg (Nat.cast_nonneg _) hden.le

theorem hull3d_unique_neighbor_radius_ge_1_0_normalized_laplacian_spectral_gap_order_0_is_bipartite_f9946b253195 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) := by
  sorry
