import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

open scoped BigOperators

theorem hull_normalized_laplacian_spectral_radius_le_0_complement_spectral_radius_2_b7beb0d09a33 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues))) ≤ (((0 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (2 : ℝ)) := by
  classical
  simp only [zero_mul, zero_add]
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let hA := Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  change (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range hA.eigenvalues)) ≤ 2
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    norm_num
  · rw [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    have hD : Matrix.conjTranspose D = D := by
      apply Matrix.IsHermitian.eq
      exact Matrix.isHermitian_diagonal_iff.mpr (fun i => IsSelfAdjoint.all _)
    have hL (y : V → ℝ) :
        dotProduct y (Matrix.mulVec (G.lapMatrix ℝ) y) ≤
          2 * ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
      have hr :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y a) ^ 2 else 0) =
            ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [G.degree_eq_sum_if_adj (R := ℝ) a]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      have hc :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y b) ^ 2 else 0) =
            ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
        rw [Finset.sum_comm]
        calc
          (∑ b : V, ∑ a : V, if G.Adj a b then (y b) ^ 2 else 0) =
              ∑ b : V, ∑ a : V, if G.Adj b a then (y b) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            simp only [G.adj_comm a b]
          _ = _ := hr
      have hb :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y a - y b) ^ 2 else 0) ≤
            2 * (∑ a : V, ∑ b : V, if G.Adj a b then (y a) ^ 2 else 0) +
            2 * (∑ a : V, ∑ b : V, if G.Adj a b then (y b) ^ 2 else 0) := by
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        by_cases hab : G.Adj a b
        · simp only [if_pos hab]
          nlinarith only [sq_nonneg (y a + y b)]
        · simp only [if_neg hab, mul_zero, add_zero, le_refl]
      rw [hr, hc] at hb
      rw [← Matrix.toLinearMap₂'_apply', G.lapMatrix_toLinearMap₂' ℝ y]
      linarith only [hb]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let x : EuclideanSpace ℝ V := hA.eigenvectorBasis i
    have hn : (∑ v : V, (x v) ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq x]
      simp only [x, OrthonormalBasis.norm_eq_one, one_pow]
    have hleft : Matrix.vecMul (⇑x) D = Matrix.mulVec D (⇑x) := by
      ext v
      simp only [D, Matrix.vecMul_diagonal, Matrix.mulVec_diagonal]
      exact mul_comm _ _
    have heig : hA.eigenvalues i =
        dotProduct (Matrix.mulVec D (⇑x))
          (Matrix.mulVec (G.lapMatrix ℝ) (Matrix.mulVec D (⇑x))) := by
      calc
        hA.eigenvalues i =
            dotProduct (⇑x)
              (Matrix.mulVec (D * G.lapMatrix ℝ * Matrix.conjTranspose D) (⇑x)) := by
          simpa only [x, star_trivial, RCLike.re_to_real] using hA.eigenvalues_eq i
        _ = _ := by
          rw [hD, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            Matrix.dotProduct_mulVec, hleft]
    have hweight :
        (∑ v : V, (G.degree v : ℝ) * ((Matrix.mulVec D (⇑x)) v) ^ 2) ≤ 1 := by
      calc
        _ ≤ ∑ v : V, (x v) ^ 2 := by
          apply Finset.sum_le_sum
          intro v _
          simp only [D, Matrix.mulVec_diagonal]
          by_cases hv : G.degree v = 0
          · simpa only [hv, Nat.cast_zero, zero_mul] using sq_nonneg (x v)
          · have hd : (G.degree v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv
            have hs : (Real.sqrt (G.degree v : ℝ)) ^ 2 = (G.degree v : ℝ) :=
              Real.sq_sqrt (Nat.cast_nonneg (G.degree v))
            simp only [mul_pow, ← mul_assoc, inv_pow, hs,
              mul_inv_cancel₀ hd, one_mul, le_refl]
        _ = 1 := hn
    have hquad := hL (Matrix.mulVec D (⇑x))
    rw [← heig] at hquad
    linarith only [hquad, hweight]
