import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic







open scoped BigOperators

theorem model_ef33481da37040865734 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≥ (9999999 / 10000000 : ℝ))) :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((((Real.exp (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + ((Fintype.card V : ℝ) - (1 : ℝ))) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + (((((2 : ℝ) * (G.edgeFinset.card : ℝ)) - ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ^ 2)) / (2 : ℝ)) * (Real.exp (-(if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · norm_num [hV] at h_guard
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV] at h_guard ⊢
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let r : ℝ := sSup (Set.range f)
    have hr : 0 ≤ r := by
      change (9999999 / 10000000 : ℝ) ≤ r at h_guard
      linarith only [h_guard]
    have hsum : (∑ w : V, f w) = 0 := by
      simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hvr : f v = r := hv
    have hle (w : V) : f w ≤ r :=
      le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self w)
    let U : Matrix.unitaryGroup V ℝ :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorUnitary
    let P : Matrix V V ℝ := U
    have hdiag : A = Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
        (Matrix.diagonal f) := by
      simpa [A, f, U, RCLike.ofReal_real_eq_id] using
        (G.isHermitian_adjMatrix ℝ).spectral_theorem
    have hfactor : A = P * Matrix.diagonal f * star P := by
      rw [hdiag, Unitary.conjStarAlgAut_apply]
    have hstar : star P * P = 1 := Unitary.coe_star_mul_self U
    have hstar' : P * star P = 1 := Unitary.coe_mul_star_self U
    have hPT : star P = Matrix.transpose P := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have horth (x y : V → ℝ) :
        dotProduct (Matrix.mulVec P x) (Matrix.mulVec P y) = dotProduct x y := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Matrix.mulVec_mulVec, ← hPT, hstar, Matrix.one_mulVec]
    have hquad (x : V → ℝ) :
        dotProduct x (Matrix.mulVec A x) ≤ r * dotProduct x x := by
      let z : V → ℝ := Matrix.mulVec (star P) x
      have hx : Matrix.mulVec P z = x := by
        dsimp only [z]
        rw [Matrix.mulVec_mulVec, hstar', Matrix.one_mulVec]
      have hAx : Matrix.mulVec A x =
          Matrix.mulVec P (Matrix.mulVec (Matrix.diagonal f) z) := by
        rw [hfactor, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hz : dotProduct z z = dotProduct x x := by
        rw [← hx, horth]
      calc
        dotProduct x (Matrix.mulVec A x) =
            dotProduct z (Matrix.mulVec (Matrix.diagonal f) z) := by
          rw [hAx, ← hx, horth]
        _ ≤ r * dotProduct z z := by
          simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i hi
          nlinarith only [mul_le_mul_of_nonneg_right (hle i) (sq_nonneg (z i))]
        _ = r * dotProduct x x := by rw [hz]
    have hAnn (i j : V) : 0 ≤ A i j := by
      dsimp [A, SimpleGraph.adjMatrix]
      split_ifs <;> norm_num
    have hspec (w : V) : |f w| ≤ r := by
      let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis w)
      let y : V → ℝ := fun i => |x i|
      have hxnorm : dotProduct x x = 1 := by
        simpa only [dotProduct, x, ← pow_two, OrthonormalBasis.norm_eq_one, one_pow]
          using (EuclideanSpace.real_norm_sq_eq
            ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis w)).symm
      have hynorm : dotProduct y y = 1 := by
        simpa only [dotProduct, y, ← pow_two, sq_abs] using hxnorm
      have heig : Matrix.mulVec A x = f w • x := by
        simpa only [A, f, x] using
          (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis w
      have hxvalue : dotProduct x (Matrix.mulVec A x) = f w := by
        rw [heig, dotProduct_smul, hxnorm]
        simp
      have habs : |dotProduct x (Matrix.mulVec A x)| ≤
          dotProduct y (Matrix.mulVec A y) := by
        dsimp only [dotProduct, Matrix.mulVec, y]
        simp_rw [Finset.mul_sum]
        calc
          |∑ i : V, ∑ j : V, x i * (A i j * x j)| ≤
              ∑ i : V, |∑ j : V, x i * (A i j * x j)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : V, ∑ j : V, |x i * (A i j * x j)| := by
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : V, ∑ j : V, |x i| * (A i j * |x j|) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul, abs_mul, abs_of_nonneg (hAnn i j)]
      have hyy : dotProduct y (Matrix.mulVec A y) ≤ r := by
        simpa only [hynorm, mul_one] using hquad y
      rw [hxvalue] at habs
      exact habs.trans hyy
    have hlo (w : V) : -r ≤ f w := (abs_le.mp (hspec w)).1
    have htrace (k : ℕ) : Matrix.trace (A ^ k) = ∑ w : V, f w ^ k := by
      rw [hdiag, ← map_pow, Unitary.conjStarAlgAut_apply,
        Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
        Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
      simp only [Pi.pow_apply]
    have hsquares : (∑ w : V, f w ^ 2) = 2 * (G.edgeFinset.card : ℝ) := by
      calc
        (∑ w : V, f w ^ 2) = Matrix.trace (A ^ 2) := (htrace 2).symm
        _ = ∑ w : V, (G.degree w : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply, A, pow_two,
            SimpleGraph.adjMatrix_mul_self_apply_self]
        _ = 2 * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hnegative (t : ℝ) (ht : 0 ≤ t) :
        (1 - t) * Real.exp t ≤ 1 - t ^ 2 / 2 := by
      by_cases ht1 : 1 ≤ t
      · have hm := mul_le_mul_of_nonneg_left
          (Real.add_one_le_exp t) (sub_nonneg.mpr ht1)
        nlinarith only [hm, sq_nonneg t]
      · have ht2 : t < 2 := by linarith only [ht1]
        have hden : 0 < 2 - t := by linarith only [ht2]
        have he : Real.exp t * (2 - t) ≤ 2 + t :=
          (le_div_iff₀ hden).mp (Real.exp_le_two_add_div_two_sub ht ht2)
        have hm := mul_le_mul_of_nonneg_left he
          (show 0 ≤ 1 - t by linarith only [ht1])
        have hc : 0 ≤ t * t ^ 2 := mul_nonneg ht (sq_nonneg t)
        apply (mul_le_mul_iff_of_pos_right hden).mp
        nlinarith only [hm, hc]
    have hpoint (x : ℝ) (hxl : -r ≤ x) :
        1 + x + x ^ 2 / 2 * Real.exp (-r) ≤ Real.exp x := by
      by_cases hx : 0 ≤ x
      · have he : Real.exp (-r) ≤ 1 := by
          simpa only [Real.exp_zero] using
            (Real.exp_le_exp.mpr (neg_nonpos.mpr hr))
        have hm := mul_le_mul_of_nonneg_left he
          (show (0 : ℝ) ≤ x ^ 2 / 2 by positivity)
        nlinarith only [hm, Real.quadratic_le_exp_of_nonneg hx]
      · have hn : (1 + x) * Real.exp (-x) ≤ 1 - x ^ 2 / 2 := by
          simpa only [sub_neg_eq_add, neg_sq] using
            hnegative (-x) (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hx)))
        have hm := mul_le_mul_of_nonneg_right hn (Real.exp_nonneg x)
        have heq : Real.exp (-x) * Real.exp x = 1 := by
          rw [← Real.exp_add]
          simp
        rw [mul_assoc, heq, mul_one] at hm
        have hc := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxl)
          (show (0 : ℝ) ≤ x ^ 2 / 2 by positivity)
        nlinarith only [hm, hc]
    have hres (w : V) :
        0 ≤ Real.exp (f w) - (1 + f w + f w ^ 2 / 2 * Real.exp (-r)) :=
      sub_nonneg.mpr (hpoint (f w) (hlo w))
    have hpolysum :
        (∑ w : V, (1 + f w + f w ^ 2 / 2 * Real.exp (-r))) =
          (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) * Real.exp (-r) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, hsum, ← Finset.sum_mul, ← Finset.sum_div, hsquares]
      ring
    have hsingle :
        Real.exp (f v) - (1 + f v + f v ^ 2 / 2 * Real.exp (-r)) ≤
          ∑ w : V, (Real.exp (f w) -
            (1 + f w + f w ^ 2 / 2 * Real.exp (-r))) :=
      Finset.single_le_sum (fun w _ => hres w) (Finset.mem_univ v)
    rw [Finset.sum_sub_distrib, hpolysum, hvr] at hsingle
    change Real.exp r + ((Fintype.card V : ℝ) - 1) - r +
      ((2 * (G.edgeFinset.card : ℝ) - r ^ 2) / 2) * Real.exp (-r) ≤
        ∑ w : V, Real.exp (f w)
    nlinarith only [hsingle]
