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

theorem model_db893752e0181a616e22 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≥ (9999999 / 10000000 : ℝ)))) :
    ((∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) - (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) ≥ ((((Fintype.card V : ℝ) / (2 : ℝ)) * (((Real.exp (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (Real.exp (-(Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) - ((2 : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) + ((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) / (14 : ℝ))) := by
  classical
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    linarith only [h_guard.1]
  have hn0 : Fintype.card V ≠ 0 := by
    exact_mod_cast hnpos.ne'
  let n : ℝ := Fintype.card V
  let q : ℝ := 2 * (G.edgeFinset.card : ℝ) / n
  let r : ℝ := Real.sqrt q
  have hn : 0 ≤ n := hnpos.le
  have hnne : n ≠ 0 := hnpos.ne'
  have hqpos : 0 < q := by
    have hg := h_guard.2
    simp only [if_neg hn0] at hg
    change q ≥ (9999999 / 10000000 : ℝ) at hg
    linarith only [hg]
  have hq : 0 ≤ q := hqpos.le
  have hr : 0 ≤ r := Real.sqrt_nonneg q
  have hrpos : 0 < r := Real.sqrt_pos.mpr hqpos
  have hrsq : r ^ 2 = q := Real.sq_sqrt hq
  have hnq : n * q = 2 * (G.edgeFinset.card : ℝ) := by
    exact mul_div_cancel₀ _ hnne
  have hkernel (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
      0 ≤ 2520 + 7 * (s * (t + s) ^ 2) * (t ^ 2 + 2 * s ^ 2) -
        150 * (s * (t + s) ^ 2) := by
    let X : ℝ := t ^ 2 + 2 * s ^ 2
    let B : ℝ := s * (t + s) ^ 2
    let z : ℝ := Real.sqrt X
    have hX : 0 ≤ X := by
      dsimp only [X]
      positivity
    have hB : 0 ≤ B := mul_nonneg hs (sq_nonneg (t + s))
    have hz : 0 ≤ z := Real.sqrt_nonneg X
    have hz2 : z ^ 2 = X := Real.sq_sqrt hX
    have hC : 0 ≤ 16 * t ^ 4 + 32 * s * t ^ 3 +
        117 * s ^ 2 * t ^ 2 + 94 * s ^ 3 * t + 101 * s ^ 4 := by
      positivity
    have hp := mul_nonneg (sq_nonneg (t - s)) hC
    have hid : 16 * X ^ 3 - 27 * B ^ 2 =
        (t - s) ^ 2 * (16 * t ^ 4 + 32 * s * t ^ 3 +
          117 * s ^ 2 * t ^ 2 + 94 * s ^ 3 * t + 101 * s ^ 4) := by
      dsimp only [X, B]
      ring
    have hbound : 27 * B ^ 2 ≤ 16 * X ^ 3 := by
      have hh : 0 ≤ 16 * X ^ 3 - 27 * B ^ 2 := by
        rw [hid]
        exact hp
      linarith only [hh]
    have hb : B ≤ (4 / 5 : ℝ) * z ^ 3 := by
      apply le_of_sq_le_sq ?_ (mul_nonneg (by norm_num) (pow_nonneg hz 3))
      calc
        B ^ 2 ≤ (16 / 27 : ℝ) * X ^ 3 := by
          nlinarith only [hbound]
        _ ≤ (16 / 25 : ℝ) * X ^ 3 :=
          mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hX 3)
        _ = ((4 / 5 : ℝ) * z ^ 3) ^ 2 := by
          rw [← hz2]
          ring
    have hz5 : 0 ≤ z ^ 5 := pow_nonneg hz 5
    have hcub : 0 ≤ 3 * z ^ 3 + 6 * (18 / 5 : ℝ) * z ^ 2 +
        4 * (18 / 5 : ℝ) ^ 2 * z + 2 * (18 / 5 : ℝ) ^ 3 := by
      positivity
    have hy := mul_nonneg (sq_nonneg (z - (18 / 5 : ℝ))) hcub
    have hyid : (z - (18 / 5 : ℝ)) ^ 2 *
        (3 * z ^ 3 + 6 * (18 / 5 : ℝ) * z ^ 2 +
          4 * (18 / 5 : ℝ) ^ 2 * z + 2 * (18 / 5 : ℝ) ^ 3) =
        3 * z ^ 5 - 5 * (18 / 5 : ℝ) ^ 2 * z ^ 3 +
          2 * (18 / 5 : ℝ) ^ 5 := by
      ring
    rw [hyid] at hy
    have hzP : 0 ≤ 3150 + 7 * z ^ 5 - 150 * z ^ 3 := by
      nlinarith only [hy, hz5]
    change 0 ≤ 2520 + 7 * B * X - 150 * B
    by_cases hx : 150 ≤ 7 * X
    · have hh := mul_nonneg hB (sub_nonneg.mpr hx)
      nlinarith only [hh]
    · have hx' : 7 * X - 150 ≤ 0 := by
        linarith only [hx]
      have hm := mul_le_mul_of_nonpos_right hb hx'
      have hh : 0 ≤ 2520 + ((4 / 5 : ℝ) * z ^ 3) * (7 * X - 150) := by
        have hh' := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) hzP
        have heq : (4 / 5 : ℝ) * (3150 + 7 * z ^ 5 - 150 * z ^ 3) =
            2520 + ((4 / 5 : ℝ) * z ^ 3) * (7 * X - 150) := by
          rw [← hz2]
          ring
        rwa [heq] at hh'
      nlinarith only [hm, hh]
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      t + (5 / 168 : ℝ) * (t ^ 2 - q) ^ 2 ≤
        r + (t ^ 2 - q) / (2 * r) +
          (t ^ 2 - q) ^ 2 * (t ^ 2 + 2 * q) / 720 := by
    have hk := hkernel t r ht hr
    have hp := mul_nonneg (sq_nonneg (t - r)) hk
    have hh : t + (5 / 168 : ℝ) * (t ^ 2 - q) ^ 2 -
        (t ^ 2 - q) ^ 2 * (t ^ 2 + 2 * q) / 720 - r ≤
          (t ^ 2 - q) / (2 * r) := by
      rw [← hrsq]
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrpos)).2
      apply sub_nonneg.mp
      have hid : t ^ 2 - r ^ 2 -
          (t + (5 / 168 : ℝ) * (t ^ 2 - r ^ 2) ^ 2 -
            (t ^ 2 - r ^ 2) ^ 2 * (t ^ 2 + 2 * r ^ 2) / 720 - r) * (2 * r) =
          (t - r) ^ 2 *
            (2520 + 7 * (r * (t + r) ^ 2) * (t ^ 2 + 2 * r ^ 2) -
              150 * (r * (t + r) ^ 2)) / 2520 := by
        ring
      rw [hid]
      exact div_nonneg hp (by norm_num)
    linarith only [hh]
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let U : Matrix.unitaryGroup V ℝ := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  have hspec : A = φ (Matrix.diagonal f) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
  have htr (B : Matrix V V ℝ) : Matrix.trace (φ B) = Matrix.trace B := by
    change Matrix.trace ((U : Matrix V V ℝ) * B *
      (star U : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have htrace (k : ℕ) : (∑ v : V, f v ^ k) = Matrix.trace (A ^ k) := by
    rw [hspec, ← map_pow, Matrix.diagonal_pow, htr, Matrix.trace_diagonal]
    simp only [Pi.pow_apply]
  have hentry (u v : V) : 0 ≤ A u v := by
    simp only [A, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hpow (k : ℕ) : ∀ u v : V, 0 ≤ (A ^ k) u v := by
    induction k with
    | zero =>
      intro u v
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
    | succ k ih =>
      intro u v
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (ih u w) (hentry w v))
  have hmoment (k : ℕ) : 0 ≤ ∑ v : V, f v ^ k := by
    rw [htrace k]
    exact Finset.sum_nonneg (fun v _ => hpow k v v)
  have hsumdeg : (∑ v : V, (G.degree v : ℝ)) = n * q := by
    calc
      _ = 2 * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ = n * q := hnq.symm
  have hsquare : (∑ v : V, f v ^ 2) = n * q := by
    calc
      _ = Matrix.trace (A ^ 2) := htrace 2
      _ = ∑ v : V, (G.degree v : ℝ) := by
        simp only [A, pow_two, Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self]
      _ = n * q := hsumdeg
  have hmean (k : ℕ) : n * q ^ k ≤ ∑ v : V, (f v ^ 2) ^ k := by
    calc
      n * q ^ k = ∑ v : V,
          (q ^ k + (k : ℝ) * q ^ (k - 1) * (f v ^ 2 - q)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hsquare]
        change n * q ^ k = n * q ^ k +
          (k : ℝ) * q ^ (k - 1) * (n * q - n * q)
        ring
      _ ≤ ∑ v : V, (f v ^ 2) ^ k := by
        apply Finset.sum_le_sum
        intro v _
        have hv : 0 ≤ 2 * q + (f v ^ 2 - q) := by
          nlinarith only [hq, sq_nonneg (f v)]
        simpa only [add_sub_cancel] using (pow_add_mul_le_add_pow hq hv k)
  have hrow (v : V) : (∑ w : V, A v w) = (G.degree v : ℝ) := by
    simpa only [A, SimpleGraph.adjMatrix_apply] using
      (G.degree_eq_sum_if_adj (R := ℝ) v).symm
  have hcol (v : V) : (∑ w : V, A w v) = (G.degree v : ℝ) := by
    calc
      _ = ∑ w : V, A v w := by
        apply Finset.sum_congr rfl
        intro w _
        exact (G.isSymm_adjMatrix (α := ℝ)).apply v w
      _ = (G.degree v : ℝ) := hrow v
  have hBsum : (∑ u : V, ∑ v : V, (A ^ 2) u v) =
      ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    calc
      _ = ∑ u : V, ∑ v : V, ∑ w : V, A u w * A w v := by
        simp only [pow_two, Matrix.mul_apply]
      _ = ∑ u : V, ∑ w : V, A u w * (∑ v : V, A w v) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ w : V, (∑ u : V, A u w) * (G.degree w : ℝ) := by
        simp only [hrow]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = ∑ v : V, (G.degree v : ℝ) ^ 2 := by
        simp only [hcol, pow_two]
  have hBdiag (u : V) : (A ^ 2) u u = (G.degree u : ℝ) := by
    simpa only [A, pow_two] using
      (G.adjMatrix_mul_self_apply_self (α := ℝ) u)
  have hBint (u v : V) : (A ^ 2) u v ≤ ((A ^ 2) u v) ^ 2 := by
    change (G.adjMatrix ℝ ^ 2) u v ≤ ((G.adjMatrix ℝ ^ 2) u v) ^ 2
    rw [G.adjMatrix_pow_apply_eq_card_walk 2 u v, pow_two]
    exact_mod_cast
      (Nat.le_mul_self (Fintype.card {p : G.Walk u v | p.length = 2}))
  have hBsym : (A ^ 2).IsSymm := (G.isSymm_adjMatrix (α := ℝ)).pow 2
  have hfour_eq : (∑ v : V, f v ^ 4) =
      ∑ u : V, ∑ v : V, ((A ^ 2) u v) ^ 2 := by
    rw [htrace 4]
    have hp : A ^ 4 = A ^ 2 * A ^ 2 := pow_add A 2 2
    rw [hp]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hBsym.apply u v]
    exact (pow_two ((A ^ 2) u v)).symm
  have hfour : 2 * (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ≤
      ∑ v : V, f v ^ 4 := by
    calc
      _ = ∑ u : V, ∑ v : V,
          ((A ^ 2) u v +
            if u = v then (G.degree u : ℝ) ^ 2 - (G.degree u : ℝ) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        rw [hBsum, Finset.sum_sub_distrib, hsumdeg]
        ring
      _ ≤ ∑ u : V, ∑ v : V, ((A ^ 2) u v) ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        by_cases huv : u = v
        · subst v
          rw [if_pos rfl, hBdiag u]
          nlinarith only []
        · rw [if_neg huv, add_zero]
          exact hBint u v
      _ = ∑ v : V, f v ^ 4 := hfour_eq.symm
  have hdsq : n * q ^ 2 ≤ ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    have hh : 0 ≤ ∑ v : V, ((G.degree v : ℝ) - q) ^ 2 :=
      Finset.sum_nonneg (fun v _ => sq_nonneg _)
    have heq : (∑ v : V, ((G.degree v : ℝ) - q) ^ 2) =
        (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ^ 2 := by
      have hp (v : V) : ((G.degree v : ℝ) - q) ^ 2 =
          (G.degree v : ℝ) ^ 2 - (2 * q) * (G.degree v : ℝ) + q ^ 2 := by
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (∑ v : V, (G.degree v : ℝ) ^ 2) -
        (2 * q) * (∑ v : V, (G.degree v : ℝ)) + n * q ^ 2 =
          (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ^ 2
      rw [hsumdeg]
      ring
    rw [heq] at hh
    linarith only [hh]
  let T : ℝ := ∑ v : V, (f v ^ 2 - q) ^ 2
  have hTid : T = (∑ v : V, f v ^ 4) - n * q ^ 2 := by
    dsimp only [T]
    have hp (v : V) : (f v ^ 2 - q) ^ 2 =
        f v ^ 4 - (2 * q) * (f v ^ 2) + q ^ 2 := by
      ring
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ v : V, f v ^ 4) - (2 * q) * (∑ v : V, f v ^ 2) + n * q ^ 2 =
      (∑ v : V, f v ^ 4) - n * q ^ 2
    rw [hsquare]
    ring
  have hTlower : n * q * (q - 1) ≤ T := by
    rw [hTid]
    nlinarith only [hfour, hdsq]
  let W : ℝ := ∑ v : V, (f v ^ 2 - q) ^ 2 * (f v ^ 2 + 2 * q)
  have hWid : W = (∑ v : V, f v ^ 6) - n * q ^ 3 := by
    dsimp only [W]
    have hp (v : V) : (f v ^ 2 - q) ^ 2 * (f v ^ 2 + 2 * q) =
        f v ^ 6 - (3 * q ^ 2) * (f v ^ 2) + 2 * q ^ 3 := by
      ring
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ v : V, f v ^ 6) - (3 * q ^ 2) * (∑ v : V, f v ^ 2) +
        2 * (n * q ^ 3) = (∑ v : V, f v ^ 6) - n * q ^ 3
    rw [hsquare]
    ring
  have hE : (∑ v : V, |f v|) + (5 / 168 : ℝ) * T ≤ n * r + W / 720 := by
    have hh : (∑ v : V, (|f v| + (5 / 168 : ℝ) * (f v ^ 2 - q) ^ 2)) ≤
        ∑ v : V, (r + (f v ^ 2 - q) / (2 * r) +
          (f v ^ 2 - q) ^ 2 * (f v ^ 2 + 2 * q) / 720) := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [sq_abs] using hpoint |f v| (abs_nonneg _)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hh
    change (∑ v : V, |f v|) + (5 / 168 : ℝ) * T ≤
      n * r + ((∑ v : V, f v ^ 2) - n * q) / (2 * r) + W / 720 at hh
    rw [hsquare, sub_self, zero_div, add_zero] at hh
    exact hh
  have hexpseries (x : ℝ) :
      HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
    apply (Real.summable_pow_div_factorial x).hasSum_iff_tendsto_nat.mpr
    have hc : Filter.Tendsto
        (fun k : ℕ => ∑ i ∈ Finset.range k,
          (x : ℂ) ^ i / (Nat.factorial i : ℂ))
        Filter.atTop (nhds (Complex.exp (x : ℂ))) := by
      rw [Complex.exp]
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := (CauSeq.equiv_lim (Complex.exp' (x : ℂ))) ε hε
      refine ⟨N, fun k hk => ?_⟩
      rw [dist_eq_norm]
      change ‖(Complex.exp' (x : ℂ)) k - (Complex.exp' (x : ℂ)).lim‖ < ε
      exact hN k hk
    apply Filter.tendsto_ofReal_iff.mp
    simpa only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_exp] using hc
  have hcoeff (k : ℕ) :
      n / 2 * (r ^ k / (Nat.factorial k : ℝ) +
        (-r) ^ k / (Nat.factorial k : ℝ)) ≤
      (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) := by
    rcases Nat.even_or_odd k with he | ho
    · have hm : n * r ^ k ≤ ∑ v : V, f v ^ k := by
        obtain ⟨l, hl⟩ := even_iff_exists_two_mul.mp he
        simpa only [hl, pow_mul, hrsq] using hmean l
      calc
        _ = (n * r ^ k) / (Nat.factorial k : ℝ) := by
          rw [he.neg_pow]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)
    · rw [ho.neg_pow]
      have hf0 : 0 ≤ (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) :=
        div_nonneg (hmoment k) (Nat.cast_nonneg _)
      simpa only [neg_div, add_neg_cancel, mul_zero] using hf0
  have hcoeff' (k : ℕ) :
      n / 2 * (r ^ k / (Nat.factorial k : ℝ) +
        (-r) ^ k / (Nat.factorial k : ℝ)) +
        (if k = 4 then T / 24 else 0) + (if k = 6 then W / 720 else 0) ≤
      (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) := by
    by_cases hk4 : k = 4
    · subst k
      apply le_of_eq
      rw [if_pos rfl, if_neg (by norm_num : (4 : ℕ) ≠ 6)]
      have hr4 : r ^ 4 = q ^ 2 := by
        calc
          _ = (r ^ 2) ^ 2 := by ring
          _ = q ^ 2 := by rw [hrsq]
      have hneg4 : (-r) ^ 4 = r ^ 4 := by ring
      rw [hneg4, hr4, hTid]
      norm_num [Nat.factorial] <;> ring
    · by_cases hk6 : k = 6
      · subst k
        apply le_of_eq
        rw [if_neg (by norm_num : (6 : ℕ) ≠ 4), if_pos rfl]
        have hr6 : r ^ 6 = q ^ 3 := by
          calc
            _ = (r ^ 2) ^ 3 := by ring
            _ = q ^ 3 := by rw [hrsq]
        have hneg6 : (-r) ^ 6 = r ^ 6 := by ring
        rw [hneg6, hr6, hWid]
        norm_num [Nat.factorial] <;> ring
      · simp only [if_neg hk4, if_neg hk6, add_zero]
        exact hcoeff k
  have hserA :
      HasSum (fun k : ℕ => (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ))
        (∑ v : V, Real.exp (f v)) := by
    simpa only [Finset.sum_div] using
      (hasSum_sum (s := (Finset.univ : Finset V))
        (fun v _ => hexpseries (f v)))
  have hserR :
      HasSum (fun k : ℕ => n / 2 *
        (r ^ k / (Nat.factorial k : ℝ) + (-r) ^ k / (Nat.factorial k : ℝ)))
        (n / 2 * (Real.exp r + Real.exp (-r))) :=
    ((hexpseries r).add (hexpseries (-r))).mul_left (n / 2)
  have hserR' :
      HasSum (fun k : ℕ => n / 2 *
        (r ^ k / (Nat.factorial k : ℝ) + (-r) ^ k / (Nat.factorial k : ℝ)) +
        (if k = 4 then T / 24 else 0) + (if k = 6 then W / 720 else 0))
        (n / 2 * (Real.exp r + Real.exp (-r)) + T / 24 + W / 720) :=
    (hserR.add (hasSum_ite_eq (4 : ℕ) (T / 24))).add
      (hasSum_ite_eq (6 : ℕ) (W / 720))
  have hEE : n / 2 * (Real.exp r + Real.exp (-r)) + T / 24 + W / 720 ≤
      ∑ v : V, Real.exp (f v) :=
    hasSum_le hcoeff' hserR' hserA
  simp only [if_neg hn0]
  change (∑ v : V, Real.exp (f v)) - (∑ v : V, |f v|) ≥
    n / 2 * (Real.exp r + Real.exp (-r) - 2 * r) + n * q * (q - 1) / 14
  nlinarith only [hEE, hE, hTlower]

theorem model_1ea93541073a670fffde {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.minDegree : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    ((∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) - (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) ≥ ((Fintype.card V : ℝ) + ((G.edgeFinset.card : ℝ) / (3 : ℝ))) := by
  sorry
