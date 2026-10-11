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

theorem model_24baa9bb5c5a3c6be85d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≥ (9999999 / 10000000 : ℝ))) :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((((Real.exp (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + ((Fintype.card V : ℝ) - (1 : ℝ))) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + (((((2 : ℝ) * (G.edgeFinset.card : ℝ)) - ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ^ 2)) / ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ^ 2)) * (((Real.exp (-(if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (1 : ℝ)))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · norm_num [hV] at h_guard
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV] at h_guard ⊢
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let r : ℝ := sSup (Set.range f)
    have hr : 0 < r := by
      change (9999999 / 10000000 : ℝ) ≤ r at h_guard
      linarith only [h_guard]
    have hsum : (∑ w : V, f w) = 0 := by
      simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
    let U : Matrix.unitaryGroup V ℝ :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorUnitary
    have hdiag : A = Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
        (Matrix.diagonal f) := by
      simpa [A, f, U, RCLike.ofReal_real_eq_id] using
        (G.isHermitian_adjMatrix ℝ).spectral_theorem
    have htrace (k : ℕ) : Matrix.trace (A ^ k) = ∑ w : V, f w ^ k := by
      rw [hdiag, ← map_pow, Unitary.conjStarAlgAut_apply,
        Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
        Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
      simp only [Pi.pow_apply]
    have hnonneg (k : ℕ) : 0 ≤ Matrix.trace (A ^ k) := by
      change 0 ≤ ∑ w : V, (G.adjMatrix ℝ ^ k) w w
      apply Finset.sum_nonneg
      intro w hw
      rw [G.adjMatrix_pow_apply_eq_card_walk k w w]
      exact Nat.cast_nonneg _
    have hsecond : Matrix.trace (A ^ 2) = 2 * (G.edgeFinset.card : ℝ) := by
      calc
        Matrix.trace (A ^ 2) = ∑ w : V, (G.degree w : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply, A, pow_two,
            SimpleGraph.adjMatrix_mul_self_apply_self]
        _ = 2 * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hsq : (∑ w : V, f w ^ 2) = 2 * (G.edgeFinset.card : ℝ) := by
      rw [← htrace 2]
      exact hsecond
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    change f v = r at hv
    have hle (w : V) : f w ≤ r :=
      le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self w)
    have hmin (w : V) : -r ≤ f w := by
      by_contra hbad
      have hbad' : f w < -r := lt_of_not_ge hbad
      let a : ℝ := -f w / r
      have ha : 1 < a := by
        change 1 < -f w / r
        apply (one_lt_div hr).2
        linarith only [hbad']
      have ha2 : (1 : ℝ) < a ^ 2 := by
        nlinarith only [ha, sq_nonneg (a - 1)]
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (Fintype.card V : ℝ) ha2
      let p : ℕ := 2 * k + 1
      have hpodd : Odd p := ⟨k, rfl⟩
      have hsumodd : 0 ≤ ∑ i : V, f i ^ p := by
        rw [← htrace p]
        exact hnonneg p
      rw [← Finset.add_sum_erase Finset.univ (fun i => f i ^ p)
        (Finset.mem_univ w)] at hsumodd
      have hrest : (∑ i ∈ Finset.univ.erase w, f i ^ p) ≤
          (Fintype.card V : ℝ) * r ^ p := by
        calc
          (∑ i ∈ Finset.univ.erase w, f i ^ p) ≤
              ∑ i ∈ Finset.univ.erase w, r ^ p :=
            Finset.sum_le_sum (fun i _ => hpodd.strictMono_pow.monotone (hle i))
          _ ≤ ∑ i : V, r ^ p :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.erase_subset w Finset.univ)
              (fun i _ _ => (pow_pos hr p).le)
          _ = (Fintype.card V : ℝ) * r ^ p := by simp
      have hnums : (-f w) ^ p ≤ (Fintype.card V : ℝ) * r ^ p := by
        rw [hpodd.neg_pow]
        linarith only [hsumodd, hrest]
      have hbound : a ^ p ≤ (Fintype.card V : ℝ) := by
        dsimp [a]
        rw [div_pow]
        exact (div_le_iff₀ (pow_pos hr p)).2 hnums
      have hp : a ^ p = (a ^ 2) ^ k * a := by
        dsimp [p]
        rw [pow_add, pow_one, pow_mul]
      have hmul : 0 ≤ (a ^ 2) ^ k * (a - 1) :=
        mul_nonneg (pow_nonneg (sq_nonneg a) k) (by linarith only [ha])
      have hpowle : (a ^ 2) ^ k ≤ a ^ p := by
        rw [hp]
        nlinarith only [hmul]
      linarith only [hk, hbound, hpowle]
    let q : ℝ → ℝ := fun x => (Real.exp x - 1 - x) / x ^ 2
    let s : ℝ → ℝ := fun x => (Real.exp x - 1) / x
    have hqnonneg (x : ℝ) : 0 ≤ q x := by
      dsimp [q]
      apply div_nonneg
      · linarith only [Real.add_one_le_exp x]
      · exact sq_nonneg x
    have hsnonneg (x : ℝ) : 0 ≤ s x := by
      dsimp [s]
      by_cases hx : 0 ≤ x
      · exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp hx)) hx
      · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
        exact div_nonneg_of_nonpos
          (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx')) hx'
    have hsmono (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≤ b) :
        s a ≤ s b := by
      simpa only [s, Real.exp_zero, sub_zero] using
        (convexOn_exp.secant_mono (a := 0) (x := a) (y := b)
          (Set.mem_univ 0) (Set.mem_univ a) (Set.mem_univ b) ha hb hab)
    have hdouble (x : ℝ) (hx : x ≠ 0) :
        q (2 * x) = q x / 2 + s x ^ 2 / 4 := by
      have he : Real.exp (2 * x) = Real.exp x * Real.exp x := by
        rw [two_mul, Real.exp_add]
      dsimp [q, s]
      rw [he]
      field_simp [hx] <;> ring
    have hqsmall (x : ℝ) (hx : x ≠ 0) (hsmall : |x| ≤ 1) : q x ≤ 1 := by
      dsimp [q]
      apply (div_le_iff₀ (sq_pos_of_ne_zero hx)).2
      simpa only [one_mul] using
        ((le_abs_self (Real.exp x - 1 - x)).trans
          (Real.abs_exp_sub_one_sub_id_le hsmall))
    have hscale (x : ℝ) (n : ℕ) :
        2 * (x / (2 : ℝ) ^ (n + 1)) = x / (2 : ℝ) ^ n := by
      have hn : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [pow_succ]
      field_simp [hn] <;> ring
    have hqmono (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≤ b) :
        q a ≤ q b := by
      by_contra hbad
      have hd : 0 < q a - q b := sub_pos.mpr (lt_of_not_ge hbad)
      have hiter (n : ℕ) :
          (2 : ℝ) ^ n * (q a - q b) ≤
            q (a / (2 : ℝ) ^ n) - q (b / (2 : ℝ) ^ n) := by
        induction n with
        | zero => simp
        | succ n ih =>
          have hden : 0 < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
          have ha' : a / (2 : ℝ) ^ (n + 1) ≠ 0 := div_ne_zero ha hden.ne'
          have hb' : b / (2 : ℝ) ^ (n + 1) ≠ 0 := div_ne_zero hb hden.ne'
          have hqa := hdouble (a / (2 : ℝ) ^ (n + 1)) ha'
          have hqb := hdouble (b / (2 : ℝ) ^ (n + 1)) hb'
          rw [hscale a n] at hqa
          rw [hscale b n] at hqb
          have hs2 : s (a / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
              s (b / (2 : ℝ) ^ (n + 1)) ^ 2 := by
            simpa only [pow_two] using
              (mul_self_le_mul_self (hsnonneg (a / (2 : ℝ) ^ (n + 1)))
                (hsmono _ _ ha' hb'
                  (div_le_div_of_nonneg_right hab hden.le)))
          calc
            (2 : ℝ) ^ (n + 1) * (q a - q b) =
                2 * ((2 : ℝ) ^ n * (q a - q b)) := by
              rw [pow_succ]
              ring
            _ ≤ q (a / (2 : ℝ) ^ (n + 1)) -
                q (b / (2 : ℝ) ^ (n + 1)) := by
              nlinarith only [ih, hqa, hqb, hs2]
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
        (|a| + |b| + 1 / (q a - q b)) (show (1 : ℝ) < 2 by norm_num)
      have hp : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
      have hi : 0 < 1 / (q a - q b) := one_div_pos.mpr hd
      have haBound : |a| < (2 : ℝ) ^ n := by
        linarith only [hn, abs_nonneg b, hi]
      have hbBound : |b| < (2 : ℝ) ^ n := by
        linarith only [hn, abs_nonneg a, hi]
      have hdBound : 1 / (q a - q b) < (2 : ℝ) ^ n := by
        linarith only [hn, abs_nonneg a, abs_nonneg b]
      have hsmallA : |a / (2 : ℝ) ^ n| ≤ 1 := by
        rw [abs_div, abs_of_pos hp]
        exact (div_le_iff₀ hp).2 (by simpa only [one_mul] using haBound.le)
      have htop := hqsmall (a / (2 : ℝ) ^ n)
        (div_ne_zero ha hp.ne') hsmallA
      have hlo := hqnonneg (b / (2 : ℝ) ^ n)
      have hgt : 1 < (2 : ℝ) ^ n * (q a - q b) :=
        (div_lt_iff₀ hd).mp hdBound
      linarith only [hiter n, htop, hlo, hgt]
    let d : ℝ := (Real.exp (-r) + r - 1) / r ^ 2
    have hqd : q (-r) = d := by
      dsimp [q, d]
      rw [neg_sq]
      congr 1 <;> ring
    have hres (w : V) : 0 ≤ Real.exp (f w) - (f w + 1) - d * f w ^ 2 := by
      by_cases hw : f w = 0
      · simp [hw]
      · have h := hqmono (-r) (f w) (neg_ne_zero.mpr hr.ne') hw (hmin w)
        rw [hqd] at h
        dsimp [q] at h
        have hh := (le_div_iff₀ (sq_pos_of_ne_zero hw)).mp h
        linarith only [hh]
    have hsingle : Real.exp r - (r + 1) - d * r ^ 2 ≤
        ∑ w : V, (Real.exp (f w) - (f w + 1) - d * f w ^ 2) := by
      simpa only [hv] using
        (Finset.single_le_sum (fun w _ => hres w) (Finset.mem_univ v))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum, hsq, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, zero_add] at hsingle
    change Real.exp r + ((Fintype.card V : ℝ) - 1) - r +
      ((2 * (G.edgeFinset.card : ℝ) - r ^ 2) / r ^ 2) *
        (Real.exp (-r) + r - 1) ≤ ∑ w : V, Real.exp (f w)
    have hid : ((2 * (G.edgeFinset.card : ℝ) - r ^ 2) / r ^ 2) *
        (Real.exp (-r) + r - 1) = d * (2 * (G.edgeFinset.card : ℝ) - r ^ 2) := by
      dsimp [d]
      ring
    rw [hid]
    nlinarith only [hsingle]
