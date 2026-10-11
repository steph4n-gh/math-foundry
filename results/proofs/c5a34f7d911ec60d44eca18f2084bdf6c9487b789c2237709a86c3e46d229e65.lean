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

theorem model_380f64eac06a6c296479 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((((Fintype.card V : ℝ) / (2 : ℝ)) * ((Real.exp (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (Real.exp (-(Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))))))) + ((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) / (24 : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let n : ℝ := Fintype.card V
    let d : ℝ := 2 * (G.edgeFinset.card : ℝ) / n
    have hn : 0 < n := by
      dsimp only [n]
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    have hn0 : n ≠ 0 := ne_of_gt hn
    have hd : 0 ≤ d := by
      dsimp only [d]
      exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
    have hnd : n * d = 2 * (G.edgeFinset.card : ℝ) := by
      dsimp only [d]
      field_simp [hn0] <;> ring
    have hmean (z : V → ℝ) (hz : ∀ i, 0 ≤ z i) (k : ℕ) :
        n * ((∑ i : V, z i) / n) ^ k ≤ ∑ i : V, z i ^ k := by
      cases k with
      | zero => simp [n]
      | succ k =>
        have hp : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
        have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (k + 1)) := by
          simpa only [Real.rpow_natCast] using
            (convexOn_rpow (p := ((k + 1 : ℕ) : ℝ)) hp)
        have hw : (∑ _i : V, n⁻¹) = 1 := by
          simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
            (mul_inv_cancel₀ hn0)
        have h := hconv.map_sum_le
          (t := (Finset.univ : Finset V)) (w := fun _ : V => n⁻¹) (p := z)
          (fun _ _ => inv_nonneg.mpr hn.le) hw (fun i _ => hz i)
        simp only [smul_eq_mul, ← Finset.mul_sum] at h
        have havg : (∑ i : V, z i) / n = n⁻¹ * (∑ i : V, z i) := by
          rw [div_eq_mul_inv]
          exact mul_comm _ _
        calc
          n * ((∑ i : V, z i) / n) ^ (k + 1) =
              n * (n⁻¹ * (∑ i : V, z i)) ^ (k + 1) := by rw [havg]
          _ ≤ n * (n⁻¹ * (∑ i : V, z i ^ (k + 1))) :=
            mul_le_mul_of_nonneg_left h hn.le
          _ = ∑ i : V, z i ^ (k + 1) := by
            rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
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
    have hdeg : (∑ w : V, (G.degree w : ℝ)) = n * d := by
      rw [hnd]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hsecond : Matrix.trace (A ^ 2) = n * d := by
      calc
        Matrix.trace (A ^ 2) = ∑ w : V, (G.degree w : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply, A, pow_two,
            SimpleGraph.adjMatrix_mul_self_apply_self]
        _ = n * d := hdeg
    have havgEig : (∑ w : V, f w ^ 2) / n = d := by
      rw [← htrace 2, hsecond, mul_div_cancel_left₀ d hn0]
    have hmoment (k : ℕ) : n * d ^ k ≤ Matrix.trace (A ^ (2 * k)) := by
      have h := hmean (fun w => f w ^ 2) (fun w => sq_nonneg (f w)) k
      rw [havgEig] at h
      rw [htrace (2 * k)]
      simpa only [pow_mul] using h
    have havgDeg : (∑ w : V, (G.degree w : ℝ)) / n = d := by
      rw [hdeg, mul_div_cancel_left₀ d hn0]
    have hdeg2 : n * d ^ 2 ≤ ∑ w : V, (G.degree w : ℝ) ^ 2 := by
      have h := hmean (fun w => (G.degree w : ℝ))
        (fun w => Nat.cast_nonneg (G.degree w)) 2
      simpa only [havgDeg] using h
    let B : Matrix V V ℝ := A ^ 2
    have hAs : A.IsSymm := by
      dsimp only [A]
      exact G.isSymm_adjMatrix (α := ℝ)
    have hBs : B.IsSymm := by
      dsimp [B, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 2
    have hBdiag (i : V) : B i i = (G.degree i : ℝ) := by
      simpa only [B, A, pow_two] using
        (G.adjMatrix_mul_self_apply_self (α := ℝ) i)
    have hBsq (i j : V) : B i j ≤ B i j ^ 2 := by
      change (G.adjMatrix ℝ ^ 2) i j ≤ ((G.adjMatrix ℝ ^ 2) i j) ^ 2
      rw [G.adjMatrix_pow_apply_eq_card_walk 2 i j, pow_two]
      exact_mod_cast
        (Nat.le_mul_self (Fintype.card {p : G.Walk i j | p.length = 2}))
    have hrowA (i : V) : (∑ j : V, A i j) = (G.degree i : ℝ) := by
      have h := SimpleGraph.adjMatrix_mulVec_const_apply
        (G := G) (a := (1 : ℝ)) (v := i)
      change (∑ j : V, G.adjMatrix ℝ i j * 1) = (G.degree i : ℝ) * 1 at h
      simpa only [A, mul_one] using h
    have hcolA (j : V) : (∑ i : V, A i j) = (G.degree j : ℝ) := by
      calc
        (∑ i : V, A i j) = ∑ i : V, A j i :=
          Finset.sum_congr rfl (fun i _ => hAs.apply j i)
        _ = (G.degree j : ℝ) := hrowA j
    have hBrow (i : V) :
        (∑ j : V, B i j) = ∑ w : V, A i w * (G.degree w : ℝ) := by
      calc
        (∑ j : V, B i j) = ∑ j : V, ∑ w : V, A i w * A w j := by
          simp only [B, pow_two, Matrix.mul_apply]
        _ = ∑ w : V, ∑ j : V, A i w * A w j := Finset.sum_comm
        _ = ∑ w : V, A i w * (G.degree w : ℝ) := by
          simp only [← Finset.mul_sum, hrowA]
    have hBsum : (∑ i : V, ∑ j : V, B i j) =
        ∑ w : V, (G.degree w : ℝ) ^ 2 := by
      calc
        (∑ i : V, ∑ j : V, B i j) =
            ∑ i : V, ∑ w : V, A i w * (G.degree w : ℝ) := by
          simp_rw [hBrow]
        _ = ∑ w : V, ∑ i : V, A i w * (G.degree w : ℝ) := Finset.sum_comm
        _ = ∑ w : V, (G.degree w : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [← Finset.sum_mul, hcolA, pow_two]
    have hfourRows : Matrix.trace (A ^ 4) = ∑ i : V, ∑ j : V, B i j ^ 2 := by
      have hp : A ^ 4 = B * B := by
        change A ^ 4 = A ^ 2 * A ^ 2
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, B i j * B j i) = ∑ j : V, B i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBs.apply i j, pow_two]
    have hrow (i : V) :
        (G.degree i : ℝ) ^ 2 + (∑ j : V, B i j) - (G.degree i : ℝ) ≤
          ∑ j : V, B i j ^ 2 := by
      have hsingle : B i i ^ 2 - B i i ≤
          ∑ j : V, (B i j ^ 2 - B i j) :=
        Finset.single_le_sum
          (fun j _ => sub_nonneg.mpr (hBsq i j)) (Finset.mem_univ i)
      rw [hBdiag i] at hsingle
      simp only [Finset.sum_sub_distrib] at hsingle
      linarith only [hsingle]
    have hrows :
        (∑ i : V, ((G.degree i : ℝ) ^ 2 +
          (∑ j : V, B i j) - (G.degree i : ℝ))) ≤
          ∑ i : V, ∑ j : V, B i j ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrow i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hrows
    rw [hBsum, ← hfourRows, hdeg] at hrows
    have hfourth : n * (2 * d ^ 2 - d) ≤ Matrix.trace (A ^ 4) := by
      nlinarith only [hrows, hdeg2]
    let a : ℝ := Real.sqrt d
    have ha2 : a ^ 2 = d := by
      simpa only [a] using Real.sq_sqrt hd
    have hcoef (k : ℕ) :
        n / 2 * (a ^ k + (-a) ^ k) ≤ Matrix.trace (A ^ k) := by
      obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
      · subst k
        calc
          n / 2 * (a ^ (2 * r) + (-a) ^ (2 * r)) = n * d ^ r := by
            simp only [pow_mul, neg_sq, ha2]
            ring
          _ ≤ Matrix.trace (A ^ (2 * r)) := hmoment r
      · subst k
        have hz : a ^ (2 * r + 1) + (-a) ^ (2 * r + 1) = 0 := by
          simp only [pow_succ, pow_mul, neg_sq]
          ring
        rw [hz, mul_zero]
        exact hnonneg (2 * r + 1)
    let q : ℕ → ℝ := fun k =>
      (Matrix.trace (A ^ k) - n / 2 * (a ^ k + (-a) ^ k)) /
        (Nat.factorial k : ℝ)
    have hq (k : ℕ) : 0 ≤ q k :=
      div_nonneg (sub_nonneg.mpr (hcoef k)) (Nat.cast_nonneg _)
    have hq4 : n * d * (d - 1) / 24 ≤ q 4 := by
      have hc4 : n / 2 * (a ^ 4 + (-a) ^ 4) = n * d ^ 2 := by
        calc
          n / 2 * (a ^ 4 + (-a) ^ 4) =
              n / 2 * ((a ^ 2) ^ 2 + ((-a) ^ 2) ^ 2) := by ring
          _ = n * d ^ 2 := by
            simp only [neg_sq, ha2]
            ring
      have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num
      dsimp only [q]
      rw [hfac, hc4]
      nlinarith only [hfourth]
    let c : ℝ → CauSeq ℝ abs := fun x =>
      Complex.cauSeqRe (Complex.exp' (x : ℂ))
    have hc (x : ℝ) (N : ℕ) :
        c x N = ∑ k ∈ Finset.range N, x ^ k / (Nat.factorial k : ℝ) := by
      change (∑ k ∈ Finset.range N,
        (x : ℂ) ^ k / (Nat.factorial k : ℂ)).re = _
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    have hclim (x : ℝ) : CauSeq.lim (c x) = Real.exp x := by
      change CauSeq.lim (Complex.cauSeqRe (Complex.exp' (x : ℂ))) = _
      rw [Complex.lim_re, Real.exp, Complex.exp]
    have happly (s : Finset V) (N : ℕ) :
        (∑ w ∈ s, c (f w)) N = ∑ w ∈ s, c (f w) N := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hws ih =>
        simp only [Finset.sum_insert hws, CauSeq.add_apply, ih]
    have hlim (s : Finset V) :
        CauSeq.lim (∑ w ∈ s, c (f w)) = ∑ w ∈ s, CauSeq.lim (c (f w)) := by
      induction s using Finset.induction_on with
      | empty => simpa using (CauSeq.lim_const (abv := abs) (0 : ℝ))
      | @insert w s hws ih =>
        rw [Finset.sum_insert hws, Finset.sum_insert hws, ← CauSeq.lim_add, ih]
    have hlimsum : CauSeq.lim (∑ w : V, c (f w)) =
        ∑ w : V, Real.exp (f w) := by
      rw [hlim]
      exact Finset.sum_congr rfl (fun w _ => hclim (f w))
    let b : CauSeq ℝ abs := CauSeq.const abs (n / 2) * (c a + c (-a))
    have hlimb : CauSeq.lim b = n / 2 * (Real.exp a + Real.exp (-a)) := by
      dsimp only [b]
      simp only [← CauSeq.lim_mul_lim, CauSeq.lim_const, ← CauSeq.lim_add, hclim]
    have hpartial (N : ℕ) :
        (∑ w : V, c (f w)) N =
          ∑ k ∈ Finset.range N, Matrix.trace (A ^ k) / (Nat.factorial k : ℝ) := by
      rw [happly]
      simp_rw [hc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_div, htrace]
    have hbpartial (N : ℕ) :
        b N = ∑ k ∈ Finset.range N,
          (n / 2 * (a ^ k + (-a) ^ k)) / (Nat.factorial k : ℝ) := by
      dsimp only [b]
      rw [CauSeq.mul_apply, CauSeq.const_apply, CauSeq.add_apply, hc, hc]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hdiff (N : ℕ) :
        ((∑ w : V, c (f w)) - b) N = ∑ k ∈ Finset.range N, q k := by
      rw [CauSeq.sub_apply, hpartial, hbpartial, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [q]
      ring
    have hlimdiff : CauSeq.lim ((∑ w : V, c (f w)) - b) =
        (∑ w : V, Real.exp (f w)) - n / 2 * (Real.exp a + Real.exp (-a)) := by
      rw [← CauSeq.lim_sub, hlimsum, hlimb]
    have hlow : n * d * (d - 1) / 24 ≤
        CauSeq.lim ((∑ w : V, c (f w)) - b) := by
      apply CauSeq.le_lim
      apply CauSeq.le_of_exists
      refine ⟨5, fun N hN => ?_⟩
      rw [CauSeq.const_apply, hdiff]
      exact le_trans hq4 (Finset.single_le_sum (fun k _ => hq k) (by
        simp only [Finset.mem_range]
        omega))
    rw [hlimdiff] at hlow
    simp only [if_neg hV]
    change n / 2 * (Real.exp a + Real.exp (-a)) +
      n * d * (d - 1) / 24 ≤ ∑ w : V, Real.exp (f w)
    linarith only [hlow]

theorem estrada_index_quadratic_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((Fintype.card V : ℝ) + (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ^ 2) / (2 : ℝ))) := by
  classical
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  have hsum : (∑ v : V, f v) = 0 := by
    simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hle (w : V) : f w ≤ f v := by
      rw [hv]
      exact le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self w)
    have hnonneg : 0 ≤ f v := by
      by_contra hneg
      have hlt : (∑ w : V, f w) < 0 :=
        Finset.sum_neg
          (fun w _ => lt_of_le_of_lt (hle w) (lt_of_not_ge hneg))
          Finset.univ_nonempty
      linarith
    have hres (w : V) : 0 ≤ Real.exp (f w) - (f w + 1) :=
      sub_nonneg.mpr (Real.add_one_le_exp (f w))
    have hsingle : Real.exp (f v) - (f v + 1) ≤
        ∑ w : V, (Real.exp (f w) - (f w + 1)) :=
      Finset.single_le_sum (fun w _ => hres w) (Finset.mem_univ v)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_add] at hsingle
    change (Fintype.card V : ℝ) +
      (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) ^ 2 / 2 ≤
        ∑ w : V, Real.exp (f w)
    rw [if_neg hV, ← hv]
    linarith [Real.quadratic_le_exp_of_nonneg hnonneg]

theorem model_236269be9669ccb9e88c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((Fintype.card V : ℝ) + (((G.maxDegree : ℝ) ^ 2) / (6 : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have he : G.edgeFinset.card = 0 := by
      apply Nat.le_zero.mp
      simpa [hV] using G.card_edgeFinset_le_card_choose_two
    simp [hV, he]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
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
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    let S : Finset V := G.neighborFinset v
    let B : Matrix V V ℝ := A ^ 2
    let R : V → ℝ := fun i => ∑ j : V, B i j ^ 2
    have hvS : v ∉ S := by simp [S]
    have hAnn (i j : V) : 0 ≤ A i j := by
      dsimp [A, SimpleGraph.adjMatrix]
      split_ifs <;> norm_num
    have hBs : B.IsSymm := by
      dsimp [B, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 2
    have hBdiag : B v v = (G.degree v : ℝ) := by
      simpa only [B, A, pow_two] using
        (G.adjMatrix_mul_self_apply_self (α := ℝ) v)
    have hBneighbors (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
        1 ≤ B i j := by
      have hvi : G.Adj v i := (G.mem_neighborFinset v i).mp hi
      have hvj : G.Adj v j := (G.mem_neighborFinset v j).mp hj
      calc
        (1 : ℝ) = A i v * A v j := by simp [A, hvi.symm, hvj]
        _ ≤ ∑ w : V, A i w * A w j :=
          Finset.single_le_sum
            (fun w _ => mul_nonneg (hAnn i w) (hAnn w j))
            (Finset.mem_univ v)
        _ = B i j := by simp only [B, pow_two, Matrix.mul_apply]
    have hRnn (i : V) : 0 ≤ R i :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (B i j))
    have hRv : (G.degree v : ℝ) ^ 2 ≤ R v := by
      calc
        (G.degree v : ℝ) ^ 2 = B v v ^ 2 := by rw [hBdiag]
        _ ≤ R v := Finset.single_le_sum
          (fun j _ => sq_nonneg (B v j)) (Finset.mem_univ v)
    have hRi (i : V) (hi : i ∈ S) : (G.degree v : ℝ) ≤ R i := by
      calc
        (G.degree v : ℝ) = ∑ j ∈ S, (1 : ℝ) := by simp [S]
        _ ≤ ∑ j ∈ S, B i j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have h := hBneighbors i j hi hj
          nlinarith [sq_nonneg (B i j - 1)]
        _ ≤ ∑ j : V, B i j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun j _ _ => sq_nonneg (B i j))
        _ = R i := rfl
    have hRN : (G.degree v : ℝ) ^ 2 ≤ ∑ i ∈ S, R i := by
      calc
        (G.degree v : ℝ) ^ 2 = ∑ i ∈ S, (G.degree v : ℝ) := by
          simp [S, pow_two, nsmul_eq_mul]
        _ ≤ ∑ i ∈ S, R i := Finset.sum_le_sum (fun i hi => hRi i hi)
    have hfourRows : Matrix.trace (A ^ 4) = ∑ i : V, R i := by
      have hp : A ^ 4 = B * B := by
        change A ^ 4 = A ^ 2 * A ^ 2
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, B i j * B j i) = ∑ j : V, B i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBs.apply i j, pow_two]
    have hRows : R v + (∑ i ∈ S, R i) ≤ Matrix.trace (A ^ 4) := by
      calc
        R v + (∑ i ∈ S, R i) = ∑ i ∈ insert v S, R i :=
          (Finset.sum_insert hvS).symm
        _ ≤ ∑ i : V, R i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ (insert v S))
            (fun i _ _ => hRnn i)
        _ = Matrix.trace (A ^ 4) := hfourRows.symm
    have hfourth : 2 * (G.maxDegree : ℝ) ^ 2 ≤ Matrix.trace (A ^ 4) := by
      rw [hv]
      nlinarith only [hRv, hRN, hRows]
    let C : Matrix V V ℝ := A ^ 3
    let T : V → ℝ := fun i => ∑ j : V, C i j ^ 2
    have hCs : C.IsSymm := by
      dsimp [C, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 3
    have hBnn (i j : V) : 0 ≤ B i j := by
      change 0 ≤ (G.adjMatrix ℝ ^ 2) i j
      rw [G.adjMatrix_pow_apply_eq_card_walk 2 i j]
      exact Nat.cast_nonneg _
    have hCneighbors (i : V) (hi : i ∈ S) :
        (G.degree v : ℝ) ≤ C v i := by
      have hvi : G.Adj v i := (G.mem_neighborFinset v i).mp hi
      calc
        (G.degree v : ℝ) = B v v * A v i := by
          rw [hBdiag]
          simp [A, hvi]
        _ ≤ ∑ w : V, B v w * A w i :=
          Finset.single_le_sum
            (fun w _ => mul_nonneg (hBnn v w) (hAnn w i))
            (Finset.mem_univ v)
        _ = C v i := by
          change (A ^ 2 * A) v i = (A ^ 3) v i
          rw [← pow_succ]
    have hCneighborsSq (i : V) (hi : i ∈ S) :
        (G.degree v : ℝ) ^ 2 ≤ C v i ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hCneighbors i hi) 2
    have hTnn (i : V) : 0 ≤ T i :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (C i j))
    have hTv : (G.degree v : ℝ) ^ 3 ≤ T v := by
      calc
        (G.degree v : ℝ) ^ 3 = ∑ i ∈ S, (G.degree v : ℝ) ^ 2 := by
          simp [S, pow_succ, nsmul_eq_mul] <;> ring
        _ ≤ ∑ i ∈ S, C v i ^ 2 :=
          Finset.sum_le_sum (fun i hi => hCneighborsSq i hi)
        _ ≤ ∑ i : V, C v i ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun i _ _ => sq_nonneg (C v i))
        _ = T v := rfl
    have hTi (i : V) (hi : i ∈ S) : (G.degree v : ℝ) ^ 2 ≤ T i := by
      calc
        (G.degree v : ℝ) ^ 2 ≤ C v i ^ 2 := hCneighborsSq i hi
        _ = C i v ^ 2 := by rw [hCs.apply i v]
        _ ≤ T i := Finset.single_le_sum
          (fun j _ => sq_nonneg (C i j)) (Finset.mem_univ v)
    have hTN : (G.degree v : ℝ) ^ 3 ≤ ∑ i ∈ S, T i := by
      calc
        (G.degree v : ℝ) ^ 3 = ∑ i ∈ S, (G.degree v : ℝ) ^ 2 := by
          simp [S, pow_succ, nsmul_eq_mul] <;> ring
        _ ≤ ∑ i ∈ S, T i := Finset.sum_le_sum (fun i hi => hTi i hi)
    have hsixRows : Matrix.trace (A ^ 6) = ∑ i : V, T i := by
      have hp : A ^ 6 = C * C := by
        change A ^ 6 = A ^ 3 * A ^ 3
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, C i j * C j i) = ∑ j : V, C i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hCs.apply i j, pow_two]
    have hTRows : T v + (∑ i ∈ S, T i) ≤ Matrix.trace (A ^ 6) := by
      calc
        T v + (∑ i ∈ S, T i) = ∑ i ∈ insert v S, T i :=
          (Finset.sum_insert hvS).symm
        _ ≤ ∑ i : V, T i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ (insert v S))
            (fun i _ _ => hTnn i)
        _ = Matrix.trace (A ^ 6) := hsixRows.symm
    have hsixth : 2 * (G.maxDegree : ℝ) ^ 3 ≤ Matrix.trace (A ^ 6) := by
      rw [hv]
      nlinarith only [hTv, hTN, hTRows]
    have hmaxedges : (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      rw [hv]
      exact_mod_cast G.degree_le_card_edgeFinset v
    have hpoly : (G.maxDegree : ℝ) ^ 2 / 6 ≤
        (G.maxDegree : ℝ) + (G.maxDegree : ℝ) ^ 2 / 12 +
          (G.maxDegree : ℝ) ^ 3 / 360 := by
      have hd : (0 : ℝ) ≤ (G.maxDegree : ℝ) := Nat.cast_nonneg _
      have hp : 0 ≤ (G.maxDegree : ℝ) * ((G.maxDegree : ℝ) - 15) ^ 2 :=
        mul_nonneg hd (sq_nonneg _)
      nlinarith only [hd, hp]
    let c : V → CauSeq ℝ abs := fun w =>
      Complex.cauSeqRe (Complex.exp' (f w : ℂ))
    have hc (w : V) (n : ℕ) :
        c w n = ∑ k ∈ Finset.range n, f w ^ k / (Nat.factorial k : ℝ) := by
      change (∑ k ∈ Finset.range n,
        (f w : ℂ) ^ k / (Nat.factorial k : ℂ)).re = _
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    have hclim (w : V) : CauSeq.lim (c w) = Real.exp (f w) := by
      change CauSeq.lim (Complex.cauSeqRe (Complex.exp' (f w : ℂ))) = _
      rw [Complex.lim_re, Real.exp, Complex.exp]
    have happly (s : Finset V) (n : ℕ) :
        (∑ w ∈ s, c w) n = ∑ w ∈ s, c w n := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hws ih =>
        simp only [Finset.sum_insert hws, CauSeq.add_apply, ih]
    have hlim (s : Finset V) :
        CauSeq.lim (∑ w ∈ s, c w) = ∑ w ∈ s, CauSeq.lim (c w) := by
      induction s using Finset.induction_on with
      | empty => simpa using (CauSeq.lim_const (abv := abs) (0 : ℝ))
      | @insert w s hws ih =>
        rw [Finset.sum_insert hws, Finset.sum_insert hws, ← CauSeq.lim_add, ih]
    have hlimsum : CauSeq.lim (∑ w : V, c w) = ∑ w : V, Real.exp (f w) := by
      rw [hlim]
      exact Finset.sum_congr rfl (fun w _ => hclim w)
    let t : ℕ → ℝ := fun k => Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
    have ht (k : ℕ) : 0 ≤ t k :=
      div_nonneg (hnonneg k) (Nat.cast_nonneg _)
    have hpartial (n : ℕ) :
        (∑ w : V, c w) n = ∑ k ∈ Finset.range n, t k := by
      rw [happly]
      simp_rw [hc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      change (∑ w : V, f w ^ k / (Nat.factorial k : ℝ)) =
        Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
      rw [← Finset.sum_div, htrace]
    have hlow : (∑ k ∈ Finset.range 7, t k) ≤ CauSeq.lim (∑ w : V, c w) := by
      apply CauSeq.le_lim
      apply CauSeq.le_of_exists
      refine ⟨7, fun n hn => ?_⟩
      rw [CauSeq.const_apply, hpartial]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun k _ _ => ht k)
    have ht0 : t 0 = (Fintype.card V : ℝ) := by simp [t]
    have ht1 : t 1 = 0 := by simp [t, A]
    have ht2 : t 2 = (G.edgeFinset.card : ℝ) := by
      norm_num [t, hsecond] <;> ring
    have ht4 : t 4 = Matrix.trace (A ^ 4) / 24 := by norm_num [t]
    have ht6 : t 6 = Matrix.trace (A ^ 6) / 720 := by norm_num [t]
    have hseven : (∑ k ∈ Finset.range 7, t k) =
        t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hseven, ht0, ht1, ht2, ht4, ht6, hlimsum] at hlow
    change (Fintype.card V : ℝ) + (G.maxDegree : ℝ) ^ 2 / 6 ≤
      ∑ w : V, Real.exp (f w)
    nlinarith only [hlow, hfourth, hsixth, hmaxedges, hpoly, ht 3, ht 5]

theorem model_97775ef52738c74004cd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) + (((G.maxDegree : ℝ) ^ 2) / (12 : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have he : G.edgeFinset.card = 0 := by
      apply Nat.le_zero.mp
      simpa [hV] using G.card_edgeFinset_le_card_choose_two
    simp [hV, he]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
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
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    let S : Finset V := G.neighborFinset v
    let B : Matrix V V ℝ := A ^ 2
    let R : V → ℝ := fun i => ∑ j : V, B i j ^ 2
    have hvS : v ∉ S := by simp [S]
    have hAnn (i j : V) : 0 ≤ A i j := by
      dsimp [A, SimpleGraph.adjMatrix]
      split_ifs <;> norm_num
    have hBs : B.IsSymm := by
      dsimp [B, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 2
    have hBdiag : B v v = (G.degree v : ℝ) := by
      simpa only [B, A, pow_two] using
        (G.adjMatrix_mul_self_apply_self (α := ℝ) v)
    have hBneighbors (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
        1 ≤ B i j := by
      have hvi : G.Adj v i := (G.mem_neighborFinset v i).mp hi
      have hvj : G.Adj v j := (G.mem_neighborFinset v j).mp hj
      calc
        (1 : ℝ) = A i v * A v j := by simp [A, hvi.symm, hvj]
        _ ≤ ∑ w : V, A i w * A w j :=
          Finset.single_le_sum
            (fun w _ => mul_nonneg (hAnn i w) (hAnn w j))
            (Finset.mem_univ v)
        _ = B i j := by simp only [B, pow_two, Matrix.mul_apply]
    have hRnn (i : V) : 0 ≤ R i :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (B i j))
    have hRv : (G.degree v : ℝ) ^ 2 ≤ R v := by
      calc
        (G.degree v : ℝ) ^ 2 = B v v ^ 2 := by rw [hBdiag]
        _ ≤ R v := Finset.single_le_sum
          (fun j _ => sq_nonneg (B v j)) (Finset.mem_univ v)
    have hRi (i : V) (hi : i ∈ S) : (G.degree v : ℝ) ≤ R i := by
      calc
        (G.degree v : ℝ) = ∑ j ∈ S, (1 : ℝ) := by simp [S]
        _ ≤ ∑ j ∈ S, B i j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have h := hBneighbors i j hi hj
          nlinarith [sq_nonneg (B i j - 1)]
        _ ≤ ∑ j : V, B i j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun j _ _ => sq_nonneg (B i j))
        _ = R i := rfl
    have hRN : (G.degree v : ℝ) ^ 2 ≤ ∑ i ∈ S, R i := by
      calc
        (G.degree v : ℝ) ^ 2 = ∑ i ∈ S, (G.degree v : ℝ) := by
          simp [S, pow_two, nsmul_eq_mul]
        _ ≤ ∑ i ∈ S, R i := Finset.sum_le_sum (fun i hi => hRi i hi)
    have hfourRows : Matrix.trace (A ^ 4) = ∑ i : V, R i := by
      have hp : A ^ 4 = B * B := by
        change A ^ 4 = A ^ 2 * A ^ 2
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, B i j * B j i) = ∑ j : V, B i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBs.apply i j, pow_two]
    have hRows : R v + (∑ i ∈ S, R i) ≤ Matrix.trace (A ^ 4) := by
      calc
        R v + (∑ i ∈ S, R i) = ∑ i ∈ insert v S, R i :=
          (Finset.sum_insert hvS).symm
        _ ≤ ∑ i : V, R i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ (insert v S))
            (fun i _ _ => hRnn i)
        _ = Matrix.trace (A ^ 4) := hfourRows.symm
    have hfourth : 2 * (G.maxDegree : ℝ) ^ 2 ≤ Matrix.trace (A ^ 4) := by
      rw [hv]
      nlinarith only [hRv, hRN, hRows]
    let c : V → CauSeq ℝ abs := fun w =>
      Complex.cauSeqRe (Complex.exp' (f w : ℂ))
    have hc (w : V) (n : ℕ) :
        c w n = ∑ k ∈ Finset.range n, f w ^ k / (Nat.factorial k : ℝ) := by
      change (∑ k ∈ Finset.range n,
        (f w : ℂ) ^ k / (Nat.factorial k : ℂ)).re = _
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    have hclim (w : V) : CauSeq.lim (c w) = Real.exp (f w) := by
      change CauSeq.lim (Complex.cauSeqRe (Complex.exp' (f w : ℂ))) = _
      rw [Complex.lim_re, Real.exp, Complex.exp]
    have happly (s : Finset V) (n : ℕ) :
        (∑ w ∈ s, c w) n = ∑ w ∈ s, c w n := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hws ih =>
        simp only [Finset.sum_insert hws, CauSeq.add_apply, ih]
    have hlim (s : Finset V) :
        CauSeq.lim (∑ w ∈ s, c w) = ∑ w ∈ s, CauSeq.lim (c w) := by
      induction s using Finset.induction_on with
      | empty => simpa using (CauSeq.lim_const (abv := abs) (0 : ℝ))
      | @insert w s hws ih =>
        rw [Finset.sum_insert hws, Finset.sum_insert hws, ← CauSeq.lim_add, ih]
    have hlimsum : CauSeq.lim (∑ w : V, c w) = ∑ w : V, Real.exp (f w) := by
      rw [hlim]
      exact Finset.sum_congr rfl (fun w _ => hclim w)
    let t : ℕ → ℝ := fun k => Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
    have ht (k : ℕ) : 0 ≤ t k :=
      div_nonneg (hnonneg k) (Nat.cast_nonneg _)
    have hpartial (n : ℕ) :
        (∑ w : V, c w) n = ∑ k ∈ Finset.range n, t k := by
      rw [happly]
      simp_rw [hc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      change (∑ w : V, f w ^ k / (Nat.factorial k : ℝ)) =
        Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
      rw [← Finset.sum_div, htrace]
    have hlow : (∑ k ∈ Finset.range 5, t k) ≤ CauSeq.lim (∑ w : V, c w) := by
      apply CauSeq.le_lim
      apply CauSeq.le_of_exists
      refine ⟨5, fun n hn => ?_⟩
      rw [CauSeq.const_apply, hpartial]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun k _ _ => ht k)
    have ht0 : t 0 = (Fintype.card V : ℝ) := by simp [t]
    have ht1 : t 1 = 0 := by simp [t, A]
    have ht2 : t 2 = (G.edgeFinset.card : ℝ) := by
      norm_num [t, hsecond] <;> ring
    have ht4 : t 4 = Matrix.trace (A ^ 4) / 24 := by norm_num [t]
    have hfive : (∑ k ∈ Finset.range 5, t k) =
        t 0 + t 1 + t 2 + t 3 + t 4 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hfive, ht0, ht1, ht2, ht4, hlimsum] at hlow
    change (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) +
      (G.maxDegree : ℝ) ^ 2 / 12 ≤ ∑ w : V, Real.exp (f w)
    nlinarith only [hlow, hfourth, ht 3]

theorem model_a256bd085bb7ac490e7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) + ((((G.maxDegree : ℝ) ^ 2) / (12 : ℝ)) + (((G.maxDegree : ℝ) ^ 3) / (360 : ℝ)))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have he : G.edgeFinset.card = 0 := by
      apply Nat.le_zero.mp
      simpa [hV] using G.card_edgeFinset_le_card_choose_two
    simp [hV, he]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
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
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    let S : Finset V := G.neighborFinset v
    let B : Matrix V V ℝ := A ^ 2
    let R : V → ℝ := fun i => ∑ j : V, B i j ^ 2
    have hvS : v ∉ S := by simp [S]
    have hAnn (i j : V) : 0 ≤ A i j := by
      dsimp [A, SimpleGraph.adjMatrix]
      split_ifs <;> norm_num
    have hBs : B.IsSymm := by
      dsimp [B, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 2
    have hBdiag : B v v = (G.degree v : ℝ) := by
      simpa only [B, A, pow_two] using
        (G.adjMatrix_mul_self_apply_self (α := ℝ) v)
    have hBneighbors (i j : V) (hi : i ∈ S) (hj : j ∈ S) :
        1 ≤ B i j := by
      have hvi : G.Adj v i := (G.mem_neighborFinset v i).mp hi
      have hvj : G.Adj v j := (G.mem_neighborFinset v j).mp hj
      calc
        (1 : ℝ) = A i v * A v j := by simp [A, hvi.symm, hvj]
        _ ≤ ∑ w : V, A i w * A w j :=
          Finset.single_le_sum
            (fun w _ => mul_nonneg (hAnn i w) (hAnn w j))
            (Finset.mem_univ v)
        _ = B i j := by simp only [B, pow_two, Matrix.mul_apply]
    have hRnn (i : V) : 0 ≤ R i :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (B i j))
    have hRv : (G.degree v : ℝ) ^ 2 ≤ R v := by
      calc
        (G.degree v : ℝ) ^ 2 = B v v ^ 2 := by rw [hBdiag]
        _ ≤ R v := Finset.single_le_sum
          (fun j _ => sq_nonneg (B v j)) (Finset.mem_univ v)
    have hRi (i : V) (hi : i ∈ S) : (G.degree v : ℝ) ≤ R i := by
      calc
        (G.degree v : ℝ) = ∑ j ∈ S, (1 : ℝ) := by simp [S]
        _ ≤ ∑ j ∈ S, B i j ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have h := hBneighbors i j hi hj
          nlinarith [sq_nonneg (B i j - 1)]
        _ ≤ ∑ j : V, B i j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun j _ _ => sq_nonneg (B i j))
        _ = R i := rfl
    have hRN : (G.degree v : ℝ) ^ 2 ≤ ∑ i ∈ S, R i := by
      calc
        (G.degree v : ℝ) ^ 2 = ∑ i ∈ S, (G.degree v : ℝ) := by
          simp [S, pow_two, nsmul_eq_mul]
        _ ≤ ∑ i ∈ S, R i := Finset.sum_le_sum (fun i hi => hRi i hi)
    have hfourRows : Matrix.trace (A ^ 4) = ∑ i : V, R i := by
      have hp : A ^ 4 = B * B := by
        change A ^ 4 = A ^ 2 * A ^ 2
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, B i j * B j i) = ∑ j : V, B i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hBs.apply i j, pow_two]
    have hRows : R v + (∑ i ∈ S, R i) ≤ Matrix.trace (A ^ 4) := by
      calc
        R v + (∑ i ∈ S, R i) = ∑ i ∈ insert v S, R i :=
          (Finset.sum_insert hvS).symm
        _ ≤ ∑ i : V, R i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ (insert v S))
            (fun i _ _ => hRnn i)
        _ = Matrix.trace (A ^ 4) := hfourRows.symm
    have hfourth : 2 * (G.maxDegree : ℝ) ^ 2 ≤ Matrix.trace (A ^ 4) := by
      rw [hv]
      nlinarith only [hRv, hRN, hRows]
    let C : Matrix V V ℝ := A ^ 3
    let T : V → ℝ := fun i => ∑ j : V, C i j ^ 2
    have hCmul : C = A * B := by
      change A ^ (2 + 1) = A * A ^ 2
      rw [pow_succ']
    have hCs : C.IsSymm := by
      dsimp [C, A]
      exact (G.isSymm_adjMatrix (α := ℝ)).pow 3
    have hCneighbors (j : V) (hj : j ∈ S) :
        (G.degree v : ℝ) ≤ C v j := by
      calc
        (G.degree v : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp [S]
        _ ≤ ∑ i ∈ S, B i j :=
          Finset.sum_le_sum (fun i hi => hBneighbors i j hi hj)
        _ = C v j := by
          rw [hCmul]
          simpa only [A, S] using (G.adjMatrix_mul_apply B v j).symm
    have hCsq (j : V) (hj : j ∈ S) :
        (G.degree v : ℝ) ^ 2 ≤ C v j ^ 2 := by
      simpa only [pow_two] using
        mul_self_le_mul_self
          (show (0 : ℝ) ≤ (G.degree v : ℝ) from Nat.cast_nonneg _)
          (hCneighbors j hj)
    have hcubeSum : (G.degree v : ℝ) ^ 3 =
        ∑ i ∈ S, (G.degree v : ℝ) ^ 2 := by
      calc
        (G.degree v : ℝ) ^ 3 =
            (G.degree v : ℝ) * (G.degree v : ℝ) ^ 2 := by ring
        _ = ∑ i ∈ S, (G.degree v : ℝ) ^ 2 := by
          simp [S, nsmul_eq_mul]
    have hTnn (i : V) : 0 ≤ T i :=
      Finset.sum_nonneg (fun j _ => sq_nonneg (C i j))
    have hTv : (G.degree v : ℝ) ^ 3 ≤ T v := by
      calc
        (G.degree v : ℝ) ^ 3 = ∑ j ∈ S, (G.degree v : ℝ) ^ 2 := hcubeSum
        _ ≤ ∑ j ∈ S, C v j ^ 2 :=
          Finset.sum_le_sum (fun j hj => hCsq j hj)
        _ ≤ ∑ j : V, C v j ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            (fun j _ _ => sq_nonneg (C v j))
        _ = T v := rfl
    have hTi (i : V) (hi : i ∈ S) : (G.degree v : ℝ) ^ 2 ≤ T i := by
      calc
        (G.degree v : ℝ) ^ 2 ≤ C v i ^ 2 := hCsq i hi
        _ = C i v ^ 2 := by rw [hCs.apply v i]
        _ ≤ T i := Finset.single_le_sum
          (fun j _ => sq_nonneg (C i j)) (Finset.mem_univ v)
    have hTN : (G.degree v : ℝ) ^ 3 ≤ ∑ i ∈ S, T i := by
      calc
        (G.degree v : ℝ) ^ 3 = ∑ i ∈ S, (G.degree v : ℝ) ^ 2 := hcubeSum
        _ ≤ ∑ i ∈ S, T i := Finset.sum_le_sum (fun i hi => hTi i hi)
    have hsixRows : Matrix.trace (A ^ 6) = ∑ i : V, T i := by
      have hp : A ^ 6 = C * C := by
        change A ^ 6 = A ^ 3 * A ^ 3
        rw [← pow_add]
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, C i j * C j i) = ∑ j : V, C i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hCs.apply i j, pow_two]
    have hTRows : T v + (∑ i ∈ S, T i) ≤ Matrix.trace (A ^ 6) := by
      calc
        T v + (∑ i ∈ S, T i) = ∑ i ∈ insert v S, T i :=
          (Finset.sum_insert hvS).symm
        _ ≤ ∑ i : V, T i :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ (insert v S))
            (fun i _ _ => hTnn i)
        _ = Matrix.trace (A ^ 6) := hsixRows.symm
    have hsixth : 2 * (G.maxDegree : ℝ) ^ 3 ≤ Matrix.trace (A ^ 6) := by
      rw [hv]
      nlinarith only [hTv, hTN, hTRows]
    let c : V → CauSeq ℝ abs := fun w =>
      Complex.cauSeqRe (Complex.exp' (f w : ℂ))
    have hc (w : V) (n : ℕ) :
        c w n = ∑ k ∈ Finset.range n, f w ^ k / (Nat.factorial k : ℝ) := by
      change (∑ k ∈ Finset.range n,
        (f w : ℂ) ^ k / (Nat.factorial k : ℂ)).re = _
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    have hclim (w : V) : CauSeq.lim (c w) = Real.exp (f w) := by
      change CauSeq.lim (Complex.cauSeqRe (Complex.exp' (f w : ℂ))) = _
      rw [Complex.lim_re, Real.exp, Complex.exp]
    have happly (s : Finset V) (n : ℕ) :
        (∑ w ∈ s, c w) n = ∑ w ∈ s, c w n := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hws ih =>
        simp only [Finset.sum_insert hws, CauSeq.add_apply, ih]
    have hlim (s : Finset V) :
        CauSeq.lim (∑ w ∈ s, c w) = ∑ w ∈ s, CauSeq.lim (c w) := by
      induction s using Finset.induction_on with
      | empty => simpa using (CauSeq.lim_const (abv := abs) (0 : ℝ))
      | @insert w s hws ih =>
        rw [Finset.sum_insert hws, Finset.sum_insert hws, ← CauSeq.lim_add, ih]
    have hlimsum : CauSeq.lim (∑ w : V, c w) = ∑ w : V, Real.exp (f w) := by
      rw [hlim]
      exact Finset.sum_congr rfl (fun w _ => hclim w)
    let t : ℕ → ℝ := fun k => Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
    have ht (k : ℕ) : 0 ≤ t k :=
      div_nonneg (hnonneg k) (Nat.cast_nonneg _)
    have hpartial (n : ℕ) :
        (∑ w : V, c w) n = ∑ k ∈ Finset.range n, t k := by
      rw [happly]
      simp_rw [hc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      change (∑ w : V, f w ^ k / (Nat.factorial k : ℝ)) =
        Matrix.trace (A ^ k) / (Nat.factorial k : ℝ)
      rw [← Finset.sum_div, htrace]
    have hlow : (∑ k ∈ Finset.range 7, t k) ≤ CauSeq.lim (∑ w : V, c w) := by
      apply CauSeq.le_lim
      apply CauSeq.le_of_exists
      refine ⟨7, fun n hn => ?_⟩
      rw [CauSeq.const_apply, hpartial]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
        (fun k _ _ => ht k)
    have ht0 : t 0 = (Fintype.card V : ℝ) := by simp [t]
    have ht1 : t 1 = 0 := by simp [t, A]
    have ht2 : t 2 = (G.edgeFinset.card : ℝ) := by
      norm_num [t, hsecond] <;> ring
    have ht4 : t 4 = Matrix.trace (A ^ 4) / 24 := by norm_num [t]
    have ht6 : t 6 = Matrix.trace (A ^ 6) / 720 := by norm_num [t]
    have hseven : (∑ k ∈ Finset.range 7, t k) =
        t 0 + t 1 + t 2 + t 3 + t 4 + t 5 + t 6 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hseven, ht0, ht1, ht2, ht4, ht6, hlimsum] at hlow
    change (Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ) +
      ((G.maxDegree : ℝ) ^ 2 / 12 + (G.maxDegree : ℝ) ^ 3 / 360) ≤
        ∑ w : V, Real.exp (f w)
    nlinarith only [hlow, hfourth, hsixth, ht 3, ht 5]

theorem model_a8dbf81d1cb58f023c39 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≥ (9999999 / 10000000 : ℝ))) :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≤ (((Fintype.card V : ℝ) * (((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) * (Real.exp (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) + ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) * (Real.exp ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))))))) / ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · norm_num [hV] at h_guard
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV] at h_guard ⊢
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let r : ℝ := sSup (Set.range f)
    let l : ℝ := sInf (Set.range f)
    have hgap : 0 < r - l := by
      change (9999999 / 10000000 : ℝ) ≤ r - l at h_guard
      linarith only [h_guard]
    have hsum : (∑ v : V, f v) = 0 := by
      simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
    have hpoint (v : V) :
        (r - l) * Real.exp (f v) ≤
          (r - f v) * Real.exp l + (f v - l) * Real.exp r := by
      have hlo : l ≤ f v :=
        csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self v)
      have hup : f v ≤ r :=
        le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v)
      rcases eq_or_lt_of_le hlo with heq | hlt
      · simp [← heq]
      · rcases eq_or_lt_of_le hup with heq | hlt'
        · simp [heq]
        · exact convexOn_exp.secant_mono_aux1
            (Set.mem_univ l) (Set.mem_univ r) hlt hlt'
    have htotal :
        (r - l) * (∑ v : V, Real.exp (f v)) ≤
          (Fintype.card V : ℝ) * ((-l) * Real.exp r + r * Real.exp l) := by
      calc
        (r - l) * (∑ v : V, Real.exp (f v)) =
            ∑ v : V, (r - l) * Real.exp (f v) := by
          rw [Finset.mul_sum]
        _ ≤ ∑ v : V,
            ((r - f v) * Real.exp l + (f v - l) * Real.exp r) :=
          Finset.sum_le_sum (fun v _ => hpoint v)
        _ = (Fintype.card V : ℝ) *
            ((-l) * Real.exp r + r * Real.exp l) := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_mul,
            Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, hsum]
          ring
    change (∑ v : V, Real.exp (f v)) ≤
      (Fintype.card V : ℝ) *
        (((r - l) - r) * Real.exp r + r * Real.exp (r - (r - l))) / (r - l)
    have he1 : (r - l) - r = -l := by ring
    have he2 : r - (r - l) = l := by ring
    rw [he1, he2]
    apply (le_div_iff₀ hgap).2
    rw [mul_comm (∑ v : V, Real.exp (f v)) (r - l)]
    exact htotal
theorem model_f8f2b4afb071e2a10817 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((((Fintype.card V : ℝ) / (2 : ℝ)) * ((Real.exp (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (Real.exp (-(Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))))))) + (((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) + (7 : ℝ))) / (180 : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · have hcard := h_guard.2.2
    norm_num [hV] at hcard
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨D, hreg⟩ := h_guard.2.1
    let n : ℝ := Fintype.card V
    let d : ℝ := D
    have hn : 0 < n := by
      dsimp only [n]
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    have hn0 : n ≠ 0 := ne_of_gt hn
    have hd : 0 ≤ d := by
      dsimp only [d]
      exact Nat.cast_nonneg D
    have hdegree (i : V) : (G.degree i : ℝ) = d := by
      dsimp only [d]
      exact_mod_cast (hreg.degree_eq i)
    have hdegSum : (∑ i : V, (G.degree i : ℝ)) = n * d := by
      simp only [hdegree, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl
    have hnd : n * d = 2 * (G.edgeFinset.card : ℝ) := by
      rw [← hdegSum]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have havg : 2 * (G.edgeFinset.card : ℝ) / n = d := by
      apply (div_eq_iff hn0).2
      nlinarith only [hnd]
    have hmean (z : V → ℝ) (hz : ∀ i, 0 ≤ z i) (k : ℕ) :
        n * ((∑ i : V, z i) / n) ^ k ≤ ∑ i : V, z i ^ k := by
      cases k with
      | zero => simp [n]
      | succ k =>
        have hp : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
        have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (k + 1)) := by
          simpa only [Real.rpow_natCast] using
            (convexOn_rpow (p := ((k + 1 : ℕ) : ℝ)) hp)
        have hw : (∑ _i : V, n⁻¹) = 1 := by
          simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
            (mul_inv_cancel₀ hn0)
        have h := hconv.map_sum_le
          (t := (Finset.univ : Finset V)) (w := fun _ : V => n⁻¹) (p := z)
          (fun _ _ => inv_nonneg.mpr hn.le) hw (fun i _ => hz i)
        simp only [smul_eq_mul, ← Finset.mul_sum] at h
        have havgz : (∑ i : V, z i) / n = n⁻¹ * (∑ i : V, z i) := by
          rw [div_eq_mul_inv]
          exact mul_comm _ _
        calc
          n * ((∑ i : V, z i) / n) ^ (k + 1) =
              n * (n⁻¹ * (∑ i : V, z i)) ^ (k + 1) := by rw [havgz]
          _ ≤ n * (n⁻¹ * (∑ i : V, z i ^ (k + 1))) :=
            mul_le_mul_of_nonneg_left h hn.le
          _ = ∑ i : V, z i ^ (k + 1) := by
            rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
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
    have hsecond : Matrix.trace (A ^ 2) = n * d := by
      calc
        Matrix.trace (A ^ 2) = ∑ w : V, (G.degree w : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply, A, pow_two,
            SimpleGraph.adjMatrix_mul_self_apply_self]
        _ = n * d := hdegSum
    have havgEig : (∑ w : V, f w ^ 2) / n = d := by
      rw [← htrace 2, hsecond, mul_div_cancel_left₀ d hn0]
    have hmoment (k : ℕ) : n * d ^ k ≤ Matrix.trace (A ^ (2 * k)) := by
      have h := hmean (fun w => f w ^ 2) (fun w => sq_nonneg (f w)) k
      rw [havgEig] at h
      rw [htrace (2 * k)]
      simpa only [pow_mul] using h
    have hAs : A.IsSymm := by
      dsimp only [A]
      exact G.isSymm_adjMatrix (α := ℝ)
    have hAnn (i j : V) : 0 ≤ A i j := by
      dsimp [A, SimpleGraph.adjMatrix]
      split_ifs <;> norm_num
    have hrowA (i : V) : (∑ j : V, A i j) = d := by
      have h := SimpleGraph.adjMatrix_mulVec_const_apply
        (G := G) (a := (1 : ℝ)) (v := i)
      change (∑ j : V, G.adjMatrix ℝ i j * 1) = (G.degree i : ℝ) * 1 at h
      simpa only [A, mul_one, hdegree] using h
    have hcolA (j : V) : (∑ i : V, A i j) = d := by
      calc
        (∑ i : V, A i j) = ∑ i : V, A j i :=
          Finset.sum_congr rfl (fun i _ => hAs.apply j i)
        _ = d := hrowA j
    have hrowPow (k : ℕ) (i : V) : (∑ j : V, (A ^ k) i j) = d ^ k := by
      induction k with
      | zero => simp [Matrix.one_apply]
      | succ k ih =>
        simp only [pow_succ, Matrix.mul_apply]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hrowA]
        rw [← Finset.sum_mul, ih]
    have htwice (k : ℕ) :
        Matrix.trace (A ^ (2 * k)) = ∑ i : V, ∑ j : V, (A ^ k) i j ^ 2 := by
      have hp : A ^ (2 * k) = A ^ k * A ^ k := by
        rw [two_mul, pow_add]
      have hs : (A ^ k).IsSymm := hAs.pow k
      rw [hp]
      unfold Matrix.trace
      apply Finset.sum_congr rfl
      intro i hi
      change (∑ j : V, (A ^ k) i j * (A ^ k) j i) =
        ∑ j : V, (A ^ k) i j ^ 2
      apply Finset.sum_congr rfl
      intro j hj
      rw [hs.apply i j, pow_two]
    have hentry (k : ℕ) (i j : V) : (A ^ k) i j ≤ (A ^ k) i j ^ 2 := by
      change (G.adjMatrix ℝ ^ k) i j ≤ ((G.adjMatrix ℝ ^ k) i j) ^ 2
      rw [G.adjMatrix_pow_apply_eq_card_walk k i j, pow_two]
      exact_mod_cast
        (Nat.le_mul_self (Fintype.card {p : G.Walk i j | p.length = k}))
    let B : Matrix V V ℝ := A ^ 2
    let C : Matrix V V ℝ := A ^ 3
    have hBdiag (i : V) : B i i = d := by
      simpa only [B, A, pow_two, hdegree] using
        (G.adjMatrix_mul_self_apply_self (α := ℝ) i)
    have hrow4 (i : V) : 2 * d ^ 2 - d ≤ ∑ j : V, B i j ^ 2 := by
      have hs : B i i ^ 2 - B i i ≤ ∑ j : V, (B i j ^ 2 - B i j) :=
        Finset.single_le_sum
          (fun j _ => sub_nonneg.mpr (hentry 2 i j)) (Finset.mem_univ i)
      rw [hBdiag i] at hs
      simp only [Finset.sum_sub_distrib] at hs
      have hr : (∑ j : V, B i j) = d ^ 2 := hrowPow 2 i
      rw [hr] at hs
      linarith only [hs]
    have hfourth : n * (2 * d ^ 2 - d) ≤ Matrix.trace (A ^ 4) := by
      calc
        n * (2 * d ^ 2 - d) = ∑ i : V, (2 * d ^ 2 - d) := by
          simp [n, nsmul_eq_mul] <;> ring
        _ ≤ ∑ i : V, ∑ j : V, B i j ^ 2 :=
          Finset.sum_le_sum (fun i _ => hrow4 i)
        _ = Matrix.trace (A ^ 4) := by
          simpa only [B] using (htwice 2).symm
    have hBvia (i j w : V) (hij : G.Adj i j) : A j w ≤ B i w := by
      calc
        A j w = A i j * A j w := by simp [A, hij]
        _ ≤ ∑ u : V, A i u * A u w :=
          Finset.single_le_sum
            (fun u _ => mul_nonneg (hAnn i u) (hAnn u w)) (Finset.mem_univ j)
        _ = B i w := by simp only [B, pow_two, Matrix.mul_apply]
    have hCedge (i j : V) (hij : G.Adj i j) : 2 * d - 1 ≤ C i j := by
      have hterm (w : V) : 0 ≤ B i w * A w j - A w j := by
        by_cases hw : G.Adj w j
        · have hb : 1 ≤ B i w := by
            simpa [A, hw.symm] using hBvia i j w hij
          simpa [A, hw] using sub_nonneg.mpr hb
        · simp [A, hw]
      have hs : B i i * A i j - A i j ≤
          ∑ w : V, (B i w * A w j - A w j) :=
        Finset.single_le_sum (fun w _ => hterm w) (Finset.mem_univ i)
      have hmul : (∑ w : V, B i w * A w j) = C i j := by
        change (A ^ 2 * A) i j = (A ^ 3) i j
        rw [← pow_succ]
      have hai : A i j = 1 := by simp [A, hij]
      simp only [Finset.sum_sub_distrib] at hs
      rw [hmul, hcolA j, hBdiag i, hai] at hs
      linarith only [hs]
    have hCpoint (i j : V) :
        C i j + ((2 * d - 1) ^ 2 - (2 * d - 1)) * A i j ≤ C i j ^ 2 := by
      by_cases hij : G.Adj i j
      · have hc := hCedge i j hij
        have hd1 : 1 ≤ d := by
          have hh : 1 ≤ G.degree i := Nat.succ_le_of_lt hij.degree_pos_left
          have hh' : (1 : ℝ) ≤ (G.degree i : ℝ) := by exact_mod_cast hh
          rwa [hdegree i] at hh'
        have hp : 0 ≤ (C i j - (2 * d - 1)) * (C i j + (2 * d - 1) - 1) :=
          mul_nonneg (sub_nonneg.mpr hc) (by linarith only [hc, hd1])
        have hai : A i j = 1 := by simp [A, hij]
        rw [hai, mul_one]
        nlinarith only [hp]
      · have hai : A i j = 0 := by simp [A, hij]
        rw [hai, mul_zero, add_zero]
        exact hentry 3 i j
    have hrow6 (i : V) :
        d ^ 3 + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d ≤
          ∑ j : V, C i j ^ 2 := by
      calc
        d ^ 3 + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d =
            ∑ j : V, (C i j + ((2 * d - 1) ^ 2 - (2 * d - 1)) * A i j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hrowA]
          change d ^ 3 + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d =
            (∑ j : V, (A ^ 3) i j) + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d
          rw [hrowPow 3 i]
        _ ≤ ∑ j : V, C i j ^ 2 :=
          Finset.sum_le_sum (fun j _ => hCpoint i j)
    have hsixth : n * (5 * d ^ 3 - 6 * d ^ 2 + 2 * d) ≤
        Matrix.trace (A ^ 6) := by
      calc
        n * (5 * d ^ 3 - 6 * d ^ 2 + 2 * d) =
            ∑ i : V, (d ^ 3 + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          change n * (5 * d ^ 3 - 6 * d ^ 2 + 2 * d) =
            n * (d ^ 3 + ((2 * d - 1) ^ 2 - (2 * d - 1)) * d)
          ring
        _ ≤ ∑ i : V, ∑ j : V, C i j ^ 2 :=
          Finset.sum_le_sum (fun i _ => hrow6 i)
        _ = Matrix.trace (A ^ 6) := by
          simpa only [C] using (htwice 3).symm
    let a : ℝ := Real.sqrt d
    have ha2 : a ^ 2 = d := by
      simpa only [a] using Real.sq_sqrt hd
    have hcoef (k : ℕ) :
        n / 2 * (a ^ k + (-a) ^ k) ≤ Matrix.trace (A ^ k) := by
      obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
      · subst k
        calc
          n / 2 * (a ^ (2 * r) + (-a) ^ (2 * r)) = n * d ^ r := by
            simp only [pow_mul, neg_sq, ha2]
            ring
          _ ≤ Matrix.trace (A ^ (2 * r)) := hmoment r
      · subst k
        have hz : a ^ (2 * r + 1) + (-a) ^ (2 * r + 1) = 0 := by
          simp only [pow_succ, pow_mul, neg_sq]
          ring
        rw [hz, mul_zero]
        exact hnonneg (2 * r + 1)
    let q : ℕ → ℝ := fun k =>
      (Matrix.trace (A ^ k) - n / 2 * (a ^ k + (-a) ^ k)) /
        (Nat.factorial k : ℝ)
    have hq (k : ℕ) : 0 ≤ q k :=
      div_nonneg (sub_nonneg.mpr (hcoef k)) (Nat.cast_nonneg _)
    have hq4 : n * d * (d - 1) / 24 ≤ q 4 := by
      have hc4 : n / 2 * (a ^ 4 + (-a) ^ 4) = n * d ^ 2 := by
        calc
          n / 2 * (a ^ 4 + (-a) ^ 4) =
              n / 2 * ((a ^ 2) ^ 2 + ((-a) ^ 2) ^ 2) := by ring
          _ = n * d ^ 2 := by
            simp only [neg_sq, ha2]
            ring
      have hfac : (Nat.factorial 4 : ℝ) = 24 := by norm_num
      dsimp only [q]
      rw [hfac, hc4]
      nlinarith only [hfourth]
    have hq6 : n * d * (d - 1) * (2 * d - 1) / 360 ≤ q 6 := by
      have hc6 : n / 2 * (a ^ 6 + (-a) ^ 6) = n * d ^ 3 := by
        calc
          n / 2 * (a ^ 6 + (-a) ^ 6) =
              n / 2 * ((a ^ 2) ^ 3 + ((-a) ^ 2) ^ 3) := by ring
          _ = n * d ^ 3 := by
            simp only [neg_sq, ha2]
            ring
      have hfac : (Nat.factorial 6 : ℝ) = 720 := by norm_num
      dsimp only [q]
      rw [hfac, hc6]
      nlinarith only [hsixth]
    let c : ℝ → CauSeq ℝ abs := fun x =>
      Complex.cauSeqRe (Complex.exp' (x : ℂ))
    have hc (x : ℝ) (N : ℕ) :
        c x N = ∑ k ∈ Finset.range N, x ^ k / (Nat.factorial k : ℝ) := by
      change (∑ k ∈ Finset.range N,
        (x : ℂ) ^ k / (Nat.factorial k : ℂ)).re = _
      simp only [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Complex.ofReal_pow, ← Complex.ofReal_natCast,
        ← Complex.ofReal_div, Complex.ofReal_re]
    have hclim (x : ℝ) : CauSeq.lim (c x) = Real.exp x := by
      change CauSeq.lim (Complex.cauSeqRe (Complex.exp' (x : ℂ))) = _
      rw [Complex.lim_re, Real.exp, Complex.exp]
    have happly (s : Finset V) (N : ℕ) :
        (∑ w ∈ s, c (f w)) N = ∑ w ∈ s, c (f w) N := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert w s hws ih =>
        simp only [Finset.sum_insert hws, CauSeq.add_apply, ih]
    have hlim (s : Finset V) :
        CauSeq.lim (∑ w ∈ s, c (f w)) = ∑ w ∈ s, CauSeq.lim (c (f w)) := by
      induction s using Finset.induction_on with
      | empty => simpa using (CauSeq.lim_const (abv := abs) (0 : ℝ))
      | @insert w s hws ih =>
        rw [Finset.sum_insert hws, Finset.sum_insert hws, ← CauSeq.lim_add, ih]
    have hlimsum : CauSeq.lim (∑ w : V, c (f w)) =
        ∑ w : V, Real.exp (f w) := by
      rw [hlim]
      exact Finset.sum_congr rfl (fun w _ => hclim (f w))
    let b : CauSeq ℝ abs := CauSeq.const abs (n / 2) * (c a + c (-a))
    have hlimb : CauSeq.lim b = n / 2 * (Real.exp a + Real.exp (-a)) := by
      dsimp only [b]
      simp only [← CauSeq.lim_mul_lim, CauSeq.lim_const, ← CauSeq.lim_add, hclim]
    have hpartial (N : ℕ) :
        (∑ w : V, c (f w)) N =
          ∑ k ∈ Finset.range N, Matrix.trace (A ^ k) / (Nat.factorial k : ℝ) := by
      rw [happly]
      simp_rw [hc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_div, htrace]
    have hbpartial (N : ℕ) :
        b N = ∑ k ∈ Finset.range N,
          (n / 2 * (a ^ k + (-a) ^ k)) / (Nat.factorial k : ℝ) := by
      dsimp only [b]
      rw [CauSeq.mul_apply, CauSeq.const_apply, CauSeq.add_apply, hc, hc]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hdiff (N : ℕ) :
        ((∑ w : V, c (f w)) - b) N = ∑ k ∈ Finset.range N, q k := by
      rw [CauSeq.sub_apply, hpartial, hbpartial, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [q]
      ring
    have hlimdiff : CauSeq.lim ((∑ w : V, c (f w)) - b) =
        (∑ w : V, Real.exp (f w)) - n / 2 * (Real.exp a + Real.exp (-a)) := by
      rw [← CauSeq.lim_sub, hlimsum, hlimb]
    have hlow : n * d * (d - 1) * (d + 7) / 180 ≤
        CauSeq.lim ((∑ w : V, c (f w)) - b) := by
      apply CauSeq.le_lim
      apply CauSeq.le_of_exists
      refine ⟨7, fun N hN => ?_⟩
      rw [CauSeq.const_apply, hdiff]
      have hpair : q 4 + q 6 ≤ ∑ k ∈ Finset.range N, q k := by
        calc
          q 4 + q 6 = ∑ k ∈ ({4, 6} : Finset ℕ), q k := by simp
          _ ≤ ∑ k ∈ Finset.range N, q k :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro k hk
                simp only [Finset.mem_insert, Finset.mem_singleton] at hk
                rcases hk with rfl | rfl <;>
                  simp only [Finset.mem_range] <;> omega)
              (fun k _ _ => hq k)
      have hcorrection : n * d * (d - 1) * (d + 7) / 180 ≤ q 4 + q 6 := by
        nlinarith only [hq4, hq6]
      exact le_trans hcorrection hpair
    rw [hlimdiff] at hlow
    simp only [if_neg hV]
    change n / 2 *
      (Real.exp (Real.sqrt (2 * (G.edgeFinset.card : ℝ) / n)) +
        Real.exp (-(Real.sqrt (2 * (G.edgeFinset.card : ℝ) / n)))) +
      n * (2 * (G.edgeFinset.card : ℝ) / n) *
        ((2 * (G.edgeFinset.card : ℝ) / n) - 1) *
        ((2 * (G.edgeFinset.card : ℝ) / n) + 7) / 180 ≤
          ∑ w : V, Real.exp (f w)
    rw [havg]
    change n / 2 * (Real.exp a + Real.exp (-a)) +
      n * d * (d - 1) * (d + 7) / 180 ≤ ∑ w : V, Real.exp (f w)
    linarith only [hlow]
