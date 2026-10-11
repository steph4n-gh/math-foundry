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

theorem estrada_ge_energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  classical
  have hsum : (∑ v : V, (G.isHermitian_adjMatrix ℝ).eigenvalues v) = 0 := by
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have hpoint (x : ℝ) : |x| + x ≤ Real.exp x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hexp := Real.quadratic_le_exp_of_nonneg hx
      nlinarith [sq_nonneg (x - 1)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have hbound :
      (∑ v : V, (|(G.isHermitian_adjMatrix ℝ).eigenvalues v| +
        (G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≤
      ∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v) := by
    exact Finset.sum_le_sum (fun v _ => hpoint _)
  simpa only [Finset.sum_add_distrib, hsum, add_zero] using hbound

theorem graph_energy_spectral_radius_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  have hsum : (∑ v : V, f v) = 0 := by
    simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hnonneg (w : V) : 0 ≤ |f w| + f w := by
      linarith [neg_abs_le (f w)]
    have hsingle : |f v| + f v ≤ ∑ w : V, (|f w| + f w) :=
      Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
    simp only [Finset.sum_add_distrib, hsum, add_zero] at hsingle
    change 2 * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) ≤
      ∑ w : V, |f w|
    rw [if_neg hV, ← hv]
    linarith [le_abs_self (f v)]

theorem composed_35ca49dcc0267544 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) := by
  exact le_trans (graph_energy_spectral_radius_lower G) (estrada_ge_energy G)

theorem spectral_spread_le_two_spectral_radius {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    change r - sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) ≤ 2 * r
    have hsym : (G.adjMatrix ℝ).toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    have heig (i : V) : (G.adjMatrix ℝ).toEuclideanLin (b i) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i • b i := by
      apply WithLp.ofLp_injective 2
      simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
        (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
    have hle (i : V) : (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ r :=
      le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
    have hq (x : EuclideanSpace ℝ V) :
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x ≤ r * inner ℝ x x := by
      calc
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
            ∑ i : V, (G.isHermitian_adjMatrix ℝ).eigenvalues i *
              (inner ℝ x (b i)) ^ 2 := by
          rw [← b.sum_inner_mul_inner ((G.adjMatrix ℝ).toEuclideanLin x) x]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hsym x (b i), heig i, inner_smul_right, real_inner_comm x (b i)]
          ring
        _ ≤ ∑ i : V, r * (inner ℝ x (b i)) ^ 2 :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
        _ = r * inner ℝ x x := by
          rw [← Finset.mul_sum]
          congr 1
          calc
            (∑ i : V, (inner ℝ x (b i)) ^ 2) =
                ∑ i : V, inner ℝ x (b i) * inner ℝ (b i) x := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [real_inner_comm x (b i)]
              ring
            _ = inner ℝ x x := b.sum_inner_mul_inner x x
    have hcoord (z : EuclideanSpace ℝ V) :
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin z) z =
          ∑ v : V, ∑ w ∈ G.neighborFinset v, z v * z w := by
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [WithLp.ofLp_toLp, star_trivial]
      change (∑ v : V, z v * Matrix.mulVec (G.adjMatrix ℝ) (fun w => z w) v) = _
      simp only [SimpleGraph.adjMatrix_mulVec_apply, Finset.mul_sum]
    have hlower (i : V) : -r ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
      let y : EuclideanSpace ℝ V := WithLp.toLp 2 (fun v => |b i v|)
      have hnormy : inner ℝ y y = 1 := by
        calc
          inner ℝ y y = inner ℝ (b i) (b i) := by
            simp only [EuclideanSpace.inner_eq_star_dotProduct, y,
              WithLp.ofLp_toLp, star_trivial]
            change (∑ v : V, |b i v| * |b i v|) =
              (∑ v : V, b i v * b i v)
            simp only [abs_mul_abs_self]
          _ = 1 := b.inner_eq_one i
      have heigen : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) =
          (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
        rw [heig i, real_inner_smul_left, b.inner_eq_one i, mul_one]
      have habs :
          -inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) ≤
            inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y := by
        simp only [hcoord]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro v hv
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro w hw
        change -(b i v * b i w) ≤ |b i v| * |b i w|
        rw [← abs_mul]
        exact neg_le_abs _
      have hy : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y ≤ r := by
        simpa only [hnormy, mul_one] using hq y
      have hneg := habs.trans hy
      rw [heigen] at hneg
      linarith only [hneg]
    have hmin : -r ≤ sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      exact hlower i
    linarith only [hmin]

theorem composed_845382c1cbed672e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) := by
  apply le_trans (spectral_spread_le_two_spectral_radius G)
  exact composed_35ca49dcc0267544 G

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h
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
