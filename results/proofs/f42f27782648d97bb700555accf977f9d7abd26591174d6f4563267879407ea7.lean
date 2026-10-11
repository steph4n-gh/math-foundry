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

theorem model_116b5eaad944a7e29fed {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ ((((4 : ℝ) / (5 : ℝ)) * (Fintype.card V : ℝ)) + (((133 : ℝ) / (90 : ℝ)) * (G.edgeFinset.card : ℝ))) := by
  classical
  have hcard : 1 < Fintype.card V := by
    by_contra hn
    have hn' : (Fintype.card V : ℝ) ≤ 1 := by
      exact_mod_cast (le_of_not_gt hn)
    linarith only [h_guard.2.1, hn']
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard
  haveI : Nonempty V := h_guard.1.nonempty
  have hmax : G.maxDegree ≤ 2 := by
    by_contra hn
    have hthree : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast (show 3 ≤ G.maxDegree by omega)
    linarith only [h_guard.2.2, hthree]
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  let d : V → ℝ := fun i => (G.degree i : ℝ)
  have hd2 (i : V) : d i ≤ 2 := by
    change (G.degree i : ℝ) ≤ (2 : ℝ)
    exact_mod_cast (le_trans (G.degree_le_maxDegree i) hmax)
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
  have hsumdeg : (∑ i : V, d i) = 2 * (G.edgeFinset.card : ℝ) := by
    change (∑ i : V, (G.degree i : ℝ)) = 2 * (G.edgeFinset.card : ℝ)
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsecond : Matrix.trace (A ^ 2) = 2 * (G.edgeFinset.card : ℝ) := by
    calc
      Matrix.trace (A ^ 2) = ∑ i : V, d i := by
        simp only [Matrix.trace, Matrix.diag_apply, A, d, pow_two,
          SimpleGraph.adjMatrix_mul_self_apply_self]
      _ = 2 * (G.edgeFinset.card : ℝ) := hsumdeg
  have hAnn (i j : V) : 0 ≤ A i j := by
    dsimp [A, SimpleGraph.adjMatrix]
    split_ifs <;> norm_num
  have hrow (i : V) : (∑ j : V, A i j) = d i := by
    have h := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := G) (α := ℝ) (a := 1) (v := i)
    change (∑ j : V, A i j * (1 : ℝ)) = (G.degree i : ℝ) * 1 at h
    simpa only [mul_one, d] using h
  have hcol (i : V) : (∑ j : V, A j i) = d i := by
    calc
      (∑ j : V, A j i) = ∑ j : V, A i j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (G.isSymm_adjMatrix (α := ℝ)).apply i j
      _ = d i := hrow i
  have hsumA : (∑ i : V, ∑ j : V, A i j) =
      2 * (G.edgeFinset.card : ℝ) := by
    simp only [hrow, hsumdeg]
  have hleft : (∑ i : V, ∑ j : V, A i j * d i) =
      ∑ i : V, d i ^ 2 := by
    calc
      (∑ i : V, ∑ j : V, A i j * d i) =
          ∑ i : V, (∑ j : V, A i j) * d i := by
        simp only [Finset.sum_mul]
      _ = ∑ i : V, d i ^ 2 := by simp only [hrow, pow_two]
  have hright : (∑ i : V, ∑ j : V, A i j * d j) =
      ∑ i : V, d i ^ 2 := by
    calc
      (∑ i : V, ∑ j : V, A i j * d j) =
          ∑ j : V, ∑ i : V, A i j * d j := Finset.sum_comm
      _ = ∑ j : V, (∑ i : V, A i j) * d j := by
        simp only [Finset.sum_mul]
      _ = ∑ j : V, d j ^ 2 := by simp only [hcol, pow_two]
  have hd (i : V) : 3 * d i - 2 ≤ d i ^ 2 := by
    have hpos : 0 < G.degree i :=
      h_guard.1.preconnected.degree_pos_of_nontrivial i
    by_cases hi : G.degree i = 1
    · norm_num [d, hi]
    · have htwo : (2 : ℝ) ≤ d i := by
        change (2 : ℝ) ≤ (G.degree i : ℝ)
        exact_mod_cast (show 2 ≤ G.degree i by omega)
      nlinarith only [htwo, sq_nonneg (d i - 2)]
  have hdSum : 6 * (G.edgeFinset.card : ℝ) - 2 * (Fintype.card V : ℝ) ≤
      ∑ i : V, d i ^ 2 := by
    have h : (∑ i : V, (3 * d i - 2)) ≤ ∑ i : V, d i ^ 2 :=
      Finset.sum_le_sum (fun i _ => hd i)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, hsumdeg] at h
    nlinarith only [h]
  let B : Matrix V V ℝ := A ^ 2
  have hBs : B.IsSymm := by
    dsimp [B, A]
    exact (G.isSymm_adjMatrix (α := ℝ)).pow 2
  have hBdiag (i : V) : B i i = d i := by
    simpa only [B, A, d, pow_two] using
      (G.adjMatrix_mul_self_apply_self (α := ℝ) i)
  have hBrow (i : V) : (∑ j : V, B i j) = ∑ k : V, A i k * d k := by
    calc
      (∑ j : V, B i j) = ∑ j : V, ∑ k : V, A i k * A k j := by
        simp only [B, pow_two, Matrix.mul_apply]
      _ = ∑ k : V, ∑ j : V, A i k * A k j := Finset.sum_comm
      _ = ∑ k : V, A i k * (∑ j : V, A k j) := by
        simp only [Finset.mul_sum]
      _ = ∑ k : V, A i k * d k := by simp only [hrow]
  have hsumB : (∑ i : V, ∑ j : V, B i j) = ∑ i : V, d i ^ 2 := by
    simp only [hBrow]
    exact hright
  have hBsq (i j : V) : B i j ≤ B i j ^ 2 := by
    change (G.adjMatrix ℝ ^ 2) i j ≤ ((G.adjMatrix ℝ ^ 2) i j) ^ 2
    rw [G.adjMatrix_pow_apply_eq_card_walk 2 i j, pow_two]
    exact_mod_cast
      (Nat.le_mul_self (Fintype.card {p : G.Walk i j | p.length = 2}))
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
  have hRi (i : V) :
      d i ^ 2 - d i + (∑ j : V, B i j) ≤ ∑ j : V, B i j ^ 2 := by
    have he := Finset.sum_le_sum
      (fun j (_ : j ∈ Finset.univ.erase i) => hBsq i j)
    rw [← Finset.add_sum_erase Finset.univ (fun j => B i j)
        (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ (fun j => B i j ^ 2)
        (Finset.mem_univ i), hBdiag i]
    linarith only [he]
  have hrows4 :
      (∑ i : V, (d i ^ 2 - d i + (∑ j : V, B i j))) ≤
        ∑ i : V, ∑ j : V, B i j ^ 2 :=
    Finset.sum_le_sum (fun i _ => hRi i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hrows4
  rw [hsumdeg, hsumB, ← hfourRows] at hrows4
  have hfourth : 10 * (G.edgeFinset.card : ℝ) - 4 * (Fintype.card V : ℝ) ≤
      Matrix.trace (A ^ 4) := by
    nlinarith only [hdSum, hrows4]
  have hBneighbors (i j k : V) (hij : G.Adj i j) (hik : G.Adj i k) :
      1 ≤ B j k := by
    calc
      (1 : ℝ) = A j i * A i k := by simp [A, hij.symm, hik]
      _ ≤ ∑ w : V, A j w * A w k :=
        Finset.single_le_sum
          (fun w _ => mul_nonneg (hAnn j w) (hAnn w k))
          (Finset.mem_univ i)
      _ = B j k := by simp only [B, pow_two, Matrix.mul_apply]
  let C : Matrix V V ℝ := A ^ 3
  have hCmul : C = A * B := by
    change A ^ (2 + 1) = A * A ^ 2
    rw [pow_succ']
  have hCs : C.IsSymm := by
    dsimp [C, A]
    exact (G.isSymm_adjMatrix (α := ℝ)).pow 3
  have hCedge (i j : V) (hij : G.Adj i j) : d i + d j - 1 ≤ C i j := by
    have hj : j ∈ G.neighborFinset i := (G.mem_neighborFinset i j).mpr hij
    have hdErase : d i = 1 + ∑ k ∈ (G.neighborFinset i).erase j, (1 : ℝ) := by
      calc
        d i = ∑ k ∈ G.neighborFinset i, (1 : ℝ) := by simp [d]
        _ = 1 + ∑ k ∈ (G.neighborFinset i).erase j, (1 : ℝ) :=
          (Finset.add_sum_erase (G.neighborFinset i) (fun _ => (1 : ℝ)) hj).symm
    have hrest : (∑ k ∈ (G.neighborFinset i).erase j, (1 : ℝ)) ≤
        ∑ k ∈ (G.neighborFinset i).erase j, B k j := by
      apply Finset.sum_le_sum
      intro k hk
      exact hBneighbors i k j
        ((G.mem_neighborFinset i k).mp (Finset.mem_erase.mp hk).2) hij
    have heq : C i j = d j + ∑ k ∈ (G.neighborFinset i).erase j, B k j := by
      calc
        C i j = ∑ k ∈ G.neighborFinset i, B k j := by
          rw [hCmul]
          exact G.adjMatrix_mul_apply B i j
        _ = B j j + ∑ k ∈ (G.neighborFinset i).erase j, B k j :=
          (Finset.add_sum_erase (G.neighborFinset i) (fun k => B k j) hj).symm
        _ = d j + ∑ k ∈ (G.neighborFinset i).erase j, B k j := by
          rw [hBdiag j]
    linarith only [hdErase, hrest, heq]
  have hsumC : (∑ i : V, ∑ j : V, C i j) =
      ∑ i : V, ∑ j : V, A i j * (d i * d j) := by
    calc
      (∑ i : V, ∑ j : V, C i j) =
          ∑ i : V, ∑ j : V, ∑ k : V, A i k * B k j := by
        simp only [hCmul, Matrix.mul_apply]
      _ = ∑ i : V, ∑ k : V, ∑ j : V, A i k * B k j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = ∑ k : V, ∑ i : V, ∑ j : V, A i k * B k j := Finset.sum_comm
      _ = ∑ k : V, (∑ i : V, A i k) * (∑ j : V, B k j) := by
        simp only [Finset.sum_mul_sum]
      _ = ∑ k : V, d k * (∑ j : V, B k j) := by simp only [hcol]
      _ = ∑ k : V, d k * (∑ j : V, A k j * d j) := by simp only [hBrow]
      _ = ∑ k : V, ∑ j : V, A k j * (d k * d j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hproduct (i j : V) : 2 * d i + 2 * d j - 4 ≤ d i * d j := by
    have hp := mul_nonneg (sub_nonneg.mpr (hd2 i)) (sub_nonneg.mpr (hd2 j))
    nlinarith only [hp]
  have hCsumlower : 4 * (∑ i : V, d i ^ 2) - 8 * (G.edgeFinset.card : ℝ) ≤
      ∑ i : V, ∑ j : V, C i j := by
    have h :
        (∑ i : V, ∑ j : V,
          (2 * (A i j * d i) + 2 * (A i j * d j) - 4 * A i j)) ≤
          ∑ i : V, ∑ j : V, A i j * (d i * d j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hh := mul_le_mul_of_nonneg_left (hproduct i j) (hAnn i j)
      nlinarith only [hh]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at h
    rw [hleft, hright, hsumA, ← hsumC] at h
    nlinarith only [h]
  have hpoly (q : ℕ) : 5 * (q : ℝ) - 6 ≤ (q : ℝ) ^ 2 := by
    by_cases hq1 : q ≤ 1
    · have hqr : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
      nlinarith only [hqr, sq_nonneg (q : ℝ)]
    · by_cases hq2 : q = 2
      · norm_num [hq2]
      · have hqr : (3 : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast (show 3 ≤ q by omega)
        nlinarith only [hqr, sq_nonneg ((q : ℝ) - 3)]
  have hCpoly (i j : V) : 5 * C i j - 6 ≤ C i j ^ 2 := by
    change 5 * (G.adjMatrix ℝ ^ 3) i j - 6 ≤ ((G.adjMatrix ℝ ^ 3) i j) ^ 2
    rw [G.adjMatrix_pow_apply_eq_card_walk 3 i j]
    exact hpoly _
  have hCbase (i j : V) : C i j ≤ C i j ^ 2 := by
    change (G.adjMatrix ℝ ^ 3) i j ≤ ((G.adjMatrix ℝ ^ 3) i j) ^ 2
    rw [G.adjMatrix_pow_apply_eq_card_walk 3 i j, pow_two]
    exact_mod_cast
      (Nat.le_mul_self (Fintype.card {p : G.Walk i j | p.length = 3}))
  have hCpoint (i j : V) :
      C i j + 4 * (A i j * d i) + 4 * (A i j * d j) - 10 * A i j ≤
        C i j ^ 2 := by
    by_cases hij : G.Adj i j
    · have ha : A i j = 1 := by simp [A, hij]
      rw [ha]
      nlinarith only [hCpoly i j, hCedge i j hij]
    · have ha : A i j = 0 := by simp [A, hij]
      rw [ha]
      simpa only [zero_mul, mul_zero, add_zero, sub_zero] using hCbase i j
  have hsixRows : Matrix.trace (A ^ 6) = ∑ i : V, ∑ j : V, C i j ^ 2 := by
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
  have hrows6 :
      (∑ i : V, ∑ j : V,
        (C i j + 4 * (A i j * d i) + 4 * (A i j * d j) - 10 * A i j)) ≤
          ∑ i : V, ∑ j : V, C i j ^ 2 :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hCpoint i j))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hrows6
  rw [hleft, hright, hsumA, ← hsixRows] at hrows6
  have hsixth : 44 * (G.edgeFinset.card : ℝ) - 24 * (Fintype.card V : ℝ) ≤
      Matrix.trace (A ^ 6) := by
    nlinarith only [hCsumlower, hrows6, hdSum]
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
  change (4 : ℝ) / 5 * (Fintype.card V : ℝ) +
    (133 : ℝ) / 90 * (G.edgeFinset.card : ℝ) ≤ ∑ w : V, Real.exp (f w)
  nlinarith only [hlow, hfourth, hsixth, ht 3, ht 5]
