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

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

theorem gutman_energy_size_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  let b := (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  let x : V → V → ℝ := fun i v => b i v
  have hsq (v : V) : (∑ i : V, x i v ^ 2) = 1 := by
    simpa only [x, EuclideanSpace.basisFun_inner,
      (EuclideanSpace.basisFun V ℝ).orthonormal.1 v, one_pow] using
      b.sum_sq_inner_left ((EuclideanSpace.basisFun V ℝ) v)
  have heig (i : V) :
      (G.isHermitian_adjMatrix ℝ).eigenvalues i =
        ∑ u : V, ∑ v : V, if G.Adj u v then x i u * x i v else 0 := by
    simpa only [RCLike.re_to_real, dotProduct, Pi.star_apply, star_trivial,
      Matrix.mulVec_apply_eq_sum, SimpleGraph.adjMatrix_apply, ite_mul,
      one_mul, zero_mul, Finset.mul_sum, mul_ite, mul_zero, x, b] using
      (G.isHermitian_adjMatrix ℝ).eigenvalues_eq i
  have hbound (i : V) :
      |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤
        ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
    rw [heig i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun u _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases huv : G.Adj u v
    · simp only [if_pos huv, abs_mul]
      have h := two_mul_le_add_sq |x i u| |x i v|
      simp only [sq_abs] at h
      linarith only [h]
    · simp [huv]
  calc
    (∑ i : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|) ≤
        ∑ i : V, ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ u : V, ∑ v : V, ∑ i : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : G.Adj u v
      · simp only [if_pos huv]
        rw [← Finset.sum_div, Finset.sum_add_distrib, hsq u, hsq v]
        norm_num
      · simp only [if_neg huv, Finset.sum_const_zero]
    _ = ∑ u : V, (G.degree u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (G.degree_eq_sum_if_adj u).symm
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem composed_1f7e49d87d42f727 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) := gutman_energy_size_bound G
    _ ≤ (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := degree_sum_density_bound G

theorem model_081bc55d24f66b98c45d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2) ≤ ((2 : ℝ) * ((Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ))) := by
  classical
    let hA := G.isHermitian_adjMatrix ℝ
    let D : Matrix V V ℝ := Matrix.diagonal hA.eigenvalues
    let U := hA.eigenvectorUnitary
    have hspec : G.adjMatrix ℝ =
        Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U D := by
      simpa [D, U] using hA.spectral_theorem
    have htrace : Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
        ∑ v : V, hA.eigenvalues v ^ 2 := by
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U (D * D)) := by
          rw [map_mul, ← hspec]
        _ = Matrix.trace (D * D) := by
          rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, one_mul]
        _ = ∑ v : V, hA.eigenvalues v ^ 2 := by
          simp [D, Matrix.diagonal_mul_diagonal, pow_two]
    have hsquares : (∑ v : V, hA.eigenvalues v ^ 2) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      rw [← htrace]
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            ∑ v : V, (G.degree v : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply,
            G.adjMatrix_mul_self_apply_self]
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hCS : (∑ v : V, |hA.eigenvalues v|) ^ 2 ≤
        (Fintype.card V : ℝ) * ∑ v : V, hA.eigenvalues v ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ : V => (1 : ℝ)) (fun v => |hA.eigenvalues v|))
    rw [hsquares] at hCS
    calc
      _ ≤ (Fintype.card V : ℝ) * ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := hCS
      _ = _ := by ring

theorem model_858f11e4042b2a0e80d8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((Fintype.card V : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) - ((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) / (48 : ℝ))) := by
  classical
  have hDelta : G.maxDegree ≤ 2 := by
    by_contra h
    have hn : 3 ≤ G.maxDegree := by omega
    have hr : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hn
    linarith
  by_cases hn0 : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    simp [hn0]
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  let n : ℝ := Fintype.card V
  let q : ℝ := 2 * (G.edgeFinset.card : ℝ)
  let a : ℝ := q / n
  let r : ℝ := Real.sqrt a
  let E : ℝ := ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnne : n ≠ 0 := ne_of_gt hn
  have ha : 0 ≤ a :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
  have hna : n * a = q := by
    have h : q = a * n :=
      (div_eq_iff hnne).mp (show q / n = a from rfl)
    exact (mul_comm n a).trans h.symm
  have ha2 : a ≤ 2 := by
    have hden : q ≤ n * (G.maxDegree : ℝ) := degree_sum_density_bound G
    have hdreal : (G.maxDegree : ℝ) ≤ 2 := by exact_mod_cast hDelta
    have hq : q ≤ n * 2 :=
      hden.trans (mul_le_mul_of_nonneg_left hdreal hn.le)
    rw [← hna] at hq
    exact (mul_le_mul_iff_right₀ hn).mp hq
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg a
  have hrsq : r ^ 2 = a := Real.sq_sqrt ha
  simp only [if_neg hn0]
  change E ≤ n * r - (n * a * (a - 1)) / 48
  have hMc : E ≤ n * r := by
    apply le_of_sq_le_sq ?_ (mul_nonneg hn.le hrnonneg)
    calc
      E ^ 2 ≤ 2 * (n * (G.edgeFinset.card : ℝ)) :=
        model_081bc55d24f66b98c45d G
      _ = n * q := by dsimp only [q]; ring
      _ = (n * r) ^ 2 := by
        rw [← hna, mul_pow, hrsq]
        ring
  by_cases ha1 : a ≤ 1
  · have hneg : n * a * (a - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hn.le ha) (sub_nonpos.mpr ha1)
    have hdiv : (n * a * (a - 1)) / 48 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hneg (by norm_num)
    linarith only [hMc, hdiv]
  have hagt : 1 < a := lt_of_not_ge ha1
  have hrpos : 0 < r :=
    Real.sqrt_pos.mpr (lt_trans (by norm_num : (0 : ℝ) < 1) hagt)
  have hrle : r ≤ 3 / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith only [ha2]
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let b := hA.eigenvectorBasis
  have hfbound (i : V) : |f i| ≤ 2 := by
    obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset V) (fun v => |b i v|) Finset.univ_nonempty
    have hpos : 0 < |b i v| := by
      by_contra hp
      have hz : |b i v| = 0 :=
        le_antisymm (le_of_not_gt hp) (abs_nonneg _)
      have hbzero : b i = 0 := by
        ext w
        change b i w = 0
        apply abs_eq_zero.mp
        exact le_antisymm
          ((hmax w (Finset.mem_univ w)).trans_eq hz) (abs_nonneg _)
      exact (b.orthonormal.ne_zero i) hbzero
    have heq : (∑ w ∈ G.neighborFinset v, b i w) = f i * b i v := by
      have he := congrFun (hA.mulVec_eigenvectorBasis i) v
      simpa only [A, b, f, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul] using he
    have hmul : |f i| * |b i v| ≤ 2 * |b i v| := by
      calc
        _ = |∑ w ∈ G.neighborFinset v, b i w| := by rw [heq, abs_mul]
        _ ≤ ∑ w ∈ G.neighborFinset v, |b i w| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |b i v| :=
          Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
        _ = (G.degree v : ℝ) * |b i v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            G.card_neighborFinset_eq_degree]
        _ ≤ 2 * |b i v| :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (G.degree_le_maxDegree v).trans hDelta)
            (abs_nonneg _)
    exact (mul_le_mul_iff_left₀ hpos).mp hmul
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
  have hspec : A = φ (Matrix.diagonal f) := by
    simpa only [φ, f, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hA.spectral_theorem
  have htr (M : Matrix V V ℝ) : Matrix.trace (φ M) = Matrix.trace M := by
    change Matrix.trace ((hA.eigenvectorUnitary : Matrix V V ℝ) * M *
      (star hA.eigenvectorUnitary : Matrix V V ℝ)) = Matrix.trace M
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have htracepow (k : ℕ) : Matrix.trace (A ^ k) = ∑ v : V, f v ^ k := by
    calc
      _ = Matrix.trace (φ (Matrix.diagonal f ^ k)) := by
        rw [map_pow, ← hspec]
      _ = Matrix.trace (Matrix.diagonal f ^ k) := htr _
      _ = _ := by simp [Matrix.diagonal_pow]
  have hdegSum : (∑ v : V, (G.degree v : ℝ)) = n * a := by
    calc
      _ = q := by
        dsimp only [q]
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ = n * a := hna.symm
  have hF2 : (∑ v : V, f v ^ 2) = n * a := by
    rw [← htracepow 2, pow_two]
    calc
      Matrix.trace (A * A) = ∑ v : V, (G.degree v : ℝ) := by
        simp only [A, Matrix.trace, Matrix.diag_apply,
          G.adjMatrix_mul_self_apply_self]
      _ = n * a := hdegSum
  let s : ℝ := ∑ v : V, (G.degree v : ℝ) ^ 2
  have hS : n * a ^ 2 ≤ s := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset V) (fun _ => (1 : ℝ))
      (fun v => (G.degree v : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hCS
    rw [hdegSum] at hCS
    change (n * a) ^ 2 ≤ n * s at hCS
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith only [hCS]
  let B : Matrix V V ℝ := A * A
  let C : Matrix V V ℕ := G.adjMatrix ℕ * G.adjMatrix ℕ
  have hcast (u v : V) : (C u v : ℝ) = B u v := by
    simp only [C, B, A, Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul,
      SimpleGraph.adjMatrix_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hBsq (u v : V) : B u v ≤ B u v ^ 2 := by
    by_cases hz : C u v = 0
    · rw [← hcast u v, hz]
      norm_num
    · have hc : 1 ≤ C u v := by omega
      have hr : (1 : ℝ) ≤ B u v := by
        rw [← hcast u v]
        exact_mod_cast hc
      have hp := mul_nonneg (sub_nonneg.mpr hr)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hr)
      nlinarith only [hp]
  have hBdiag (u : V) : B u u = (G.degree u : ℝ) :=
    G.adjMatrix_mul_self_apply_self u
  have hBT : Matrix.transpose B = B := by
    simp only [B, A, Matrix.transpose_mul, SimpleGraph.transpose_adjMatrix]
  have hBsym (u v : V) : B v u = B u v :=
    congrFun (congrFun hBT u) v
  have hAsym (u v : V) : A v u = A u v :=
    (G.isSymm_adjMatrix (α := ℝ)).apply u v
  have hrow (u : V) : (∑ v : V, A u v) = (G.degree u : ℝ) := by
    simpa only [A, SimpleGraph.adjMatrix_apply]
      using (G.degree_eq_sum_if_adj (R := ℝ) u).symm
  have hcol (v : V) : (∑ u : V, A u v) = (G.degree v : ℝ) := by
    calc
      _ = ∑ u : V, A v u :=
        Finset.sum_congr rfl (fun u _ => hAsym v u)
      _ = _ := hrow v
  have hallB : (∑ u : V, ∑ v : V, B u v) = s := by
    calc
      _ = ∑ u : V, ∑ v : V, ∑ w : V, A u w * A w v := by
        simp only [B, Matrix.mul_apply]
      _ = ∑ u : V, ∑ w : V, ∑ v : V, A u w * A w v := by
        apply Finset.sum_congr rfl
        intro u _
        exact Finset.sum_comm
      _ = ∑ w : V, ∑ u : V, ∑ v : V, A u w * A w v :=
        Finset.sum_comm
      _ = ∑ w : V, (∑ u : V, A u w) * (∑ v : V, A w v) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ = s := by simp only [hcol, hrow, s, pow_two]
  have hFourth : (∑ v : V, f v ^ 4) =
      ∑ u : V, ∑ v : V, B u v ^ 2 := by
    have hp : A ^ 4 = B * B := by
      calc
        A ^ 4 = A ^ (2 + 2) := rfl
        _ = A ^ 2 * A ^ 2 := pow_add A 2 2
        _ = B * B := by simp only [B, pow_two]
    calc
      _ = Matrix.trace (A ^ 4) := (htracepow 4).symm
      _ = Matrix.trace (B * B) := congrArg Matrix.trace hp
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        rw [hBsym u v, pow_two]
  have hpoint (u v : V) :
      B u v + (if u = v then (G.degree u : ℝ) ^ 2 - (G.degree u : ℝ)
        else 0) ≤ B u v ^ 2 := by
    by_cases huv : u = v
    · subst v
      simp only [if_pos rfl, hBdiag, ite_true]
      nlinarith only []
    · rw [if_neg huv, add_zero]
      exact hBsq u v
  have hF4bound : 2 * s - n * a ≤ ∑ v : V, f v ^ 4 := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (fun u _ => Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun v _ => hpoint u v))
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.sum_sub_distrib] at h
    rw [hallB, hdegSum, ← hFourth] at h
    change s + (s - n * a) ≤ ∑ v : V, f v ^ 4 at h
    linarith only [h]
  let δ : ℝ := ∑ v : V, (f v ^ 2 - a) ^ 2
  have hδ : δ = (∑ v : V, f v ^ 4) - n * a ^ 2 := by
    have ht (v : V) : (f v ^ 2 - a) ^ 2 =
        f v ^ 4 - 2 * a * f v ^ 2 + a ^ 2 := by ring
    dsimp only [δ]
    simp only [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hF2]
    change (∑ v : V, f v ^ 4) - 2 * a * (n * a) + n * a ^ 2 =
      (∑ v : V, f v ^ 4) - n * a ^ 2
    ring
  have hδlower : n * a * (a - 1) ≤ δ := by
    rw [hδ]
    nlinarith only [hF4bound, hS]
  have hscalar (i : V) :
      2 * r * |f i| ≤ f i ^ 2 + a - (r / 24) * (f i ^ 2 - a) ^ 2 := by
    let t : ℝ := |f i|
    have ht0 : 0 ≤ t := abs_nonneg _
    have ht2 : t ≤ 2 := hfbound i
    have hsum0 : 0 ≤ t + r := add_nonneg ht0 hrnonneg
    have hsum4 : t + r ≤ 4 := by linarith only [ht2, hrle]
    have hsquare : (t + r) ^ 2 ≤ 16 := by
      have hp := mul_nonneg (sub_nonneg.mpr hsum4)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 4) hsum0)
      nlinarith only [hp]
    have hcoef : r * (t + r) ^ 2 ≤ 24 := by
      calc
        _ ≤ r * 16 := mul_le_mul_of_nonneg_left hsquare hrnonneg
        _ ≤ 24 := by linarith only [hrle]
    have hp := mul_nonneg (sq_nonneg (t - r)) (sub_nonneg.mpr hcoef)
    have ht : 2 * r * t ≤ t ^ 2 + a - (r / 24) * (t ^ 2 - a) ^ 2 := by
      rw [← hrsq]
      nlinarith only [hp]
    simpa only [t, sq_abs] using ht
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun i _ => hscalar i)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hF2] at hsum
  change 2 * r * E ≤ n * a + n * a - (r / 24) * δ at hsum
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrpos)).mp
  calc
    (2 * r) * E ≤ n * a + n * a - (r / 24) * δ := hsum
    _ ≤ n * a + n * a - (r / 24) * (n * a * (a - 1)) :=
      sub_le_sub_left
        (mul_le_mul_of_nonneg_left hδlower
          (div_nonneg hrnonneg (by norm_num))) _
    _ = (2 * r) * (n * r - (n * a * (a - 1)) / 48) := by
      rw [← hrsq]
      ring

theorem model_f1abeb346d4f50c57240 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) := by
  classical
  rcases h_guard with ⟨hc, ⟨d, hd⟩, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hn : Fintype.card V ≤ 1 := by omega
    have hnr : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
  have hsum_real : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn0
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff hcard).2
    exact hsum_real.symm.trans (mul_comm _ _)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let N : Matrix V V ℝ := D * G.lapMatrix ℝ * Matrix.conjTranspose D
  let hN : N.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  simp only [if_neg hn0, if_pos hc, dif_pos htwo]
  change (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥
    (2 * ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) *
      (1 + max 0 (1 - hN.eigenvalues₀ j))
  rw [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : D = (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix V V ℝ) := by
    simp only [D, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hcoef : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hdnonneg]
  have hNsmul : N = (d : ℝ)⁻¹ • G.lapMatrix ℝ := by
    simp only [N, hD, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hcoef]
  have hdN : (d : ℝ) • N = G.lapMatrix ℝ := by
    rw [hNsmul, smul_smul, mul_inv_cancel₀ hdne, one_smul]
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    simp only [SimpleGraph.degMatrix, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hA : G.adjMatrix ℝ =
      (d : ℝ) • (1 : Matrix V V ℝ) - (d : ℝ) • N := by
    rw [hdN, SimpleGraph.lapMatrix, hdeg]
    abel
  let m : V → ℝ := fun v => (d : ℝ) * (1 - hN.eigenvalues v)
  let U := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hN.eigenvectorUnitary
  have hspec : N = U (Matrix.diagonal hN.eigenvalues) := by
    simpa [U] using hN.spectral_theorem
  have hdiag : Matrix.diagonal m =
      (d : ℝ) • (1 : Matrix V V ℝ) -
        (d : ℝ) • Matrix.diagonal hN.eigenvalues := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext v
    simp only [m, Pi.smul_apply, smul_eq_mul]
    ring
  have hAconj : G.adjMatrix ℝ = U (Matrix.diagonal m) := by
    rw [hdiag]
    simpa only [map_sub, map_smul, map_one, ← hspec] using hA
  have hcp : (G.adjMatrix ℝ).charpoly = (Matrix.diagonal m).charpoly := by
    rw [hAconj]
    change (((hN.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal m) *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)).charpoly =
        (Matrix.diagonal m).charpoly
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hroots :
      (Finset.univ : Finset V).val.map (G.isHermitian_adjMatrix ℝ).eigenvalues =
        (Finset.univ : Finset V).val.map m := by
    calc
      _ = (G.adjMatrix ℝ).charpoly.roots := by
        simpa using (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues.symm
      _ = (Matrix.diagonal m).charpoly.roots :=
        congrArg (fun p : Polynomial ℝ => p.roots) hcp
      _ = (Finset.univ : Finset V).val.map m := by
        rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
        · simp
        · exact Finset.prod_ne_zero_iff.mpr
            (fun v _ => Polynomial.X_sub_C_ne_zero (m v))
  have hsum : (∑ v : V, m v) = 0 := by
    have h := congrArg Multiset.sum hroots
    simp only [Finset.sum_map_val] at h
    rw [← h]
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have henergy : (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
      ∑ v : V, |m v| := by
    have h := congrArg
      (fun s : Multiset ℝ => (s.map (fun x : ℝ => |x|)).sum) hroots
    simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply] using h
  have hPSD : N.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg (v : V) : 0 ≤ hN.eigenvalues v := by
    rw [hN.eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hN.eigenvectorBasis v))
  have hzero : (0 : ℝ) ∈ spectrum ℝ N := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : V → ℝ))
      ⟨Module.End.mem_genEigenspace_one.mpr ?_, by simp⟩
    simp only [Matrix.toLin'_apply, hNsmul, Matrix.smul_mulVec,
      G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, zero_smul]
  rw [hN.spectrum_real_eq_range_eigenvalues] at hzero
  obtain ⟨z, hz⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have heig (i : Fin (Fintype.card V)) :
      hN.eigenvalues (e i) = hN.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hk0 : hN.eigenvalues₀ k = 0 := by
    have hk_nonneg : 0 ≤ hN.eigenvalues₀ k := by
      simpa only [heig] using hnonneg (e k)
    change hN.eigenvalues₀ (e.symm z) = 0 at hz
    have hzk : e.symm z ≤ k := by
      change (e.symm z).val ≤ Fintype.card V - 1
      have hzlt := (e.symm z).isLt
      omega
    exact le_antisymm ((hN.eigenvalues₀_antitone hzk).trans_eq hz) hk_nonneg
  have hmu_k : m (e k) = (d : ℝ) := by
    simp only [m, heig, hk0, sub_zero, mul_one]
  have hmu_j : m (e j) = (d : ℝ) * (1 - hN.eigenvalues₀ j) := by
    simp only [m, heig]
  have hne : e k ≠ e j := by
    intro h
    have hkj := e.injective h
    have hv := congrArg Fin.val hkj
    dsimp only [k, j] at hv
    omega
  have hpoint (v : V) : 0 ≤ |m v| + m v := by
    linarith [neg_abs_le (m v)]
  have hpair : (|m (e k)| + m (e k)) + (|m (e j)| + m (e j)) ≤
      ∑ v : V, (|m v| + m v) := by
    calc
      _ = ∑ v ∈ ({e k, e j} : Finset V), (|m v| + m v) :=
        (Finset.sum_pair hne).symm
      _ ≤ ∑ v : V, (|m v| + m v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ => hpoint v)
  simp only [Finset.sum_add_distrib, hsum, add_zero] at hpair
  simp only [hmu_k, hmu_j, abs_of_nonneg hdnonneg] at hpair
  rw [henergy]
  by_cases ht : 0 ≤ 1 - hN.eigenvalues₀ j
  · rw [max_eq_right ht]
    have hp : 0 ≤ (d : ℝ) * (1 - hN.eigenvalues₀ j) := mul_nonneg hdnonneg ht
    rw [abs_of_nonneg hp] at hpair
    nlinarith only [hpair]
  · have ht' : 1 - hN.eigenvalues₀ j ≤ 0 := (lt_of_not_ge ht).le
    rw [max_eq_left ht']
    have hp : (d : ℝ) * (1 - hN.eigenvalues₀ j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdnonneg ht'
    rw [abs_of_nonpos hp] at hpair
    nlinarith only [hpair]

theorem model_6bde2f687ba9b3e6e8a5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (max (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) ((((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * (((Fintype.card V : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))) / (max (1 : ℝ) ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))))) := by
  classical
  refine max_le (model_f1abeb346d4f50c57240 G h_guard) ?_
  rcases h_guard with ⟨hc, ⟨d, hd⟩, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hn : Fintype.card V ≤ 1 := by omega
    have hnr : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
  have hsum_real : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn0
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff hcard).2
    exact hsum_real.symm.trans (mul_comm _ _)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let N : Matrix V V ℝ := D * G.lapMatrix ℝ * Matrix.conjTranspose D
  let hN : N.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  simp only [if_neg hn0, if_pos hc, dif_pos htwo]
  change (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥
    (2 * ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) *
      (((Fintype.card V : ℝ) -
          (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
        ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
          max 0 (1 - hN.eigenvalues₀ j)) /
      max 1
        ((sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
          ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
            max 0 (1 - hN.eigenvalues₀ j))
  simp only [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul, zero_div]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : D = (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix V V ℝ) := by
    simp only [D, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hcoef : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hdnonneg]
  have hNsmul : N = (d : ℝ)⁻¹ • G.lapMatrix ℝ := by
    simp only [N, hD, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hcoef]
  have hdN : (d : ℝ) • N = G.lapMatrix ℝ := by
    rw [hNsmul, smul_smul, mul_inv_cancel₀ hdne, one_smul]
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    simp only [SimpleGraph.degMatrix, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hA : G.adjMatrix ℝ =
      (d : ℝ) • (1 : Matrix V V ℝ) - (d : ℝ) • N := by
    rw [hdN, SimpleGraph.lapMatrix, hdeg]
    abel
  let m : V → ℝ := fun v => (d : ℝ) * (1 - hN.eigenvalues v)
  let U := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hN.eigenvectorUnitary
  have hspec : N = U (Matrix.diagonal hN.eigenvalues) := by
    simpa [U] using hN.spectral_theorem
  have hdiag : Matrix.diagonal m =
      (d : ℝ) • (1 : Matrix V V ℝ) -
        (d : ℝ) • Matrix.diagonal hN.eigenvalues := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext v
    simp only [m, Pi.smul_apply, smul_eq_mul]
    ring
  have hAconj : G.adjMatrix ℝ = U (Matrix.diagonal m) := by
    rw [hdiag]
    simpa only [map_sub, map_smul, map_one, ← hspec] using hA
  have hcp : (G.adjMatrix ℝ).charpoly = (Matrix.diagonal m).charpoly := by
    rw [hAconj]
    change (((hN.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal m) *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)).charpoly =
        (Matrix.diagonal m).charpoly
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hroots :
      (Finset.univ : Finset V).val.map (G.isHermitian_adjMatrix ℝ).eigenvalues =
        (Finset.univ : Finset V).val.map m := by
    calc
      _ = (G.adjMatrix ℝ).charpoly.roots := by
        simpa using (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues.symm
      _ = (Matrix.diagonal m).charpoly.roots :=
        congrArg (fun p : Polynomial ℝ => p.roots) hcp
      _ = (Finset.univ : Finset V).val.map m := by
        rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
        · simp
        · exact Finset.prod_ne_zero_iff.mpr
            (fun v _ => Polynomial.X_sub_C_ne_zero (m v))
  have hsum : (∑ v : V, m v) = 0 := by
    have h := congrArg Multiset.sum hroots
    simp only [Finset.sum_map_val] at h
    rw [← h]
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have henergy : (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
      ∑ v : V, |m v| := by
    have h := congrArg
      (fun s : Multiset ℝ => (s.map (fun x : ℝ => |x|)).sum) hroots
    simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply] using h
  have hrange : Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues =
      Set.range m := by
    ext x
    have hx := congrArg (fun s : Multiset ℝ => x ∈ s) hroots
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and, Set.mem_range] using (Iff.of_eq hx)
  have htr (B : Matrix V V ℝ) : Matrix.trace (U B) = Matrix.trace B := by
    change Matrix.trace ((hN.eigenvectorUnitary : Matrix V V ℝ) * B *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hAA : G.adjMatrix ℝ * G.adjMatrix ℝ =
      U (Matrix.diagonal m * Matrix.diagonal m) := by
    rw [map_mul, ← hAconj]
  have hsquare : (∑ v : V, m v ^ 2) =
      (Fintype.card V : ℝ) * (d : ℝ) := by
    calc
      _ = Matrix.trace (Matrix.diagonal m * Matrix.diagonal m) := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]
      _ = Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) := by
        rw [hAA, htr]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self, hd.degree_eq,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hPSD : N.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg (v : V) : 0 ≤ hN.eigenvalues v := by
    rw [hN.eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hN.eigenvectorBasis v))
  have hzero : (0 : ℝ) ∈ spectrum ℝ N := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : V → ℝ))
      ⟨Module.End.mem_genEigenspace_one.mpr ?_, by simp⟩
    simp only [Matrix.toLin'_apply, hNsmul, Matrix.smul_mulVec,
      G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, zero_smul]
  rw [hN.spectrum_real_eq_range_eigenvalues] at hzero
  obtain ⟨z, hz⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have heig (i : Fin (Fintype.card V)) :
      hN.eigenvalues (e i) = hN.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hk0 : hN.eigenvalues₀ k = 0 := by
    have hk_nonneg : 0 ≤ hN.eigenvalues₀ k := by
      simpa only [heig] using hnonneg (e k)
    change hN.eigenvalues₀ (e.symm z) = 0 at hz
    have hzk : e.symm z ≤ k := by
      change (e.symm z).val ≤ Fintype.card V - 1
      have hzlt := (e.symm z).isLt
      omega
    exact le_antisymm ((hN.eigenvalues₀_antitone hzk).trans_eq hz) hk_nonneg
  have hmu_k : m (e k) = (d : ℝ) := by
    simp only [m, heig, hk0, sub_zero, mul_one]
  have hupper (v : V) : m v ≤ (d : ℝ) := by
    have hp := mul_nonneg hdnonneg (hnonneg v)
    dsimp only [m]
    nlinarith only [hp]
  have hmax : sSup (Set.range m) = (d : ℝ) := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty m)
      rintro x ⟨v, rfl⟩
      exact hupper v
    · rw [← hmu_k]
      exact le_csSup (Set.finite_range m).bddAbove ⟨e k, rfl⟩
  let a : ℝ := (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
  let b : ℝ := -sInf (Set.range m)
  let E : ℝ := ∑ v : V, |m v|
  have hEnonneg : 0 ≤ E := Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hlower (v : V) : -b ≤ m v := by
    simpa only [b, neg_neg] using
      (csInf_le (Set.finite_range m).bddBelow
        (show m v ∈ Set.range m from ⟨v, rfl⟩))
  have hcap (v : V) (hv : v ≠ e k) : m v ≤ a := by
    have hidx : e.symm v ≠ k := by
      intro hi
      apply hv
      simpa only [Equiv.apply_symm_apply] using congrArg e hi
    have hi : e.symm v ≤ j := by
      have hlt := (e.symm v).isLt
      have hval : (e.symm v).val ≠ Fintype.card V - 1 := by
        intro h
        exact hidx (Fin.ext h)
      change (e.symm v).val ≤ Fintype.card V - 2
      omega
    have hEigOrder := hN.eigenvalues₀_antitone hi
    change hN.eigenvalues₀ j ≤ hN.eigenvalues v at hEigOrder
    change (d : ℝ) * (1 - hN.eigenvalues v) ≤
      (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
    exact mul_le_mul_of_nonneg_left
      ((sub_le_sub_left hEigOrder 1).trans (le_max_right _ _)) hdnonneg
  have hpoint (v : V) : m v ^ 2 ≤
      (a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
        (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0) := by
    by_cases hv : v = e k
    · rw [hv, if_pos rfl, hmu_k, abs_of_nonneg hdnonneg]
      nlinarith only []
    · rw [if_neg hv, add_zero]
      by_cases hm : 0 ≤ m v
      · rw [abs_of_nonneg hm]
        have hp := mul_nonneg (sub_nonneg.mpr (hcap v hv)) hm
        nlinarith only [hp]
      · have hm' : m v ≤ 0 := (lt_of_not_ge hm).le
        rw [abs_of_nonpos hm']
        have hp := mul_nonneg
          (show 0 ≤ m v + b by linarith only [hlower v])
          (neg_nonneg.mpr hm')
        nlinarith only [hp]
  have hquad : (Fintype.card V : ℝ) * (d : ℝ) ≤
      (a + b) * E / 2 + (d : ℝ) ^ 2 - a * (d : ℝ) := by
    calc
      _ = ∑ v : V, m v ^ 2 := hsquare.symm
      _ ≤ ∑ v : V,
          ((a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
            (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0)) :=
        Finset.sum_le_sum (fun v _ => hpoint v)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_div, ← Finset.mul_sum, hsum, add_zero, sub_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, E]
        ring
  have hmono : (b + a) * E ≤ max 1 (b + a) * E :=
    mul_le_mul_of_nonneg_right (le_max_right 1 (b + a)) hEnonneg
  have hprod : (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) ≤
      E * max 1 (b + a) := by
    nlinarith only [hquad, hmono]
  have hdenpos : (0 : ℝ) < max 1 (b + a) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 (b + a))
  have hsecond :
      (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
        max 1 (b + a) ≤ E :=
    (div_le_iff₀ hdenpos).2 hprod
  rw [henergy, hrange, hmax]
  change E ≥
    (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
      max 1 (((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a)
  have hdenexpr : ((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a = b + a := by
    dsimp only [b]
    ring
  rw [hdenexpr]
  exact hsecond

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

theorem gutman_energy_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
      (G.adjMatrix ℝ).toEuclideanLin
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
    let r : ℝ := sSup (Set.range f)
    have hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    have heig (i : V) : T (b i) = f i • b i := by
      apply WithLp.ofLp_injective 2
      change Matrix.mulVec (G.adjMatrix ℝ)
          (⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i •
          ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
      exact (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
    have hquad : inner ℝ (T x) x =
        ∑ i : V, f i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      apply Finset.sum_congr rfl
      intro i _
      rw [hT x (b i), heig i, real_inner_smul_right,
        real_inner_comm x (b i)]
      ring
    have hnorm : ‖x‖ ^ 2 = (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [x, PiLp.toLp_apply]
    have hcount : inner ℝ (T x) x = 2 * (G.edgeFinset.card : ℝ) := by
      calc
        inner ℝ (T x) x = ∑ v : V, (G.degree v : ℝ) := by
          rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
          change dotProduct
              (Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)))
              (star (fun _ : V => (1 : ℝ))) =
            ∑ v : V, (G.degree v : ℝ)
          simp [dotProduct]
        _ = 2 * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : inner ℝ (T x) x ≤ r * ‖x‖ ^ 2 := by
      rw [hquad, ← b.sum_sq_inner_right x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (le_csSup (Set.finite_range f).bddAbove ⟨i, rfl⟩)
        (sq_nonneg _)
    rw [hcount, hnorm] at hbound
    have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        (Fintype.card V : ℝ) ≤ r :=
      (div_le_iff₀ hcard).2 hbound
    have henergy : 2 * r ≤
        ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v| := by
      simpa only [r, f, if_neg hV] using graph_energy_spectral_radius_lower G
    rw [if_neg hV]
    exact (mul_le_mul_of_nonneg_left havg (by norm_num : (0 : ℝ) ≤ 2)).trans henergy

theorem koolen_moulton_order_2003 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((Fintype.card V : ℝ) / (2 : ℝ)) * ((1 : ℝ) + (Real.sqrt (Fintype.card V : ℝ)))) := by
  classical
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let U : Matrix.unitaryGroup V ℝ := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  let s : V → ℝ := fun i => if 0 ≤ f i then 1 else -1
  let S : Matrix V V ℝ := φ (Matrix.diagonal s)
  let N : ℝ := Fintype.card V
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hs (i : V) : s i * s i = 1 := by
    by_cases hi : 0 ≤ f i <;> simp [s, hi]
  have hsabs (i : V) : f i * s i = |f i| := by
    by_cases hi : 0 ≤ f i
    · simp [s, hi, abs_of_nonneg hi]
    · simp [s, hi, abs_of_neg (lt_of_not_ge hi)]
  have htr (B : Matrix V V ℝ) : Matrix.trace (φ B) = Matrix.trace B := by
    change Matrix.trace ((U : Matrix V V ℝ) * B *
      (star U : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hSS : S * S = 1 := by
    have hd : Matrix.diagonal s * Matrix.diagonal s = (1 : Matrix V V ℝ) := by
      simp only [Matrix.diagonal_mul_diagonal, hs, Matrix.diagonal_one]
    change φ (Matrix.diagonal s) * φ (Matrix.diagonal s) = 1
    rw [← map_mul, hd, map_one]
  have hST : Matrix.transpose S = S := by
    have hstar : star S = S := by
      change star (φ (Matrix.diagonal s)) = φ (Matrix.diagonal s)
      rw [← map_star, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, star_trivial]
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hstar
  have hsym (i j : V) : S j i = S i j :=
    congrFun (congrFun hST i) j
  have henergy : Matrix.trace (A * S) = ∑ i : V, |f i| := by
    have hspec : A = φ (Matrix.diagonal f) := by
      simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
    calc
      Matrix.trace (A * S) =
          Matrix.trace (φ (Matrix.diagonal f * Matrix.diagonal s)) := by
        rw [hspec]
        change Matrix.trace (φ (Matrix.diagonal f) * φ (Matrix.diagonal s)) =
          Matrix.trace (φ (Matrix.diagonal f * Matrix.diagonal s))
        rw [map_mul]
      _ = Matrix.trace (Matrix.diagonal f * Matrix.diagonal s) := htr _
      _ = ∑ i : V, |f i| := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, hsabs]
  have hSsq : (∑ i : V, ∑ j : V, (S i j) ^ 2) = N := by
    calc
      (∑ i : V, ∑ j : V, (S i j) ^ 2) = Matrix.trace (S * S) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym i j, pow_two]
      _ = N := by simpa only [hSS, Matrix.trace_one, N]
  let r : V → ℝ := fun i => ∑ j : V, S i j
  have hr : (∑ i : V, (r i) ^ 2) = N := by
    let x : V → ℝ := fun _ => 1
    have hx : Matrix.mulVec S x = r := by
      funext i
      simp [Matrix.mulVec, dotProduct, x, r]
    calc
      (∑ i : V, (r i) ^ 2) =
          dotProduct (Matrix.mulVec S x) (Matrix.mulVec S x) := by
        rw [hx]
        simp only [dotProduct, pow_two]
      _ = dotProduct x (Matrix.mulVec (Matrix.transpose S) (Matrix.mulVec S x)) :=
        (Matrix.dotProduct_transpose_mulVec S x (Matrix.mulVec S x)).symm
      _ = dotProduct x x := by
        rw [Matrix.mulVec_mulVec, hST, hSS, Matrix.one_mulVec]
      _ = N := by simp [dotProduct, x, N]
  have hJ : (∑ i : V, r i) ≤ N := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset V) (fun _ => (1 : ℝ)) r
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hr] at hc
    have hsq : (∑ i : V, r i) ^ 2 ≤ N ^ 2 := by
      simpa only [pow_two] using hc
    exact le_of_sq_le_sq hsq hN
  let B : Matrix V V ℝ := Matrix.of (fun i j => A i j - (1 / 2 : ℝ))
  have hBentry (i j : V) : (B i j) ^ 2 = (1 / 4 : ℝ) := by
    change (G.adjMatrix ℝ i j - (1 / 2 : ℝ)) ^ 2 = (1 / 4 : ℝ)
    rcases (G.isAdjMatrix_adjMatrix ℝ).zero_or_one i j with hij | hij
      <;> rw [hij] <;> norm_num
  have hBsqPair : (∑ p : V × V, (B p.1 p.2) ^ 2) = (N / 2) ^ 2 := by
    calc
      (∑ p : V × V, (B p.1 p.2) ^ 2) = (N * N) * (1 / 4 : ℝ) := by
        simp only [hBentry, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_prod, Nat.cast_mul, N]
      _ = (N / 2) ^ 2 := by ring
  have hSsqPair : (∑ p : V × V, (S p.1 p.2) ^ 2) = N := by
    simpa only [Fintype.sum_prod_type] using hSsq
  let C : ℝ := ∑ p : V × V, B p.1 p.2 * S p.1 p.2
  have hC : C ≤ N / 2 * Real.sqrt N := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (V × V))
      (fun p => B p.1 p.2) (fun p => S p.1 p.2)
    have hsq : C ^ 2 ≤ (N / 2 * Real.sqrt N) ^ 2 := by
      calc
        C ^ 2 ≤ (N / 2) ^ 2 * N := by
          simpa only [hBsqPair, hSsqPair] using hc
        _ = (N / 2 * Real.sqrt N) ^ 2 := by
          symm
          rw [mul_pow, Real.sq_sqrt hN]
    exact le_of_sq_le_sq hsq
      (mul_nonneg (div_nonneg hN (by norm_num)) (Real.sqrt_nonneg N))
  have hdecomp : (∑ i : V, |f i|) = C + (1 / 2 : ℝ) * (∑ i : V, r i) := by
    rw [← henergy]
    calc
      Matrix.trace (A * S) = ∑ i : V, ∑ j : V, A i j * S i j := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym i j]
      _ = (∑ i : V, ∑ j : V, B i j * S i j) +
          (1 / 2 : ℝ) * (∑ i : V, ∑ j : V, S i j) := by
        have hterm (i j : V) :
            A i j * S i j = B i j * S i j + (1 / 2 : ℝ) * S i j := by
          change A i j * S i j =
            (A i j - (1 / 2 : ℝ)) * S i j + (1 / 2 : ℝ) * S i j
          ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = C + (1 / 2 : ℝ) * (∑ i : V, r i) := by
        simp only [C, r, Fintype.sum_prod_type]
  change (∑ i : V, |f i|) ≤ N / 2 * (1 + Real.sqrt N)
  calc
    (∑ i : V, |f i|) = C + (1 / 2 : ℝ) * (∑ i : V, r i) := hdecomp
    _ ≤ N / 2 * Real.sqrt N + (1 / 2 : ℝ) * N :=
      add_le_add hC (mul_le_mul_of_nonneg_left hJ (by norm_num))
    _ = N / 2 * (1 + Real.sqrt N) := by ring

theorem mcclelland_graph_energy_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  classical
  have hsq :
      (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2 ≤
        (2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) * ((Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ)) :=
        model_081bc55d24f66b98c45d G
      _ = _ := by ring
  calc
    _ ≤ |(∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)| :=
      le_abs_self _
    _ = Real.sqrt ((∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq
theorem model_63aaabca8d79723937de {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((Fintype.card V : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) - ((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) / (max (1 : ℝ) (((2 : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) * (((G.maxDegree : ℝ) + (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) ^ 2))))) := by
  classical
  by_cases hn0 : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    simp [hn0]
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  let n : ℝ := Fintype.card V
  let q : ℝ := 2 * (G.edgeFinset.card : ℝ)
  let a : ℝ := q / n
  let r : ℝ := Real.sqrt a
  let E : ℝ := ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|
  let Δ : ℝ := G.maxDegree
  let c : ℝ := (Δ + r) ^ 2
  let K : ℝ := max 1 (2 * r * c)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnne : n ≠ 0 := ne_of_gt hn
  have ha : 0 ≤ a :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
  have hna : n * a = q := by
    have h : q = a * n :=
      (div_eq_iff hnne).mp (show q / n = a from rfl)
    exact (mul_comm n a).trans h.symm
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg a
  have hrsq : r ^ 2 = a := Real.sq_sqrt ha
  have hΔnonneg : 0 ≤ Δ := Nat.cast_nonneg _
  simp only [if_neg hn0]
  change E ≤ n * r - (n * a * (a - 1)) / K
  have hMc : E ≤ n * r := by
    apply le_of_sq_le_sq ?_ (mul_nonneg hn.le hrnonneg)
    calc
      E ^ 2 ≤ 2 * (n * (G.edgeFinset.card : ℝ)) :=
        model_081bc55d24f66b98c45d G
      _ = n * q := by dsimp only [q]; ring
      _ = (n * r) ^ 2 := by
        rw [← hna, mul_pow, hrsq]
        ring
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let b := hA.eigenvectorBasis
  have hfbound (i : V) : |f i| ≤ Δ := by
    obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset V) (fun v => |b i v|) Finset.univ_nonempty
    have hpos : 0 < |b i v| := by
      by_contra hp
      have hz : |b i v| = 0 :=
        le_antisymm (le_of_not_gt hp) (abs_nonneg _)
      have hbzero : b i = 0 := by
        ext w
        change b i w = 0
        apply abs_eq_zero.mp
        exact le_antisymm
          ((hmax w (Finset.mem_univ w)).trans_eq hz) (abs_nonneg _)
      exact (b.orthonormal.ne_zero i) hbzero
    have heq : (∑ w ∈ G.neighborFinset v, b i w) = f i * b i v := by
      have he := congrFun (hA.mulVec_eigenvectorBasis i) v
      simpa only [A, b, f, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul] using he
    have hmul : |f i| * |b i v| ≤ Δ * |b i v| := by
      calc
        _ = |∑ w ∈ G.neighborFinset v, b i w| := by rw [heq, abs_mul]
        _ ≤ ∑ w ∈ G.neighborFinset v, |b i w| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |b i v| :=
          Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
        _ = (G.degree v : ℝ) * |b i v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            G.card_neighborFinset_eq_degree]
        _ ≤ Δ * |b i v| :=
          mul_le_mul_of_nonneg_right
            (by
              dsimp only [Δ]
              exact_mod_cast G.degree_le_maxDegree v)
            (abs_nonneg _)
    exact (mul_le_mul_iff_left₀ hpos).mp hmul
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
  have hspec : A = φ (Matrix.diagonal f) := by
    simpa only [φ, f, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hA.spectral_theorem
  have htr (M : Matrix V V ℝ) : Matrix.trace (φ M) = Matrix.trace M := by
    change Matrix.trace ((hA.eigenvectorUnitary : Matrix V V ℝ) * M *
      (star hA.eigenvectorUnitary : Matrix V V ℝ)) = Matrix.trace M
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have htracepow (k : ℕ) : Matrix.trace (A ^ k) = ∑ v : V, f v ^ k := by
    calc
      _ = Matrix.trace (φ (Matrix.diagonal f ^ k)) := by
        rw [map_pow, ← hspec]
      _ = Matrix.trace (Matrix.diagonal f ^ k) := htr _
      _ = _ := by simp [Matrix.diagonal_pow]
  have hdegSum : (∑ v : V, (G.degree v : ℝ)) = n * a := by
    calc
      _ = q := by
        dsimp only [q]
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ = n * a := hna.symm
  have hF2 : (∑ v : V, f v ^ 2) = n * a := by
    rw [← htracepow 2, pow_two]
    calc
      Matrix.trace (A * A) = ∑ v : V, (G.degree v : ℝ) := by
        simp only [A, Matrix.trace, Matrix.diag_apply,
          G.adjMatrix_mul_self_apply_self]
      _ = n * a := hdegSum
  let s : ℝ := ∑ v : V, (G.degree v : ℝ) ^ 2
  have hS : n * a ^ 2 ≤ s := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset V) (fun _ => (1 : ℝ))
      (fun v => (G.degree v : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hCS
    rw [hdegSum] at hCS
    change (n * a) ^ 2 ≤ n * s at hCS
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith only [hCS]
  let B : Matrix V V ℝ := A * A
  let C : Matrix V V ℕ := G.adjMatrix ℕ * G.adjMatrix ℕ
  have hcast (u v : V) : (C u v : ℝ) = B u v := by
    simp only [C, B, A, Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul,
      SimpleGraph.adjMatrix_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hBsq (u v : V) : B u v ≤ B u v ^ 2 := by
    by_cases hz : C u v = 0
    · rw [← hcast u v, hz]
      norm_num
    · have hc : 1 ≤ C u v := by omega
      have hr : (1 : ℝ) ≤ B u v := by
        rw [← hcast u v]
        exact_mod_cast hc
      have hp := mul_nonneg (sub_nonneg.mpr hr)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hr)
      nlinarith only [hp]
  have hBdiag (u : V) : B u u = (G.degree u : ℝ) :=
    G.adjMatrix_mul_self_apply_self u
  have hBT : Matrix.transpose B = B := by
    simp only [B, A, Matrix.transpose_mul, SimpleGraph.transpose_adjMatrix]
  have hBsym (u v : V) : B v u = B u v :=
    congrFun (congrFun hBT u) v
  have hAsym (u v : V) : A v u = A u v :=
    (G.isSymm_adjMatrix (α := ℝ)).apply u v
  have hrow (u : V) : (∑ v : V, A u v) = (G.degree u : ℝ) := by
    simpa only [A, SimpleGraph.adjMatrix_apply]
      using (G.degree_eq_sum_if_adj (R := ℝ) u).symm
  have hcol (v : V) : (∑ u : V, A u v) = (G.degree v : ℝ) := by
    calc
      _ = ∑ u : V, A v u :=
        Finset.sum_congr rfl (fun u _ => hAsym v u)
      _ = _ := hrow v
  have hallB : (∑ u : V, ∑ v : V, B u v) = s := by
    calc
      _ = ∑ u : V, ∑ v : V, ∑ w : V, A u w * A w v := by
        simp only [B, Matrix.mul_apply]
      _ = ∑ u : V, ∑ w : V, ∑ v : V, A u w * A w v := by
        apply Finset.sum_congr rfl
        intro u _
        exact Finset.sum_comm
      _ = ∑ w : V, ∑ u : V, ∑ v : V, A u w * A w v :=
        Finset.sum_comm
      _ = ∑ w : V, (∑ u : V, A u w) * (∑ v : V, A w v) := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
      _ = s := by simp only [hcol, hrow, s, pow_two]
  have hFourth : (∑ v : V, f v ^ 4) =
      ∑ u : V, ∑ v : V, B u v ^ 2 := by
    have hp : A ^ 4 = B * B := by
      calc
        A ^ 4 = A ^ (2 + 2) := rfl
        _ = A ^ 2 * A ^ 2 := pow_add A 2 2
        _ = B * B := by simp only [B, pow_two]
    calc
      _ = Matrix.trace (A ^ 4) := (htracepow 4).symm
      _ = Matrix.trace (B * B) := congrArg Matrix.trace hp
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        rw [hBsym u v, pow_two]
  have hpoint (u v : V) :
      B u v + (if u = v then (G.degree u : ℝ) ^ 2 - (G.degree u : ℝ)
        else 0) ≤ B u v ^ 2 := by
    by_cases huv : u = v
    · subst v
      simp only [if_pos rfl, hBdiag, ite_true]
      nlinarith only []
    · rw [if_neg huv, add_zero]
      exact hBsq u v
  have hF4bound : 2 * s - n * a ≤ ∑ v : V, f v ^ 4 := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (fun u _ => Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun v _ => hpoint u v))
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.sum_sub_distrib] at h
    rw [hallB, hdegSum, ← hFourth] at h
    change s + (s - n * a) ≤ ∑ v : V, f v ^ 4 at h
    linarith only [h]
  let δ : ℝ := ∑ v : V, (f v ^ 2 - a) ^ 2
  have hδ : δ = (∑ v : V, f v ^ 4) - n * a ^ 2 := by
    have ht (v : V) : (f v ^ 2 - a) ^ 2 =
        f v ^ 4 - 2 * a * f v ^ 2 + a ^ 2 := by ring
    dsimp only [δ]
    simp only [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hF2]
    change (∑ v : V, f v ^ 4) - 2 * a * (n * a) + n * a ^ 2 =
      (∑ v : V, f v ^ 4) - n * a ^ 2
    ring
  have hδlower : n * a * (a - 1) ≤ δ := by
    rw [hδ]
    nlinarith only [hF4bound, hS]
  have hscalar (i : V) :
      (f i ^ 2 - a) ^ 2 ≤ c * (f i ^ 2 + a - 2 * r * |f i|) := by
    let t : ℝ := |f i|
    have ht0 : 0 ≤ t := abs_nonneg _
    have htΔ : t ≤ Δ := hfbound i
    have hs : (t + r) ^ 2 ≤ (Δ + r) ^ 2 :=
      (sq_le_sq₀ (add_nonneg ht0 hrnonneg)
        (add_nonneg hΔnonneg hrnonneg)).mpr (add_le_add htΔ (le_refl r))
    have ht : t ^ 2 = f i ^ 2 := sq_abs (f i)
    calc
      (f i ^ 2 - a) ^ 2 = (t - r) ^ 2 * (t + r) ^ 2 := by
        rw [← ht, ← hrsq]
        ring
      _ ≤ (t - r) ^ 2 * (Δ + r) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = c * (f i ^ 2 + a - 2 * r * |f i|) := by
        dsimp only [c]
        rw [← ht, ← hrsq]
        change (t - r) ^ 2 * (Δ + r) ^ 2 =
          (Δ + r) ^ 2 * (t ^ 2 + r ^ 2 - 2 * r * t)
        ring
  have hδupper : δ ≤ c * (n * a + n * a - 2 * r * E) := by
    calc
      δ ≤ ∑ i : V, c * (f i ^ 2 + a - 2 * r * |f i|) :=
        Finset.sum_le_sum (fun i _ => hscalar i)
      _ = c * (n * a + n * a - 2 * r * E) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hF2]
        rfl
  have hgap : 0 ≤ n * r - E := sub_nonneg.mpr hMc
  have hKpos : 0 < K :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hKbound : 2 * r * c ≤ K := le_max_right _ _
  have hδgap : δ ≤ K * (n * r - E) := by
    calc
      δ ≤ c * (n * a + n * a - 2 * r * E) := hδupper
      _ = (2 * r * c) * (n * r - E) := by
        rw [← hrsq]
        ring
      _ ≤ K * (n * r - E) :=
        mul_le_mul_of_nonneg_right hKbound hgap
  have hfrac : (n * a * (a - 1)) / K ≤ n * r - E := by
    apply (div_le_iff₀ hKpos).2
    calc
      n * a * (a - 1) ≤ δ := hδlower
      _ ≤ K * (n * r - E) := hδgap
      _ = (n * r - E) * K := mul_comm _ _
  linarith only [hfrac]
