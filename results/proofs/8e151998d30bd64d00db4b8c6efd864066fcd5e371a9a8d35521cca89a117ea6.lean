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

theorem model_2649c493de46c591f981 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((2 : ℝ) * ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ))) / (3 : ℝ)) := by
  classical
    have hDelta : G.maxDegree ≤ 2 := by
      by_contra h
      have hn : 3 ≤ G.maxDegree := by omega
      have hr : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hn
      linarith
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let f : V → ℝ := hA.eigenvalues
    let b := hA.eigenvectorBasis
    let n : ℝ := Fintype.card V
    let q : ℝ := 2 * (G.edgeFinset.card : ℝ)
    have hfbound (i : V) : |f i| ≤ 2 := by
      obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
        (Finset.univ : Finset V) (fun v => |b i v|)
        ⟨i, Finset.mem_univ i⟩
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
    have hdegSum : (∑ v : V, (G.degree v : ℝ)) = q := by
      dsimp only [q]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hF2 : (∑ v : V, f v ^ 2) = q := by
      rw [← htracepow 2, pow_two]
      calc
        Matrix.trace (A * A) = ∑ v : V, (G.degree v : ℝ) := by
          simp only [A, Matrix.trace, Matrix.diag_apply,
            G.adjMatrix_mul_self_apply_self]
        _ = q := hdegSum
    let s : ℝ := ∑ v : V, (G.degree v : ℝ) ^ 2
    have hdegree (u : V) :
        3 * (G.degree u : ℝ) - 2 ≤ (G.degree u : ℝ) ^ 2 := by
      have hd2 : G.degree u ≤ 2 := (G.degree_le_maxDegree u).trans hDelta
      have hd : G.degree u = 0 ∨ G.degree u = 1 ∨ G.degree u = 2 := by omega
      rcases hd with hd | hd | hd <;> rw [hd] <;> norm_num
    have hS : 3 * q - 2 * n ≤ s := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun u _ => hdegree u)
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hdegSum] at h
      change 3 * q - n * 2 ≤ s at h
      linarith only [h]
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
    have hF4bound : 2 * s - q ≤ ∑ v : V, f v ^ 4 := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
        (fun u _ => Finset.sum_le_sum (s := (Finset.univ : Finset V))
          (fun v _ => hpoint u v))
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Finset.sum_sub_distrib] at h
      rw [hallB, hdegSum, ← hFourth] at h
      change s + (s - q) ≤ ∑ v : V, f v ^ 4 at h
      linarith only [h]
    have hF4 : 5 * q - 4 * n ≤ ∑ v : V, f v ^ 4 := by
      linarith only [hF4bound, hS]
    have hscalar (i : V) :
        18 * |f i| ≤ 8 + 11 * f i ^ 2 - f i ^ 4 := by
      let t : ℝ := |f i|
      have ht0 : 0 ≤ t := abs_nonneg _
      have ht2 : t ≤ 2 := hfbound i
      have hp : 0 ≤ (t - 1) ^ 2 * (2 - t) * (t + 4) :=
        mul_nonneg
          (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ht2))
          (by linarith only [ht0])
      have h2 : t ^ 2 = f i ^ 2 := sq_abs _
      have h4 : t ^ 4 = f i ^ 4 :=
        (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_abs _
      have ht : 18 * t ≤ 8 + 11 * t ^ 2 - t ^ 4 := by
        nlinarith only [hp]
      rw [h2, h4] at ht
      exact ht
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (fun i _ => hscalar i)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hF2] at hsum
    change 18 * (∑ i : V, |f i|) ≤
      n * 8 + 11 * q - (∑ i : V, f i ^ 4) at hsum
    calc
      (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
          ∑ i : V, |f i| := rfl
      _ ≤ (2 * n + q) / 3 := by linarith only [hsum, hF4]
      _ = ((2 : ℝ) * ((Fintype.card V : ℝ) +
          (G.edgeFinset.card : ℝ))) / 3 := by
        dsimp only [n, q]
        ring

theorem model_ec4f3d91aaed60f3f436 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((2 : ℝ) / (3 : ℝ)) * ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ))) := by
  classical
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤
        ((2 : ℝ) * ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ))) / (3 : ℝ) :=
      model_2649c493de46c591f981 G h_guard.2.2
    _ = ((2 : ℝ) / (3 : ℝ)) *
        ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) := by ring
