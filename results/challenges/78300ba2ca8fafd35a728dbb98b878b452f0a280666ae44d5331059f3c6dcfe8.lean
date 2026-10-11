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

theorem composed_b9a7629301cf0891 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  calc
    _ ≤ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) :=
      graph_energy_spectral_radius_lower G
    _ ≤ _ := mcclelland_graph_energy_upper G
theorem composed_a8305e0fa5e3ee71 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  sorry
