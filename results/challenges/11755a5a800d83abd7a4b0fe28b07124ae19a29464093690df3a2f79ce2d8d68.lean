import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

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
theorem composed_4f819129e1379926 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  sorry
