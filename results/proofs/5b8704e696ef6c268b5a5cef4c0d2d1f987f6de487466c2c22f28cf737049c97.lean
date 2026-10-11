import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

theorem hull3d_graph_energy_le_0_2_average_degree_size_0_is_regular_99710b2e7422 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨d, hd⟩ := h_guard
  have hbound (i : V) : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (d : ℝ) := by
    let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    obtain ⟨w, _, hw⟩ := Finset.exists_max_image Finset.univ (fun v => |x v|)
      ⟨j, Finset.mem_univ j⟩
    have hwpos : 0 < |x w| :=
      lt_of_lt_of_le (abs_pos.mpr hj) (hw j (Finset.mem_univ j))
    have heq : (∑ u ∈ G.neighborFinset w, x u) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i * x w := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) w
    have hmul : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| ≤
        (d : ℝ) * |x w| := by
      calc
        |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| =
            |∑ u ∈ G.neighborFinset w, x u| := by rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset w, |x u| :=
          Finset.abs_sum_le_sum_abs x (G.neighborFinset w)
        _ ≤ ∑ u ∈ G.neighborFinset w, |x w| :=
          Finset.sum_le_sum (fun u _ => hw u (Finset.mem_univ u))
        _ = (d : ℝ) * |x w| := by
          simp only [Finset.sum_const, G.card_neighborFinset_eq_degree,
            hd.degree_eq, nsmul_eq_mul]
    exact (mul_le_mul_iff_left₀ hwpos).mp hmul
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤
        ∑ _v : V, (d : ℝ) :=
      Finset.sum_le_sum (fun v _ => hbound v)
    _ = ∑ v : V, (G.degree v : ℝ) := by simp only [hd.degree_eq]
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
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
