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
  sorry
