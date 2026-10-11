import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

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
theorem estrada_ge_energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  sorry
