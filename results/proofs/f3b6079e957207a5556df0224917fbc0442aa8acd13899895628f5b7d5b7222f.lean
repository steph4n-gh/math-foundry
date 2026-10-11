import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic








open scoped BigOperators

theorem hull3d_signless_laplacian_spectral_radius_le_1_0_laplacian_spectral_radius_order_0_is_tree_2b08091466a0 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  let c : G.Coloring (Fin 2) := h_guard.coloringTwo
  let d : V → ℝ := fun v => if c v = 0 then 1 else -1
  let S : Matrix V V ℝ := Matrix.diagonal d
  have hd_sq (v : V) : d v * d v = 1 := by
    by_cases hv : c v = 0 <;> simp [d, hv]
  have hd_adj {v w : V} (hab : G.Adj v w) : d v * d w = -1 := by
    have hne : c v ≠ c w := c.valid hab
    by_cases hv : c v = 0
    · have hw : c w ≠ 0 := fun hw => hne (hv.trans hw.symm)
      simp [d, hv, hw]
    · have hv1 : c v = 1 := Fin.eq_one_of_ne_zero (c v) hv
      have hw : c w = 0 := by
        by_contra hw
        exact hne (hv1.trans (Fin.eq_one_of_ne_zero (c w) hw).symm)
      simp [d, hv, hw]
  have hSS : S * S = 1 := by
    simp only [S, Matrix.diagonal_mul_diagonal, hd_sq, Matrix.diagonal_one]
  have hconj : S * G.lapMatrix ℝ * S = G.degMatrix ℝ + G.adjMatrix ℝ := by
    ext v w
    simp only [S, Matrix.mul_diagonal, Matrix.diagonal_mul,
      SimpleGraph.lapMatrix, Matrix.sub_apply, Matrix.add_apply,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply]
    by_cases hvw : v = w
    · subst w
      simp only [Matrix.diagonal_apply_eq, if_neg (G.irrefl (v := v)),
        sub_zero, add_zero]
      calc
        d v * (G.degree v : ℝ) * d v =
            (G.degree v : ℝ) * (d v * d v) := by ring
        _ = (G.degree v : ℝ) := by rw [hd_sq, mul_one]
    · simp only [Matrix.diagonal_apply_ne _ hvw]
      by_cases hab : G.Adj v w
      · simp only [if_pos hab, zero_sub, zero_add]
        calc
          d v * (-1 : ℝ) * d w = -(d v * d w) := by ring
          _ = 1 := by rw [hd_adj hab]; norm_num
      · simp only [if_neg hab, sub_zero, add_zero, mul_zero, zero_mul]
  have hchar :
      (G.degMatrix ℝ + G.adjMatrix ℝ).charpoly = (G.lapMatrix ℝ).charpoly := by
    rw [← hconj, Matrix.charpoly_mul_comm, ← mul_assoc, hSS, one_mul]
  have heq :
      ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues =
        (G.isHermitian_lapMatrix ℝ).eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ))
      (G.isHermitian_lapMatrix ℝ)).2 hchar
  simp only [heq, le_refl]
