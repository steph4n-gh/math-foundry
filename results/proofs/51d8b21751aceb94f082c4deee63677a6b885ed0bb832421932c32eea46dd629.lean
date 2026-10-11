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

theorem hull_laplacian_spectral_radius_le_1_signless_laplacian_spectral_radius_0_e1c0af0e1150 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let hL := G.isHermitian_lapMatrix ℝ
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    let r : ℝ := sSup (Set.range hQ.eigenvalues)
    change sSup (Set.range hL.eigenvalues) ≤ r
    have hr (i : V) : hQ.eigenvalues i ≤ r :=
      le_csSup (Set.finite_range hQ.eigenvalues).bddAbove (Set.mem_range_self i)
    have hC :
        (r • (1 : Matrix V V ℝ) - (G.degMatrix ℝ + G.adjMatrix ℝ)).PosSemidef := by
      have hp : (Matrix.diagonal (fun i : V => r - hQ.eigenvalues i)).PosSemidef :=
        Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hr i))
      have hs :
          Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hQ.eigenvectorUnitary
            (Matrix.diagonal (fun i : V => r - hQ.eigenvalues i)) =
          r • (1 : Matrix V V ℝ) - (G.degMatrix ℝ + G.adjMatrix ℝ) := by
        rw [← Matrix.diagonal_sub (fun _ : V => r) hQ.eigenvalues,
          ← Matrix.smul_one_eq_diagonal r, map_sub, map_smul, map_one]
        exact congrArg
          (fun M : Matrix V V ℝ => r • (1 : Matrix V V ℝ) - M)
          hQ.spectral_theorem.symm
      rw [← hs]
      simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose] using
        hp.mul_mul_conjTranspose_same (hQ.eigenvectorUnitary : Matrix V V ℝ)
    have hupper (y : V → ℝ) :
        dotProduct y (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) y) ≤
          r * dotProduct y y := by
      have ht := hC.dotProduct_mulVec_nonneg y
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at ht
      exact sub_nonneg.mp ht
    refine csSup_le (Set.range_nonempty hL.eigenvalues) ?_
    rintro _ ⟨i, rfl⟩
    let x : EuclideanSpace ℝ V := hL.eigenvectorBasis i
    let y : V → ℝ := fun v => |x v|
    have hn : (∑ v : V, (x v) ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq x]
      simp only [x, OrthonormalBasis.norm_eq_one, one_pow]
    have hy : dotProduct y y = (1 : ℝ) := by
      simpa only [dotProduct, y, abs_mul_abs_self, pow_two] using hn
    have hdiag :
        dotProduct y (Matrix.mulVec (G.degMatrix ℝ) y) =
          dotProduct (⇑x) (Matrix.mulVec (G.degMatrix ℝ) (⇑x)) := by
      simp only [G.dotProduct_mulVec_degMatrix, y, mul_assoc, abs_mul_abs_self]
    have hadj :
        -dotProduct (⇑x) (Matrix.mulVec (G.adjMatrix ℝ) (⇑x)) ≤
          dotProduct y (Matrix.mulVec (G.adjMatrix ℝ) y) := by
      simp only [G.dotProduct_mulVec_adjMatrix, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases hab : G.Adj a b
      · simp only [if_pos hab, y]
        simpa only [abs_mul] using (neg_le_abs (x a * x b))
      · simp only [if_neg hab, neg_zero, le_refl]
    have heig : hL.eigenvalues i =
        dotProduct (⇑x) (Matrix.mulVec (G.lapMatrix ℝ) (⇑x)) := by
      simpa only [x, star_trivial, RCLike.re_to_real] using hL.eigenvalues_eq i
    calc
      hL.eigenvalues i =
          dotProduct (⇑x) (Matrix.mulVec (G.lapMatrix ℝ) (⇑x)) := heig
      _ = dotProduct (⇑x) (Matrix.mulVec (G.degMatrix ℝ) (⇑x)) -
          dotProduct (⇑x) (Matrix.mulVec (G.adjMatrix ℝ) (⇑x)) := by
        rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub]
      _ ≤ dotProduct y (Matrix.mulVec (G.degMatrix ℝ) y) +
          dotProduct y (Matrix.mulVec (G.adjMatrix ℝ) y) := by
        rw [hdiag]
        simpa only [sub_eq_add_neg] using
          add_le_add
            (le_refl (dotProduct (⇑x) (Matrix.mulVec (G.degMatrix ℝ) (⇑x))))
            hadj
      _ = dotProduct y (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) y) := by
        rw [Matrix.add_mulVec, dotProduct_add]
      _ ≤ r * dotProduct y y := hupper y
      _ = r := by rw [hy, mul_one]
