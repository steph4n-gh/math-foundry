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

theorem hull_order_le_1_nordhaus_gaddum_spectral_sum_1_914963b7a9e6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card V : ℝ) ≤ (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · simp only [if_neg hn]
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let B : Matrix V V ℝ := Gᶜ.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let hB : B.IsHermitian := Gᶜ.isHermitian_adjMatrix ℝ
    let a : ℝ := sSup (Set.range hA.eigenvalues)
    let b : ℝ := sSup (Set.range hB.eigenvalues)
    change (Fintype.card V : ℝ) ≤ a + b + 1
    have hupper : ∀ (M : Matrix V V ℝ) (hM : M.IsHermitian),
        ((sSup (Set.range hM.eigenvalues)) • (1 : Matrix V V ℝ) - M).PosSemidef := by
      intro M hM
      let t : ℝ := sSup (Set.range hM.eigenvalues)
      change (t • (1 : Matrix V V ℝ) - M).PosSemidef
      have ht : ∀ i, hM.eigenvalues i ≤ t := by
        intro i
        exact le_csSup (Set.finite_range hM.eigenvalues).bddAbove (Set.mem_range_self i)
      have hd : (t • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)).PosSemidef := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
        apply Matrix.PosSemidef.diagonal
        intro i
        simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          mul_one, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
          using sub_nonneg.mpr (ht i)
      let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hM.eigenvectorUnitary
      have hC : C (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) = M :=
        hM.spectral_theorem.symm
      have heq : t • (1 : Matrix V V ℝ) - M =
          C (t • (1 : Matrix V V ℝ) -
            Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) := by
        rw [map_sub, map_smul, map_one, hC]
      rw [heq]
      change ((hM.eigenvectorUnitary : Matrix V V ℝ) *
        (t • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) *
        Matrix.conjTranspose (hM.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
      exact hd.mul_mul_conjTranspose_same _
    have hsum : (1 : Matrix V V ℝ) + A + B = Matrix.of 1 := by
      simpa only [A, B, G.compl_adjMatrix_eq_adjMatrix_compl ℝ] using
        G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    have htotal : ((a + b + 1) • (1 : Matrix V V ℝ) -
        Matrix.of 1).PosSemidef := by
      have heq : (a + b + 1) • (1 : Matrix V V ℝ) - Matrix.of 1 =
          (a • (1 : Matrix V V ℝ) - A) +
            (b • (1 : Matrix V V ℝ) - B) := by
        rw [← hsum, add_smul, add_smul, one_smul]
        abel
      rw [heq]
      exact (hupper A hA).add (hupper B hB)
    have hones : Matrix.mulVec (Matrix.of 1 : Matrix V V ℝ) (1 : V → ℝ) =
        (Fintype.card V : ℝ) • (1 : V → ℝ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hnonneg : 0 ≤ (a + b + 1) * (Fintype.card V : ℝ) -
        (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
      simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hones, dotProduct_sub, dotProduct_smul,
        one_dotProduct_one, smul_eq_mul]
        using htotal.dotProduct_mulVec_nonneg (1 : V → ℝ)
    have hprod : 0 ≤ ((a + b + 1) - (Fintype.card V : ℝ)) *
        (Fintype.card V : ℝ) := by
      simpa only [sub_mul] using hnonneg
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hpos).mp hprod)

theorem model_df1156dc814ca602e6d4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)) ∧ ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) < (19999999 / 10000000 : ℝ)))) :
    ((Fintype.card V : ℝ) * ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) - ((Fintype.card V : ℝ) - (1 : ℝ))) * (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)))) ≥ ((3 : ℝ) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2)) := by
  sorry
