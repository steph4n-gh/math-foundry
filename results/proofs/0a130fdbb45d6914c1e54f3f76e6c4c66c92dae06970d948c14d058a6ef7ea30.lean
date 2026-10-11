import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

open scoped BigOperators

theorem hull_spectral_spread_le_1_nordhaus_gaddum_spectral_sum_1_1136dbf5ed1c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · simp only [if_neg hn]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let B : Matrix V V ℝ := Gᶜ.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let hB : B.IsHermitian := Gᶜ.isHermitian_adjMatrix ℝ
    let b : ℝ := sSup (Set.range hB.eigenvalues)
    have hb : ∀ i, hB.eigenvalues i ≤ b := by
      intro i
      exact le_csSup (Set.finite_range hB.eigenvalues).bddAbove (Set.mem_range_self i)
    have hd : (b • (1 : Matrix V V ℝ) -
        Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)).PosSemidef := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
      apply Matrix.PosSemidef.diagonal
      intro i
      simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
        using sub_nonneg.mpr (hb i)
    let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hB.eigenvectorUnitary
    have hC : C (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) = B :=
      hB.spectral_theorem.symm
    have heq : b • (1 : Matrix V V ℝ) - B =
        C (b • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) := by
      rw [map_sub, map_smul, map_one, hC]
    have hBbound : (b • (1 : Matrix V V ℝ) - B).PosSemidef := by
      rw [heq]
      change ((hB.eigenvectorUnitary : Matrix V V ℝ) *
        (b • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) *
        Matrix.conjTranspose (hB.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
      exact hd.mul_mul_conjTranspose_same _
    have hJ : (Matrix.of 1 : Matrix V V ℝ).PosSemidef := by
      have heqJ : (Matrix.of 1 : Matrix V V ℝ) =
          Matrix.vecMulVec (fun _ : V => (1 : ℝ))
            (star (fun _ : V => (1 : ℝ))) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.one_apply,
          star_trivial, mul_one]
      rw [heqJ]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : V => (1 : ℝ))
    have hsum : (1 : Matrix V V ℝ) + A + B = Matrix.of 1 := by
      simpa only [A, B, G.compl_adjMatrix_eq_adjMatrix_compl ℝ] using
        G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    have hs : (A + (b + 1) • (1 : Matrix V V ℝ)).PosSemidef := by
      have heq' : A + (b + 1) • (1 : Matrix V V ℝ) =
          Matrix.of 1 + (b • (1 : Matrix V V ℝ) - B) := by
        rw [← hsum, add_smul, one_smul]
        abel
      rw [heq']
      exact hJ.add hBbound
    have hlower : ∀ i : V, -(b + 1) ≤ hA.eigenvalues i := by
      intro i
      let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
      have hx : dotProduct x x = 1 := by
        have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i i
        rw [if_pos rfl] at h
        simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using h
      have heig : Matrix.mulVec A x = hA.eigenvalues i • x :=
        hA.mulVec_eigenvectorBasis i
      have hnonneg : 0 ≤ hA.eigenvalues i + (b + 1) := by
        simpa only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec,
          Matrix.one_mulVec, heig, dotProduct_add, dotProduct_smul,
          hx, smul_eq_mul, mul_one] using hs.dotProduct_mulVec_nonneg x
      linarith
    have hmin : -(b + 1) ≤ sInf (Set.range hA.eigenvalues) := by
      apply le_csInf (Set.range_nonempty hA.eigenvalues)
      rintro y ⟨i, rfl⟩
      exact hlower i
    change -(sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) + 1) ≤
      sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) at hmin
    linarith
