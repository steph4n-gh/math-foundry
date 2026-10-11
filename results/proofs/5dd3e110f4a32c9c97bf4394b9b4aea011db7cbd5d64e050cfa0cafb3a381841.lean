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

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)

theorem model_886a365b7173b119a27a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Gᶜ.cliqueNum : ℝ) + (G.edgeFinset.card : ℝ)) ≥ (Fintype.card V : ℝ) := by
  classical
  let T : Finset V := G.edgeFinset.image (fun e : Sym2 V => e.out.1)
  let S : Finset V := Finset.univ \ T
  have hT : T.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hS : Gᶜ.IsClique (S : Set V) := by
    intro u hu v hv hne
    change u ≠ v ∧ ¬ G.Adj u v
    refine ⟨hne, ?_⟩
    intro huv
    have he : s(u, v) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr huv)
    have hm : (s(u, v) : Sym2 V).out.1 ∈ T :=
      Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v))) with h | h
    · apply (Finset.mem_sdiff.mp hu).2
      exact h ▸ hm
    · apply (Finset.mem_sdiff.mp hv).2
      exact h ▸ hm
  have hclique : S.card ≤ Gᶜ.cliqueNum := hS.card_le_cliqueNum
  have hcards : S.card + T.card = Fintype.card V := by
    simpa only [S, Finset.card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T))
  have hnat : Fintype.card V ≤ Gᶜ.cliqueNum + G.edgeFinset.card := by
    omega
  exact_mod_cast hnat
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
