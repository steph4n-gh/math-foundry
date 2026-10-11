import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
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

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

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

theorem hull_spectral_spread_le_2_nordhaus_gaddum_spectral_sum_0_24c7f07054c7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)))) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp only [if_pos hn, sub_self, add_zero, mul_zero, le_refl]
  · simp only [if_neg hn]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    have hquad (H : SimpleGraph V) [DecidableRel H.Adj]
        (x : EuclideanSpace ℝ V) :
        inner ℝ x ((H.adjMatrix ℝ).toEuclideanLin x) ≤
          sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) * inner ℝ x x := by
      let A : Matrix V V ℝ := H.adjMatrix ℝ
      let hA : A.IsHermitian := H.isHermitian_adjMatrix ℝ
      let b := hA.eigenvectorBasis
      let T := A.toEuclideanLin
      let M : ℝ := sSup (Set.range hA.eigenvalues)
      have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
      have heig (i : V) : T (b i) = hA.eigenvalues i • b i := by
        apply PiLp.ext
        intro j
        change Matrix.mulVec A (fun k => b i k) j = hA.eigenvalues i * b i j
        exact congrFun (hA.mulVec_eigenvectorBasis i) j
      have hcoeff (i : V) :
          inner ℝ (b i) (T x) = hA.eigenvalues i * inner ℝ (b i) x := by
        rw [← hT (b i) x, heig i, real_inner_smul_left]
      calc
        inner ℝ x (T x) = ∑ i : V, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2 := by
          rw [← b.sum_inner_mul_inner x (T x)]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoeff i, real_inner_comm (b i) x]
          ring
        _ ≤ ∑ i : V, M * (inner ℝ (b i) x) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right
          · exact le_csSup (Set.finite_range hA.eigenvalues).bddAbove ⟨i, rfl⟩
          · exact sq_nonneg _
        _ = M * inner ℝ x x := by
          rw [← Finset.mul_sum, b.sum_sq_inner_right x, real_inner_self_eq_norm_sq]
    have hbound (H : SimpleGraph V) [DecidableRel H.Adj] (i : V) :
        -((H.isHermitian_adjMatrix ℝ).eigenvalues i) ≤
          sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) := by
      let A : Matrix V V ℝ := H.adjMatrix ℝ
      let hA : A.IsHermitian := H.isHermitian_adjMatrix ℝ
      let T := A.toEuclideanLin
      let x : EuclideanSpace ℝ V := hA.eigenvectorBasis i
      let y : EuclideanSpace ℝ V := WithLp.toLp 2 (fun v => |x v|)
      have hx1 : inner ℝ x x = 1 :=
        inner_self_eq_one_of_norm_eq_one (hA.eigenvectorBasis.orthonormal.1 i)
      have hy : inner ℝ y y = inner ℝ x x := by
        change (∑ v : V, |x v| * |x v|) = ∑ v : V, x v * x v
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [pow_two] using sq_abs (x v)
      have hx : T x = hA.eigenvalues i • x := by
        apply PiLp.ext
        intro j
        change Matrix.mulVec A (fun k => x k) j = hA.eigenvalues i * x j
        exact congrFun (hA.mulVec_eigenvectorBasis i) j
      have he : inner ℝ x (T x) = hA.eigenvalues i := by
        rw [hx, real_inner_smul_right, hx1, mul_one]
      have hcomp : -inner ℝ x (T x) ≤ inner ℝ y (T y) := by
        change -(∑ v : V, (∑ w : V, A v w * x w) * x v) ≤
          ∑ v : V, (∑ w : V, A v w * |x w|) * |x v|
        simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro v hv
        apply Finset.sum_le_sum
        intro w hw
        have ha : 0 ≤ A v w := by
          change (0 : ℝ) ≤ (if H.Adj v w then 1 else 0)
          split_ifs <;> norm_num
        calc
          -(A v w * x w * x v) ≤ |A v w * x w * x v| := neg_le_abs _
          _ = A v w * |x w| * |x v| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha]
      calc
        -(hA.eigenvalues i) = -inner ℝ x (T x) := by rw [he]
        _ ≤ inner ℝ y (T y) := hcomp
        _ ≤ sSup (Set.range hA.eigenvalues) * inner ℝ y y := hquad H y
        _ = sSup (Set.range hA.eigenvalues) := by rw [hy, hx1, mul_one]
    have hlo :
        -sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) ≤
          sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) := by
      apply le_csInf (Set.range_nonempty _)
      rintro z ⟨i, rfl⟩
      have hi := hbound G i
      linarith only [hi]
    have hc : 0 ≤ sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) := by
      obtain ⟨v⟩ := (inferInstance : Nonempty V)
      have hneg := hbound Gᶜ v
      have hle : (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues v ≤
          sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) :=
        le_csSup (Set.finite_range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues).bddAbove ⟨v, rfl⟩
      linarith only [hneg, hle]
    linarith only [hlo, hc]

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn
theorem hull3d_order_ge_1_0_spectral_spread_triangle_count_0_is_regular_282e36142d1e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Fintype.card V : ℝ) ≥ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  sorry
