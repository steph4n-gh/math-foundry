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

theorem model_a9b32b4443158507d765 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((G.minDegree : ℝ) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))) ≤ (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hsmall : Fintype.card V ≤ 1 := by omega
    have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hsmall
    linarith only [h_guard.2.1, hsmallR]
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  dsimp only
  simp only [if_pos h_guard.1, dif_pos hn]
  let r : V → ℝ := fun v => Real.sqrt (G.degree v : ℝ)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (r v)⁻¹)
  let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
  have hL : (G.lapMatrix ℝ).IsHermitian := G.isHermitian_lapMatrix ℝ
  have hM : M.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose D hL
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  change (G.minDegree : ℝ) * hM.eigenvalues₀ k ≤ hL.eigenvalues₀ k
  have heig (A : Matrix V V ℝ) (hA : A.IsHermitian)
      (i : Fin (Fintype.card V)) :
      hA.eigenvalues (e i) = hA.eigenvalues₀ i := by
    change hA.eigenvalues₀ (e.symm (e i)) = hA.eigenvalues₀ i
    rw [e.symm_apply_apply]
  have hevec (A : Matrix V V ℝ) (hA : A.IsHermitian) (v : V) :
      A.toEuclideanLin (hA.eigenvectorBasis v) =
        hA.eigenvalues v • hA.eigenvectorBasis v := by
    apply PiLp.ext
    intro w
    change (Matrix.mulVec A (⇑(hA.eigenvectorBasis v))) w =
      hA.eigenvalues v * (hA.eigenvectorBasis v) w
    exact congrFun (hA.mulVec_eigenvectorBasis v) w
  have hp : M.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg : 0 ≤ hM.eigenvalues₀ k := by
    rw [← heig M hM k, hM.eigenvalues_eq (e k)]
    simpa only [RCLike.re_to_real] using
      hp.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e k)))
  have hquad (z : EuclideanSpace ℝ V) :
      inner ℝ z (M.toEuclideanLin z) =
        ∑ v : V, hM.eigenvalues v *
          (inner ℝ (hM.eigenvectorBasis v) z) ^ 2 := by
    have hd := congrArg (fun w : EuclideanSpace ℝ V => M.toEuclideanLin w)
      (hM.eigenvectorBasis.sum_repr' z)
    simp only [map_sum, map_smul, hevec] at hd
    rw [← hd, inner_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [inner_smul_right]
    rw [real_inner_comm (hM.eigenvectorBasis v) z]
    ring
  have hlow (z : EuclideanSpace ℝ V)
      (hz : inner ℝ (hM.eigenvectorBasis (e l)) z = 0) :
      hM.eigenvalues₀ k * ‖z‖ ^ 2 ≤ inner ℝ z (M.toEuclideanLin z) := by
    rw [hquad z, ← hM.eigenvectorBasis.sum_sq_inner_right z, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v = e l
    · subst v
      simp [hz]
    · have hi_ne : e.symm v ≠ l := by
        intro hi
        exact hv (by simpa only [Equiv.apply_symm_apply] using congrArg e hi)
      have hival : (e.symm v).val ≠ Fintype.card V - 1 := by
        intro heq
        exact hi_ne (Fin.ext heq)
      have hik : e.symm v ≤ k := by
        change (e.symm v).val ≤ Fintype.card V - 2
        have hlt := (e.symm v).isLt
        omega
      have hle : hM.eigenvalues₀ k ≤ hM.eigenvalues v := by
        change hM.eigenvalues₀ k ≤ hM.eigenvalues₀ (e.symm v)
        exact hM.eigenvalues₀_antitone hik
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
    (Matrix.diagonal r).toEuclideanLin
  have hrne (v : V) : r v ≠ 0 := by
    have hd : 0 < G.degree v :=
      h_guard.1.preconnected.degree_pos_of_nontrivial v
    have hdR : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast hd
    exact (Real.sqrt_ne_zero (Nat.cast_nonneg (G.degree v))).mpr (ne_of_gt hdR)
  have hrsq (v : V) : (r v) ^ 2 = (G.degree v : ℝ) := by
    exact Real.sq_sqrt (Nat.cast_nonneg (G.degree v))
  have hT (u : EuclideanSpace ℝ V) (v : V) : (T u) v = r v * u v := by
    change (Matrix.mulVec (Matrix.diagonal r) (⇑u)) v = r v * u v
    exact Matrix.mulVec_diagonal r (⇑u) v
  have hdu (u : EuclideanSpace ℝ V) : Matrix.mulVec D (⇑(T u)) = ⇑u := by
    funext v
    change (Matrix.mulVec (Matrix.diagonal (fun w => (r w)⁻¹))
      (⇑(T u))) v = u v
    rw [Matrix.mulVec_diagonal, hT u v, ← mul_assoc,
      inv_mul_cancel₀ (hrne v), one_mul]
  have hDself : D.conjTranspose = D := by
    simp only [D, Matrix.diagonal_conjTranspose, star_trivial]
  have hDtrans : D.transpose = D := by
    simp only [D, Matrix.diagonal_transpose]
  have hinner (u v : EuclideanSpace ℝ V) :
      inner ℝ u v = dotProduct (⇑u) (⇑v) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have henergy (u : EuclideanSpace ℝ V) :
      inner ℝ (T u) (M.toEuclideanLin (T u)) =
        inner ℝ u ((G.lapMatrix ℝ).toEuclideanLin u) := by
    rw [hinner, hinner]
    change dotProduct (⇑(T u))
        (Matrix.mulVec (D * G.lapMatrix ℝ * D.conjTranspose) (⇑(T u))) =
      dotProduct (⇑u) (Matrix.mulVec (G.lapMatrix ℝ) (⇑u))
    rw [hDself, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdu u]
    calc
      _ = dotProduct (Matrix.mulVec (G.lapMatrix ℝ) (⇑u))
          (Matrix.mulVec D (⇑(T u))) := by
        simpa only [hDtrans] using
          Matrix.dotProduct_transpose_mulVec D (⇑(T u))
            (Matrix.mulVec (G.lapMatrix ℝ) (⇑u))
      _ = dotProduct (Matrix.mulVec (G.lapMatrix ℝ) (⇑u)) (⇑u) := by
        rw [hdu u]
      _ = _ := dotProduct_comm _ _
  have hnorm (u : EuclideanSpace ℝ V) :
      (G.minDegree : ℝ) * ‖u‖ ^ 2 ≤ ‖T u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq u,
      EuclideanSpace.real_norm_sq_eq (T u), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [hT u v, mul_pow, hrsq v]
    have hd : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by
      exact_mod_cast G.minDegree_le_degree v
    exact mul_le_mul_of_nonneg_right hd (sq_nonneg (u v))
  let x : EuclideanSpace ℝ V := hL.eigenvectorBasis (e k)
  let y : EuclideanSpace ℝ V := hL.eigenvectorBasis (e l)
  have hne : e k ≠ e l := by
    intro h
    have hv := congrArg Fin.val (e.injective h)
    dsimp only [k, l] at hv
    omega
  have hxx : inner ℝ x x = 1 := hL.eigenvectorBasis.inner_eq_one (e k)
  have hyy : inner ℝ y y = 1 := hL.eigenvectorBasis.inner_eq_one (e l)
  have hxy : inner ℝ x y = 0 := hL.eigenvectorBasis.inner_eq_zero hne
  have hyx : inner ℝ y x = 0 := hL.eigenvectorBasis.inner_eq_zero (Ne.symm hne)
  have hx : (G.lapMatrix ℝ).toEuclideanLin x = hL.eigenvalues₀ k • x := by
    simpa only [x, heig] using hevec (G.lapMatrix ℝ) hL (e k)
  have hy : (G.lapMatrix ℝ).toEuclideanLin y = hL.eigenvalues₀ l • y := by
    simpa only [y, heig] using hevec (G.lapMatrix ℝ) hL (e l)
  have hkl : k ≤ l := by
    change Fintype.card V - 2 ≤ Fintype.card V - 1
    omega
  have horder : hL.eigenvalues₀ l ≤ hL.eigenvalues₀ k :=
    hL.eigenvalues₀_antitone hkl
  have hup (a b : ℝ) :
      inner ℝ (a • x + b • y)
          ((G.lapMatrix ℝ).toEuclideanLin (a • x + b • y)) ≤
        hL.eigenvalues₀ k * ‖a • x + b • y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [map_add, map_smul, hx, hy, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hxx, hxy, hyx, hyy,
      mul_zero, mul_one, zero_mul, add_zero, zero_add]
    have hb := mul_le_mul_of_nonneg_right horder (sq_nonneg b)
    nlinarith only [hb]
  have hex : ∃ u : EuclideanSpace ℝ V, u ≠ 0 ∧
      inner ℝ (hM.eigenvectorBasis (e l)) (T u) = 0 ∧
      inner ℝ u ((G.lapMatrix ℝ).toEuclideanLin u) ≤
        hL.eigenvalues₀ k * ‖u‖ ^ 2 := by
    by_cases ha : inner ℝ (hM.eigenvectorBasis (e l)) (T x) = 0
    · refine ⟨x, hL.eigenvectorBasis.orthonormal.ne_zero (e k), ha, ?_⟩
      simpa only [one_smul, zero_smul, add_zero] using hup 1 0
    · let a : ℝ := inner ℝ (hM.eigenvectorBasis (e l)) (T x)
      let b : ℝ := inner ℝ (hM.eigenvectorBasis (e l)) (T y)
      let u : EuclideanSpace ℝ V := b • x + (-a) • y
      have hu : u ≠ 0 := by
        intro hu
        have h := congrArg (fun w : EuclideanSpace ℝ V => inner ℝ y w) hu
        dsimp only [u] at h
        simp only [inner_add_right, real_inner_smul_right, hyx, hyy,
          mul_zero, mul_one, zero_add, inner_zero_right] at h
        have ha' : a = 0 := by linarith only [h]
        exact ha ha'
      have hz : inner ℝ (hM.eigenvectorBasis (e l)) (T u) = 0 := by
        dsimp only [u]
        simp only [map_add, map_smul, inner_add_right, real_inner_smul_right]
        change b * a + (-a) * b = 0
        ring
      exact ⟨u, hu, hz, hup b (-a)⟩
  obtain ⟨u, hu, hz, hub⟩ := hex
  have hpos : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hcomp : ((G.minDegree : ℝ) * hM.eigenvalues₀ k) * ‖u‖ ^ 2 ≤
      hL.eigenvalues₀ k * ‖u‖ ^ 2 := by
    calc
      _ = hM.eigenvalues₀ k * ((G.minDegree : ℝ) * ‖u‖ ^ 2) := by ring
      _ ≤ hM.eigenvalues₀ k * ‖T u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hnorm u) hnonneg
      _ ≤ inner ℝ (T u) (M.toEuclideanLin (T u)) := hlow (T u) hz
      _ = inner ℝ u ((G.lapMatrix ℝ).toEuclideanLin u) := henergy u
      _ ≤ hL.eigenvalues₀ k * ‖u‖ ^ 2 := hub
  exact le_of_mul_le_mul_right hcomp hpos
