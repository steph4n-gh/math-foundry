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

theorem model_f507aec4f80c30fd2faa {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) - (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))) ≥ ((Fintype.card V : ℝ) * ((G.maxDegree : ℝ) - (G.minDegree : ℝ))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hleR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let n : ℝ := Fintype.card V
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast (by omega : 0 < Fintype.card V)
  let H := G.isHermitian_lapMatrix ℝ
  let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
    (G.lapMatrix ℝ).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr H
  let lam : Fin (Fintype.card V) → ℝ := H.eigenvalues₀
  let b : OrthonormalBasis (Fin (Fintype.card V)) ℝ (EuclideanSpace ℝ V) :=
    hT.eigenvectorBasis finrank_euclideanSpace
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let r : ℝ := sSup (Set.range H.eigenvalues)
  have hbdd : BddAbove (Set.range H.eigenvalues) :=
    (Set.finite_range H.eigenvalues).bddAbove
  have hspec (i : Fin (Fintype.card V)) : lam i ≤ r := by
    have he : H.eigenvalues (e i) = lam i := by
      change H.eigenvalues₀ (e.symm (e i)) = H.eigenvalues₀ i
      rw [e.symm_apply_apply]
    rw [← he]
    exact le_csSup hbdd ⟨e i, rfl⟩
  have heig (i : Fin (Fintype.card V)) : T (b i) = lam i • b i :=
    hT.apply_eigenvectorBasis finrank_euclideanSpace i
  have hpos (x : EuclideanSpace ℝ V) : 0 ≤ inner ℝ x (T x) := by
    change 0 ≤ dotProduct (Matrix.mulVec (G.lapMatrix ℝ) (WithLp.ofLp x))
      (star (WithLp.ofLp x))
    rw [dotProduct_comm]
    exact (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (WithLp.ofLp x)
  have hlam_nonneg (i : Fin (Fintype.card V)) : 0 ≤ lam i := by
    have hp := hpos (b i)
    rw [heig i, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.norm_eq_one i, one_pow, mul_one] at hp
    exact hp
  have hquadratic (x : EuclideanSpace ℝ V) :
      inner ℝ x (T x) = ∑ i, lam i * (b.repr x i) ^ 2 := by
    rw [← b.sum_inner_mul_inner x (T x)]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (b i) x, ← b.repr_apply_apply x i,
      ← b.repr_apply_apply (T x) i,
      hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace x i]
    change b.repr x i * (lam i * b.repr x i) = lam i * (b.repr x i) ^ 2
    ring
  have hparseval (x : EuclideanSpace ℝ V) :
      (∑ i, (b.repr x i) ^ 2) = ‖x‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using b.sum_sq_inner_right x
  have hupper (x : EuclideanSpace ℝ V) : inner ℝ x (T x) ≤ r * ‖x‖ ^ 2 := by
    rw [hquadratic x, ← hparseval x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hspec i) (sq_nonneg (b.repr x i))
  let o : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have hozero : T o = 0 := by
    apply (WithLp.ofLp_injective 2)
    change Matrix.mulVec (G.lapMatrix ℝ) (1 : V → ℝ) = 0
    exact G.lapMatrix_mulVec_one_eq_zero ℝ
  have hone : inner ℝ o o = n := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    simp [o, n]
  have hevnorm (v : V) :
      inner ℝ (EuclideanSpace.basisFun V ℝ v) (EuclideanSpace.basisFun V ℝ v) = 1 := by
    rw [real_inner_self_eq_norm_sq, (EuclideanSpace.basisFun V ℝ).norm_eq_one v,
      one_pow]
  have hve (v : V) : inner ℝ (EuclideanSpace.basisFun V ℝ v) o = 1 := by
    rw [EuclideanSpace.basisFun_inner]
  have hove (v : V) : inner ℝ o (EuclideanSpace.basisFun V ℝ v) = 1 :=
    (real_inner_comm (EuclideanSpace.basisFun V ℝ v) o).trans (hve v)
  have hdiag (v : V) :
      inner ℝ (EuclideanSpace.basisFun V ℝ v)
        (T (EuclideanSpace.basisFun V ℝ v)) = (G.degree v : ℝ) := by
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]
    change (Matrix.mulVec (G.lapMatrix ℝ) (Pi.single v (1 : ℝ))) v = (G.degree v : ℝ)
    rw [Matrix.mulVec_single_one]
    change (G.lapMatrix ℝ) v v = (G.degree v : ℝ)
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]
  let z : V → EuclideanSpace ℝ V :=
    fun v => n • EuclideanSpace.basisFun V ℝ v - o
  have hmean (v : V) : inner ℝ o (z v) = 0 := by
    change inner ℝ o (n • EuclideanSpace.basisFun V ℝ v - o) = 0
    rw [inner_sub_right, real_inner_smul_right, hove v, hone]
    ring
  have hznorm (v : V) : ‖z v‖ ^ 2 = n * (n - 1) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (n • EuclideanSpace.basisFun V ℝ v - o)
      (n • EuclideanSpace.basisFun V ℝ v - o) = n * (n - 1)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hevnorm v, hve v, hove v, hone]
    ring
  have hqz (v : V) : inner ℝ (z v) (T (z v)) = n ^ 2 * (G.degree v : ℝ) := by
    have hot : inner ℝ o (T (EuclideanSpace.basisFun V ℝ v)) = 0 := by
      rw [← hT o (EuclideanSpace.basisFun V ℝ v), hozero, inner_zero_left]
    change inner ℝ (n • EuclideanSpace.basisFun V ℝ v - o)
      (T (n • EuclideanSpace.basisFun V ℝ v - o)) = n ^ 2 * (G.degree v : ℝ)
    rw [map_sub, map_smul, hozero, sub_zero]
    simp only [inner_sub_left, real_inner_smul_left, real_inner_smul_right,
      hdiag v, hot, mul_zero, sub_zero]
    ring
  have hvertex_upper (v : V) : n * (G.degree v : ℝ) ≤ (n - 1) * r := by
    have hu := hupper (z v)
    rw [hqz v, hznorm v] at hu
    have hh : (n * (G.degree v : ℝ)) * n ≤ ((n - 1) * r) * n := by
      nlinarith only [hu]
    exact le_of_mul_le_mul_right hh hnpos
  obtain ⟨vM, hvM⟩ := G.exists_maximal_degree_vertex
  have hmax := hvertex_upper vM
  rw [← hvM] at hmax
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  have hzero : (0 : ℝ) ∈ Set.range H.eigenvalues := by
    rw [← H.spectrum_real_eq_range_eigenvalues]
    exact G.zero_mem_spectrum_lapMatrix ℝ
  obtain ⟨w, hw⟩ := hzero
  let k : Fin (Fintype.card V) := e.symm w
  have hk : lam k = 0 := hw
  have hk_le : k ≤ last := by
    change k.val ≤ Fintype.card V - 1
    have hkb := k.isLt
    omega
  have hlastzero : lam last = 0 := by
    apply le_antisymm _ (hlam_nonneg last)
    calc
      lam last ≤ lam k := H.eigenvalues₀_antitone hk_le
      _ = 0 := hk
  rw [if_neg hn0]
  by_cases hc : G.Connected
  · simp only [if_pos hc, dif_pos hn]
    change n * ((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ≤
      (n - 1) * (r - lam j)
    have hbzero : T (b last) = 0 := by
      rw [heig last, hlastzero, zero_smul]
    have hker : Matrix.mulVec (G.lapMatrix ℝ) (WithLp.ofLp (b last)) = 0 := by
      funext v
      exact congrArg (fun x : EuclideanSpace ℝ V => x v) hbzero
    have hbconst : b last = ((b last) vM) • o := by
      apply (WithLp.ofLp_injective 2)
      funext v
      change (b last) v = (b last) vM * 1
      rw [mul_one]
      exact (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hker)
        v vM (hc v vM)
    have hlower (x : EuclideanSpace ℝ V) (hm : inner ℝ o x = 0) :
        lam j * ‖x‖ ^ 2 ≤ inner ℝ x (T x) := by
      have hcoeff : b.repr x last = 0 := by
        rw [b.repr_apply_apply x last, hbconst, real_inner_smul_left, hm, mul_zero]
      rw [hquadratic x, ← hparseval x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      by_cases hil : i = last
      · subst i
        simp [hcoeff]
      · have hij : i ≤ j := by
          have hib := i.isLt
          have hine : i.val ≠ Fintype.card V - 1 := by
            intro hval
            apply hil
            apply Fin.ext
            exact hval
          change i.val ≤ Fintype.card V - 2
          omega
        exact mul_le_mul_of_nonneg_right (H.eigenvalues₀_antitone hij)
          (sq_nonneg (b.repr x i))
    obtain ⟨vm, hvm⟩ := G.exists_minimal_degree_vertex
    have hl := hlower (z vm) (hmean vm)
    rw [hznorm vm, hqz vm] at hl
    have hh : ((n - 1) * lam j) * n ≤ (n * (G.degree vm : ℝ)) * n := by
      nlinarith only [hl]
    have hmin := le_of_mul_le_mul_right hh hnpos
    rw [← hvm] at hmin
    nlinarith only [hmax, hmin]
  · simp only [if_neg hc, sub_zero]
    change n * ((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ≤ (n - 1) * r
    have hminprod : 0 ≤ n * (G.minDegree : ℝ) :=
      mul_nonneg (le_of_lt hnpos) (Nat.cast_nonneg _)
    nlinarith only [hmax, hminprod]
