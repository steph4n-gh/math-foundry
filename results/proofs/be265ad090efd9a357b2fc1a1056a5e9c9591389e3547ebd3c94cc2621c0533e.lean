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

theorem model_b0cf9d1e2a8965e241a4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) ≥ ((G.minDegree : ℝ) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hsmall : Fintype.card V ≤ 1 := by omega
    have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hsmall
    linarith only [h_guard.2, hsmallR]
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  dsimp only
  simp only [if_pos h_guard.1, dif_pos hn]
  let s : V → ℝ := fun v => Real.sqrt (G.degree v : ℝ)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (s v)⁻¹)
  let S : Matrix V V ℝ := Matrix.diagonal s
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let M : Matrix V V ℝ := D * L * D.conjTranspose
  have hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  have hM : M.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose D hL
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let a : ℝ := hL.eigenvalues₀ j
  let b : ℝ := hM.eigenvalues₀ j
  change (G.minDegree : ℝ) * b ≤ a
  have heig {A : Matrix V V ℝ} (hA : A.IsHermitian)
      (i : Fin (Fintype.card V)) :
      hA.eigenvalues (e i) = hA.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hact {A : Matrix V V ℝ} (hA : A.IsHermitian) (v : V) :
      A.toEuclideanLin (hA.eigenvectorBasis v) =
        hA.eigenvalues v • hA.eigenvectorBasis v := by
    apply PiLp.ext
    intro w
    change (Matrix.mulVec A ⇑(hA.eigenvectorBasis v)) w =
      (hA.eigenvalues v • ⇑(hA.eigenvectorBasis v)) w
    exact congrFun (hA.mulVec_eigenvectorBasis v) w
  have hnn {A : Matrix V V ℝ} (hA : A.IsHermitian)
      (hp : A.PosSemidef) (i : Fin (Fintype.card V)) :
      0 ≤ hA.eigenvalues₀ i := by
    rw [← heig hA i, hA.eigenvalues_eq (e i)]
    simpa only [RCLike.re_to_real] using
      hp.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis (e i)))
  have hpL : L.PosSemidef := G.posSemidef_lapMatrix ℝ
  have hpM : M.PosSemidef := hpL.mul_mul_conjTranspose_same D
  have ha : 0 ≤ a := hnn hL hpL j
  have hb : 0 ≤ b := hnn hM hpM j
  have hprod : (∏ v : V, hL.eigenvalues v) = 0 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      (hL.det_eq_prod_eigenvalues.symm.trans (G.det_lapMatrix_eq_zero ℝ))
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hz : hL.eigenvalues₀ (e.symm v) = 0 := by
    rw [← heig hL (e.symm v), Equiv.apply_symm_apply]
    exact hv
  have hvl : e.symm v ≤ l := by
    change (e.symm v).val ≤ Fintype.card V - 1
    have hlt := (e.symm v).isLt
    omega
  have hlast : hL.eigenvalues₀ l = 0 :=
    le_antisymm ((hL.eigenvalues₀_antitone hvl).trans_eq hz) (hnn hL hpL l)
  have hs (v : V) : s v ≠ 0 := by
    have hd : 0 < G.degree v :=
      h_guard.1.preconnected.degree_pos_of_nontrivial v
    have hdR : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast hd
    exact (Real.sqrt_ne_zero (Nat.cast_nonneg (G.degree v))).2 (ne_of_gt hdR)
  have hsquare (v : V) : s v ^ 2 = (G.degree v : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg (G.degree v))
  have hDself : D.conjTranspose = D := by
    simp only [D, Matrix.diagonal_conjTranspose, star_trivial]
  have hD : D.IsHermitian := hDself
  have hDsym : D.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hD
  have hMsym : M.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have hDS (x : EuclideanSpace ℝ V) :
      D.toEuclideanLin (S.toEuclideanLin x) = x := by
    apply PiLp.ext
    intro v
    change (Matrix.mulVec D (Matrix.mulVec S ⇑x)) v = x v
    simp only [D, S, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hs v), one_mul]
  have hMact (z : EuclideanSpace ℝ V) :
      M.toEuclideanLin z = D.toEuclideanLin (L.toEuclideanLin (D.toEuclideanLin z)) := by
    apply PiLp.ext
    intro v
    change (Matrix.mulVec M ⇑z) v =
      (Matrix.mulVec D (Matrix.mulVec L (Matrix.mulVec D ⇑z))) v
    simp only [M, hDself, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have henergy (x : EuclideanSpace ℝ V) :
      inner ℝ (S.toEuclideanLin x) (M.toEuclideanLin (S.toEuclideanLin x)) =
        inner ℝ x (L.toEuclideanLin x) := by
    rw [hMact, hDS]
    rw [← hDsym (S.toEuclideanLin x) (L.toEuclideanLin x), hDS]
  have hnorm (x : EuclideanSpace ℝ V) :
      (G.minDegree : ℝ) * ‖x‖ ^ 2 ≤ ‖S.toEuclideanLin x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    calc
      (G.minDegree : ℝ) * (x v) ^ 2 ≤ (G.degree v : ℝ) * (x v) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast G.minDegree_le_degree v) (sq_nonneg (x v))
      _ = ((S.toEuclideanLin x) v) ^ 2 := by
        change (G.degree v : ℝ) * (x v) ^ 2 = ((Matrix.mulVec S ⇑x) v) ^ 2
        simp only [S, Matrix.mulVec_diagonal]
        rw [mul_pow, hsquare v]
  have hgap (z : EuclideanSpace ℝ V)
      (hz : inner ℝ (hM.eigenvectorBasis (e l)) z = 0) :
      b * ‖z‖ ^ 2 ≤ inner ℝ z (M.toEuclideanLin z) := by
    calc
      b * ‖z‖ ^ 2 =
          ∑ v : V, b * (inner ℝ (hM.eigenvectorBasis v) z) ^ 2 := by
        rw [← hM.eigenvectorBasis.sum_sq_inner_right z, Finset.mul_sum]
      _ ≤ ∑ v : V, hM.eigenvalues v * (inner ℝ (hM.eigenvectorBasis v) z) ^ 2 := by
        apply Finset.sum_le_sum
        intro v _
        by_cases hv : v = e l
        · simp [hv, hz]
        · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hne : e.symm v ≠ l := by
            intro hh
            apply hv
            calc
              v = e (e.symm v) := (e.apply_symm_apply v).symm
              _ = e l := congrArg e hh
          have hvalne : (e.symm v).val ≠ Fintype.card V - 1 := by
            intro hh
            apply hne
            exact Fin.ext hh
          have hij : e.symm v ≤ j := by
            change (e.symm v).val ≤ Fintype.card V - 2
            have hlt := (e.symm v).isLt
            omega
          calc
            b = hM.eigenvalues₀ j := rfl
            _ ≤ hM.eigenvalues₀ (e.symm v) := hM.eigenvalues₀_antitone hij
            _ = hM.eigenvalues v := by
              simpa only [Equiv.apply_symm_apply] using (heig hM (e.symm v)).symm
      _ = inner ℝ z (M.toEuclideanLin z) := by
        rw [← hM.eigenvectorBasis.sum_inner_mul_inner z (M.toEuclideanLin z)]
        apply Finset.sum_congr rfl
        intro v _
        rw [real_inner_comm (hM.eigenvectorBasis v) z,
          ← hMsym (hM.eigenvectorBasis v) z, hact hM v, real_inner_smul_left]
        ring
  let u : EuclideanSpace ℝ V := hL.eigenvectorBasis (e j)
  let t : EuclideanSpace ℝ V := hL.eigenvectorBasis (e l)
  let y : EuclideanSpace ℝ V := hM.eigenvectorBasis (e l)
  have huact : L.toEuclideanLin u = a • u := by
    dsimp only [u, a]
    rw [hact hL (e j), heig hL j]
  have htact : L.toEuclideanLin t = 0 := by
    dsimp only [t]
    rw [hact hL (e l), heig hL l, hlast, zero_smul]
  have hfinish (x : EuclideanSpace ℝ V) (hx : x ≠ 0)
      (hz : inner ℝ y (S.toEuclideanLin x) = 0)
      (hupper : inner ℝ x (L.toEuclideanLin x) ≤ a * ‖x‖ ^ 2) :
      (G.minDegree : ℝ) * b ≤ a := by
    have hxp : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    have hcompare : ((G.minDegree : ℝ) * b) * ‖x‖ ^ 2 ≤ a * ‖x‖ ^ 2 := by
      calc
        ((G.minDegree : ℝ) * b) * ‖x‖ ^ 2 =
            b * ((G.minDegree : ℝ) * ‖x‖ ^ 2) := by ring
        _ ≤ b * ‖S.toEuclideanLin x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (hnorm x) hb
        _ ≤ inner ℝ (S.toEuclideanLin x) (M.toEuclideanLin (S.toEuclideanLin x)) :=
          hgap (S.toEuclideanLin x) hz
        _ = inner ℝ x (L.toEuclideanLin x) := henergy x
        _ ≤ a * ‖x‖ ^ 2 := hupper
    exact (mul_le_mul_iff_left₀ hxp).mp hcompare
  by_cases hbt : inner ℝ y (S.toEuclideanLin t) = 0
  · apply hfinish t (hL.eigenvectorBasis.orthonormal.ne_zero (e l)) hbt
    rw [htact, inner_zero_right]
    exact mul_nonneg ha (sq_nonneg ‖t‖)
  · have hjl : e j ≠ e l := by
      intro hh
      have hval := congrArg Fin.val (e.injective hh)
      dsimp only [j, l] at hval
      omega
    have huu : inner ℝ u u = 1 := hL.eigenvectorBasis.inner_eq_one (e j)
    have htt : inner ℝ t t = 1 := hL.eigenvectorBasis.inner_eq_one (e l)
    have hut : inner ℝ u t = 0 := hL.eigenvectorBasis.inner_eq_zero hjl
    have htu : inner ℝ t u = 0 := hL.eigenvectorBasis.inner_eq_zero hjl.symm
    let c : ℝ := inner ℝ y (S.toEuclideanLin u) / inner ℝ y (S.toEuclideanLin t)
    let x : EuclideanSpace ℝ V := u - c • t
    have hxorth : inner ℝ y (S.toEuclideanLin x) = 0 := by
      dsimp only [x]
      rw [map_sub, map_smul, inner_sub_right, real_inner_smul_right]
      dsimp only [c]
      rw [div_mul_cancel₀ _ hbt, sub_self]
    have hux : inner ℝ u x = 1 := by
      dsimp only [x]
      rw [inner_sub_right, real_inner_smul_right, huu, hut, mul_zero, sub_zero]
    have hx : x ≠ 0 := by
      intro hxzero
      rw [hxzero, inner_zero_right] at hux
      norm_num at hux
    have hxu : inner ℝ x u = 1 := (real_inner_comm u x).trans hux
    have hxnorm : ‖x‖ ^ 2 = 1 + c ^ 2 := by
      rw [← real_inner_self_eq_norm_sq x]
      dsimp only [x]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, huu, hut, htu, htt]
      ring
    have hxact : L.toEuclideanLin x = a • u := by
      dsimp only [x]
      rw [map_sub, map_smul, huact, htact, smul_zero, sub_zero]
    apply hfinish x hx hxorth
    rw [hxact, real_inner_smul_right, hxu, mul_one, hxnorm]
    nlinarith only [mul_nonneg ha (sq_nonneg c)]

theorem model_00c10ac49d00184b94a2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ (¬ ((∃ d : ℕ, G.IsRegularOfDegree d))) ∧ ((Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ (((2 : ℝ) * (G.maxDegree : ℝ)) - ((((2 : ℝ) * ((G.minDegree : ℝ) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))) * ((G.maxDegree : ℝ) - (G.minDegree : ℝ))) / ((Fintype.card V : ℝ) * (max (1 : ℝ) (((G.minDegree : ℝ) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))) + ((2 : ℝ) * ((G.maxDegree : ℝ) - (G.minDegree : ℝ)))))))) := by
  classical
  have hn3 : 3 ≤ Fintype.card V := by
    by_contra h
    have hs : Fintype.card V ≤ 2 := by omega
    have hsR : (Fintype.card V : ℝ) ≤ 2 := by exact_mod_cast hs
    linarith only [h_guard.2.2, hsR]
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let M : Matrix V V ℝ := D * L * D.conjTranspose
  have hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  have hM : M.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose D hL
  let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  let e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let n : ℝ := (Fintype.card V : ℝ)
  let r : ℝ := (G.maxDegree : ℝ) - (G.minDegree : ℝ)
  let a : ℝ := (G.minDegree : ℝ) * hM.eigenvalues₀ j
  let k : ℝ := max 1 (a + 2 * r)
  rw [if_neg hn0]
  dsimp only
  simp only [if_pos h_guard.1, dif_pos hn2]
  change sSup (Set.range hQ.eigenvalues) ≤
    2 * (G.maxDegree : ℝ) - (2 * a * r) / (n * k)
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < Fintype.card V from by omega)
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    exact sub_nonneg.mpr (by exact_mod_cast G.minDegree_le_maxDegree)
  have heig {A : Matrix V V ℝ} (hA : A.IsHermitian)
      (i : Fin (Fintype.card V)) :
      hA.eigenvalues (e i) = hA.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hact {A : Matrix V V ℝ} (hA : A.IsHermitian) (v : V) :
      A.toEuclideanLin (hA.eigenvectorBasis v) =
        hA.eigenvalues v • hA.eigenvectorBasis v := by
    apply PiLp.ext
    intro w
    change (Matrix.mulVec A ⇑(hA.eigenvectorBasis v)) w =
      (hA.eigenvalues v • ⇑(hA.eigenvectorBasis v)) w
    exact congrFun (hA.mulVec_eigenvectorBasis v) w
  have hnn {A : Matrix V V ℝ} (hA : A.IsHermitian)
      (hp : A.PosSemidef) (i : Fin (Fintype.card V)) :
      0 ≤ hA.eigenvalues₀ i := by
    rw [← heig hA i, hA.eigenvalues_eq (e i)]
    simpa only [RCLike.re_to_real] using
      hp.dotProduct_mulVec_nonneg (⇑(hA.eigenvectorBasis (e i)))
  have hpL : L.PosSemidef := G.posSemidef_lapMatrix ℝ
  have hpM : M.PosSemidef := hpL.mul_mul_conjTranspose_same D
  have ha0 : 0 ≤ a :=
    mul_nonneg (Nat.cast_nonneg G.minDegree) (hnn hM hpM j)
  have ha : a ≤ hL.eigenvalues₀ j := by
    have hh := model_b0cf9d1e2a8965e241a4 G
      ⟨h_guard.1, by linarith only [h_guard.2.2]⟩
    dsimp only at hh
    simp only [if_pos h_guard.1, dif_pos hn2] at hh
    exact hh
  have hzero : (0 : ℝ) ∈ Set.range hL.eigenvalues := by
    rw [← hL.spectrum_real_eq_range_eigenvalues]
    exact G.zero_mem_spectrum_lapMatrix ℝ
  obtain ⟨v, hv⟩ := hzero
  have hz : hL.eigenvalues₀ (e.symm v) = 0 := by
    rw [← heig hL (e.symm v), Equiv.apply_symm_apply]
    exact hv
  have hvl : e.symm v ≤ l := by
    change (e.symm v).val ≤ Fintype.card V - 1
    have hlt := (e.symm v).isLt
    omega
  have hlast : hL.eigenvalues₀ l = 0 :=
    le_antisymm ((hL.eigenvalues₀_antitone hvl).trans_eq hz) (hnn hL hpL l)
  have hLsym : L.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hL
  let t : EuclideanSpace ℝ V := hL.eigenvectorBasis (e l)
  have htact : L.toEuclideanLin t = 0 := by
    dsimp only [t]
    rw [hact hL (e l), heig hL l, hlast, zero_smul]
  have htvec : Matrix.mulVec (G.lapMatrix ℝ) ⇑t = 0 := by
    change Matrix.mulVec L ⇑t = 0
    dsimp only [t]
    rw [hL.mulVec_eigenvectorBasis (e l), heig hL l, hlast, zero_smul]
  have hconst (u w : V) : t u = t w :=
    (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp htvec) u w
      (h_guard.1.preconnected u w)
  obtain ⟨v0, hv0⟩ := G.exists_minimal_degree_vertex
  have ht0 : t v0 ≠ 0 := by
    intro h
    have htzero : t = 0 := by
      apply PiLp.ext
      intro w
      change t w = 0
      rw [hconst w v0, h]
    exact hL.eigenvectorBasis.orthonormal.ne_zero (e l) htzero
  have htt : inner ℝ t t = 1 := hL.eigenvectorBasis.inner_eq_one (e l)
  have hgap (z : EuclideanSpace ℝ V)
      (hz : inner ℝ (hL.eigenvectorBasis (e l)) z = 0) :
      a * ‖z‖ ^ 2 ≤ inner ℝ z (L.toEuclideanLin z) := by
    calc
      a * ‖z‖ ^ 2 =
          ∑ w : V, a * (inner ℝ (hL.eigenvectorBasis w) z) ^ 2 := by
        rw [← hL.eigenvectorBasis.sum_sq_inner_right z, Finset.mul_sum]
      _ ≤ ∑ w : V, hL.eigenvalues w * (inner ℝ (hL.eigenvectorBasis w) z) ^ 2 := by
        apply Finset.sum_le_sum
        intro w _
        by_cases hw : w = e l
        · simp [hw, hz]
        · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hne : e.symm w ≠ l := by
            intro hh
            apply hw
            calc
              w = e (e.symm w) := (e.apply_symm_apply w).symm
              _ = e l := congrArg e hh
          have hvalne : (e.symm w).val ≠ Fintype.card V - 1 := by
            intro hh
            apply hne
            exact Fin.ext hh
          have hij : e.symm w ≤ j := by
            change (e.symm w).val ≤ Fintype.card V - 2
            have hlt := (e.symm w).isLt
            omega
          calc
            a ≤ hL.eigenvalues₀ j := ha
            _ ≤ hL.eigenvalues₀ (e.symm w) := hL.eigenvalues₀_antitone hij
            _ = hL.eigenvalues w := by
              simpa only [Equiv.apply_symm_apply] using (heig hL (e.symm w)).symm
      _ = inner ℝ z (L.toEuclideanLin z) := by
        rw [← hL.eigenvectorBasis.sum_inner_mul_inner z (L.toEuclideanLin z)]
        apply Finset.sum_congr rfl
        intro w _
        have hc : inner ℝ (hL.eigenvectorBasis w) (L.toEuclideanLin z) =
            hL.eigenvalues w * inner ℝ (hL.eigenvectorBasis w) z := by
          rw [← hLsym (hL.eigenvectorBasis w) z, hact hL w, real_inner_smul_left]
        rw [hc, real_inner_comm z (hL.eigenvectorBasis w)]
        ring
  have hinner (u w : EuclideanSpace ℝ V) :
      inner ℝ u w = dotProduct ⇑u ⇑w := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dotProduct_comm _ _
  have htrace0 : 0 ≤ a + 2 * r :=
    add_nonneg ha0 (mul_nonneg (by norm_num) hr0)
  have hk : a + 2 * r ≤ k := le_max_right _ _
  have hkpos : 0 < k :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 (a + 2 * r))
  have hden : 0 < n * k := mul_pos hnpos hkpos
  apply csSup_le (Set.range_nonempty hQ.eigenvalues)
  rintro q ⟨i, rfl⟩
  let x : EuclideanSpace ℝ V := hQ.eigenvectorBasis i
  have hunit : (∑ w : V, (x w) ^ 2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    dsimp only [x]
    rw [hQ.eigenvectorBasis.norm_eq_one i, one_pow]
  let z : EuclideanSpace ℝ V := x - (inner ℝ t x) • t
  let T : ℝ := ∑ w : V, (z w) ^ 2
  have hT0 : 0 ≤ T := by
    dsimp only [T]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hzorth : inner ℝ t z = 0 := by
    dsimp only [z]
    rw [inner_sub_right, real_inner_smul_right, htt, mul_one, sub_self]
  have henergy : inner ℝ z (L.toEuclideanLin z) =
      inner ℝ x (L.toEuclideanLin x) := by
    dsimp only [z]
    rw [map_sub, map_smul, htact, smul_zero, sub_zero,
      inner_sub_left, real_inner_smul_left]
    rw [← hLsym t x, htact, inner_zero_left, mul_zero, sub_zero]
  have hzsum : (∑ w : V, z w) = 0 := by
    have hh : inner ℝ t z = t v0 * ∑ w : V, z w := by
      rw [hinner]
      change (∑ w : V, t w * z w) = t v0 * ∑ w : V, z w
      calc
        (∑ w : V, t w * z w) = ∑ w : V, t v0 * z w := by
          apply Finset.sum_congr rfl
          intro w _
          rw [hconst w v0]
        _ = t v0 * ∑ w : V, z w := (Finset.mul_sum _ _ _).symm
    rw [hzorth] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left ht0
  have hP : a * T ≤ inner ℝ x (L.toEuclideanLin x) := by
    have hh := hgap z hzorth
    rw [henergy, EuclideanSpace.real_norm_sq_eq] at hh
    exact hh
  have hsumErase : (∑ w ∈ Finset.univ.erase v0, z w) = -z v0 := by
    have hh := Finset.sum_erase_add Finset.univ (fun w : V => z w)
      (Finset.mem_univ v0)
    rw [hzsum] at hh
    linarith only [hh]
  have hsquareErase : (∑ w ∈ Finset.univ.erase v0, (z w) ^ 2) = T - (z v0) ^ 2 := by
    have hh := Finset.sum_erase_add Finset.univ (fun w : V => (z w) ^ 2)
      (Finset.mem_univ v0)
    change (∑ w ∈ Finset.univ.erase v0, (z w) ^ 2) + (z v0) ^ 2 = T at hh
    linarith only [hh]
  have hcardErase : ((Finset.univ.erase v0).card : ℝ) = n - 1 := by
    dsimp only [n]
    rw [Finset.card_erase_of_mem (Finset.mem_univ v0), Finset.card_univ,
      Nat.cast_sub (show 1 ≤ Fintype.card V from by omega), Nat.cast_one]
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase v0)
    (fun w : V => z w) (fun _ : V => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hC
  rw [hsumErase, hsquareErase, hcardErase] at hC
  simp only [neg_sq] at hC
  have hvvar : n * (z v0) ^ 2 ≤ (n - 1) * T := by
    nlinarith only [hC]
  have hdiff : (∑ w : V, (x w - x v0) ^ 2) ≤ n * T := by
    have hdiffeq : (∑ w : V, (x w - x v0) ^ 2) = T + n * (z v0) ^ 2 := by
      calc
        (∑ w : V, (x w - x v0) ^ 2) = ∑ w : V, (z w - z v0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro w _
          change (x w - x v0) ^ 2 =
            ((x w - inner ℝ t x * t w) - (x v0 - inner ℝ t x * t v0)) ^ 2
          rw [hconst w v0]
          ring
        _ = ∑ w : V, ((z w) ^ 2 - (2 * z v0) * z w + (z v0) ^ 2) := by
          apply Finset.sum_congr rfl
          intro w _
          ring
        _ = T + n * (z v0) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
            hzsum, mul_zero, sub_zero, Finset.sum_const, nsmul_eq_mul]
          simp only [Finset.card_univ, T, n]
    rw [hdiffeq]
    nlinarith only [hvvar]
  let E : ℝ := 2 * (G.maxDegree : ℝ) - hQ.eigenvalues i
  have hqe : hQ.eigenvalues i =
      dotProduct ⇑x (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) ⇑x) := by
    simpa only [x, star_trivial, RCLike.re_to_real] using hQ.eigenvalues_eq i
  have hdege : dotProduct ⇑x (Matrix.mulVec (G.degMatrix ℝ) ⇑x) =
      ∑ w : V, (G.degree w : ℝ) * (x w) ^ 2 := by
    rw [G.dotProduct_mulVec_degMatrix]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have hLE : inner ℝ x (L.toEuclideanLin x) =
      dotProduct ⇑x (Matrix.mulVec L ⇑x) := by
    rw [hinner]
    rfl
  have hs : (∑ w : V, 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2) =
      2 * (G.maxDegree : ℝ) - 2 * (∑ w : V, (G.degree w : ℝ) * (x w) ^ 2) := by
    calc
      (∑ w : V, 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2) =
          ∑ w : V, (2 * (G.maxDegree : ℝ) * (x w) ^ 2 -
            2 * ((G.degree w : ℝ) * (x w) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = 2 * (G.maxDegree : ℝ) * (∑ w : V, (x w) ^ 2) -
          2 * (∑ w : V, (G.degree w : ℝ) * (x w) ^ 2) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (G.maxDegree : ℝ) -
          2 * (∑ w : V, (G.degree w : ℝ) * (x w) ^ 2) := by
        rw [hunit, mul_one]
  have hE : E = inner ℝ x (L.toEuclideanLin x) +
      ∑ w : V, 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2 := by
    dsimp only [E]
    rw [hqe, Matrix.add_mulVec, dotProduct_add, hLE]
    simp only [L, SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub]
    rw [hdege, hs]
    ring
  have hterm (w : V) :
      0 ≤ 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (by exact_mod_cast G.degree_le_maxDegree w))) (sq_nonneg _)
  have hdefect : 2 * r * (x v0) ^ 2 ≤
      ∑ w : V, 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2 := by
    calc
      2 * r * (x v0) ^ 2 =
          2 * ((G.maxDegree : ℝ) - (G.degree v0 : ℝ)) * (x v0) ^ 2 := by
        dsimp only [r]
        rw [← hv0]
      _ ≤ ∑ w : V, 2 * ((G.maxDegree : ℝ) - (G.degree w : ℝ)) * (x w) ^ 2 :=
        Finset.single_le_sum (fun w _ => hterm w) (Finset.mem_univ v0)
  have hlower : a * T + 2 * r * (x v0) ^ 2 ≤ E :=
    (add_le_add hP hdefect).trans_eq hE.symm
  have hE0 : 0 ≤ E :=
    (add_nonneg (mul_nonneg ha0 hT0)
      (mul_nonneg (mul_nonneg (by norm_num) hr0) (sq_nonneg (x v0)))).trans hlower
  have hw (w : V) : a * (2 * r) * (x w) ^ 2 ≤
      (a + 2 * r) * (a * (x w - x v0) ^ 2 + 2 * r * (x v0) ^ 2) := by
    nlinarith only [sq_nonneg (a * (x w - x v0) - (2 * r) * x v0)]
  have hweighted : a * (2 * r) ≤
      (a + 2 * r) * (a * (∑ w : V, (x w - x v0) ^ 2) + n * (2 * r) * (x v0) ^ 2) := by
    calc
      a * (2 * r) = ∑ w : V, a * (2 * r) * (x w) ^ 2 := by
        rw [← Finset.mul_sum, hunit, mul_one]
      _ ≤ ∑ w : V, (a + 2 * r) *
          (a * (x w - x v0) ^ 2 + 2 * r * (x v0) ^ 2) :=
        Finset.sum_le_sum (fun w _ => hw w)
      _ = (a + 2 * r) *
          (a * (∑ w : V, (x w - x v0) ^ 2) + n * (2 * r) * (x v0) ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        simp only [n, mul_assoc]
  have htrace : a * (2 * r) ≤ n * (a + 2 * r) * E := by
    calc
      a * (2 * r) ≤ (a + 2 * r) *
          (a * (∑ w : V, (x w - x v0) ^ 2) + n * (2 * r) * (x v0) ^ 2) := hweighted
      _ ≤ (a + 2 * r) * (a * (n * T) + n * (2 * r) * (x v0) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hdiff ha0)
            (le_refl (n * (2 * r) * (x v0) ^ 2))) htrace0
      _ = n * (a + 2 * r) * (a * T + 2 * r * (x v0) ^ 2) := by ring
      _ ≤ n * (a + 2 * r) * E :=
        mul_le_mul_of_nonneg_left hlower (mul_nonneg hnpos.le htrace0)
  have hcross : 2 * a * r ≤ E * (n * k) := by
    calc
      2 * a * r = a * (2 * r) := by ring
      _ ≤ n * (a + 2 * r) * E := htrace
      _ ≤ n * k * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hnpos.le) hE0
      _ = E * (n * k) := by ring
  have hratio : (2 * a * r) / (n * k) ≤ E := (div_le_iff₀ hden).2 hcross
  dsimp only [E] at hratio
  linarith only [hratio]
