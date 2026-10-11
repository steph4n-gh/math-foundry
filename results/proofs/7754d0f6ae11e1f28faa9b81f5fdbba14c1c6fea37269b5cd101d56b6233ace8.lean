import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
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

theorem model_e23944a6e66f4e3a45c2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ (¬ ((∃ d : ℕ, G.IsRegularOfDegree d))) ∧ ((Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (((Fintype.card V : ℝ) * ((G.maxDegree : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) * ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) + ((G.maxDegree : ℝ) - (G.minDegree : ℝ)))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * ((G.maxDegree : ℝ) - (G.minDegree : ℝ))) := by
  classical
  letI : Nonempty V := h_guard.1.nonempty
  have hnzero : Fintype.card V ≠ 0 := ne_of_gt Fintype.card_pos
  have hn2 : 2 ≤ Fintype.card V := by
    have hh : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      linarith only [h_guard.2.2]
    exact_mod_cast hh
  simp only [if_neg hnzero, if_pos h_guard.1, dif_pos hn2]
  let n : ℝ := Fintype.card V
  let M : ℝ := G.maxDegree
  let d : ℝ := M - (G.minDegree : ℝ)
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let hL := G.isHermitian_lapMatrix ℝ
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let a : ℝ := hL.eigenvalues₀ k
  change a * d ≤ n * (M - r) * (a + d)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hd : 0 ≤ d := by
    dsimp only [d, M]
    exact sub_nonneg.mpr (by exact_mod_cast G.minDegree_le_maxDegree)
  obtain ⟨w, hw⟩ := G.exists_minimal_degree_vertex
  let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
    (G.lapMatrix ℝ).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hL
  let B : OrthonormalBasis (Fin (Fintype.card V)) ℝ (EuclideanSpace ℝ V) :=
    hT.eigenvectorBasis finrank_euclideanSpace
  have hinner (u v : EuclideanSpace ℝ V) :
      inner ℝ u (T v) = dotProduct (⇑u) (Matrix.mulVec (G.lapMatrix ℝ) (⇑v)) := by
    change dotProduct (Matrix.mulVec (G.lapMatrix ℝ) (⇑v)) (star (⇑u)) =
      dotProduct (⇑u) (Matrix.mulVec (G.lapMatrix ℝ) (⇑v))
    rw [star_trivial, dotProduct_comm]
  have heig (j : Fin (Fintype.card V)) :
      T (B j) = hL.eigenvalues₀ j • B j := by
    exact hT.apply_eigenvectorBasis finrank_euclideanSpace j
  have heig_nonneg (j : Fin (Fintype.card V)) : 0 ≤ hL.eigenvalues₀ j := by
    have hh : 0 ≤ inner ℝ (B j) (T (B j)) := by
      rw [hinner]
      simpa only [star_trivial] using
        (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (⇑(B j))
    rw [heig j, inner_smul_right] at hh
    simpa only [OrthonormalBasis.inner_eq_one, mul_one] using hh
  have ha : 0 ≤ a := heig_nonneg k
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hzero_mem : (0 : ℝ) ∈ Set.range hL.eigenvalues := by
    rw [← hL.spectrum_real_eq_range_eigenvalues]
    exact G.zero_mem_spectrum_lapMatrix ℝ
  obtain ⟨z, hz⟩ := hzero_mem
  let z₀ : Fin (Fintype.card V) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm z
  have hz₀ : hL.eigenvalues₀ z₀ = 0 := hz
  have hzlast : z₀ ≤ last := by
    change z₀.val ≤ Fintype.card V - 1
    have hh := z₀.isLt
    omega
  have hlast_zero : hL.eigenvalues₀ last = 0 :=
    le_antisymm ((hL.eigenvalues₀_antitone hzlast).trans_eq hz₀)
      (heig_nonneg last)
  have hzeroq : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ)
      (⇑(B last)) (⇑(B last)) = 0 := by
    rw [Matrix.toLinearMap₂'_apply', ← hinner (B last) (B last),
      heig last, hlast_zero, zero_smul, inner_zero_right]
  have hconst_fun : (⇑(B last) : V → ℝ) = fun _ => B last w := by
    funext u
    exact (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable
      ℝ G (⇑(B last))).mp hzeroq u w (h_guard.1 u w)
  have hgap (y : V → ℝ) (hy : ∑ v : V, y v = 0) :
      a * (∑ v : V, y v ^ 2) ≤ dotProduct y (Matrix.mulVec (G.lapMatrix ℝ) y) := by
    let Y : EuclideanSpace ℝ V := WithLp.toLp 2 y
    have hc : B.repr Y last = 0 := by
      rw [B.repr_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      change dotProduct y (⇑(B last)) = 0
      rw [hconst_fun]
      simp only [dotProduct, ← Finset.sum_mul, hy, zero_mul]
    have hcoord (j : Fin (Fintype.card V)) :
        B.repr (T Y) j = hL.eigenvalues₀ j * B.repr Y j := by
      exact hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace Y j
    have hnormY : (∑ j : Fin (Fintype.card V), B.repr Y j ^ 2) =
        ∑ v : V, y v ^ 2 := by
      calc
        _ = ‖B.repr Y‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq _).symm
        _ = ‖Y‖ ^ 2 := by rw [B.repr.norm_map]
        _ = _ := EuclideanSpace.real_norm_sq_eq Y
    have henergyY :
        (∑ j : Fin (Fintype.card V), hL.eigenvalues₀ j * B.repr Y j ^ 2) =
          dotProduct y (Matrix.mulVec (G.lapMatrix ℝ) y) := by
      calc
        _ = inner ℝ (B.repr Y) (B.repr (T Y)) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
          change (∑ j : Fin (Fintype.card V), hL.eigenvalues₀ j * B.repr Y j ^ 2) =
            ∑ j : Fin (Fintype.card V), B.repr (T Y) j * B.repr Y j
          simp only [hcoord, pow_two, mul_assoc]
        _ = inner ℝ Y (T Y) := B.repr.inner_map_map Y (T Y)
        _ = _ := hinner Y Y
    have hh : a * (∑ j : Fin (Fintype.card V), B.repr Y j ^ 2) ≤
        ∑ j : Fin (Fintype.card V), hL.eigenvalues₀ j * B.repr Y j ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = last
      · subst j
        simp [hc]
      · have hjk : j ≤ k := by
          change j.val ≤ Fintype.card V - 2
          have hjlt := j.isLt
          have hjne : j.val ≠ Fintype.card V - 1 := by
            intro he
            exact hj (Fin.ext he)
          omega
        exact mul_le_mul_of_nonneg_right (hL.eigenvalues₀_antitone hjk)
          (sq_nonneg _)
    rw [hnormY, henergyY] at hh
    exact hh
  let hA := G.isHermitian_adjMatrix ℝ
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset V) hA.eigenvalues Finset.univ_nonempty
  have hi : hA.eigenvalues i = r := by
    apply le_antisymm
    · exact le_csSup (Set.finite_range hA.eigenvalues).bddAbove ⟨i, rfl⟩
    · apply csSup_le (Set.range_nonempty hA.eigenvalues)
      rintro _ ⟨j, rfl⟩
      exact hmax j (Finset.mem_univ j)
  let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
  have hnorm : (∑ v : V, x v ^ 2) = 1 := by
    calc
      _ = ‖hA.eigenvectorBasis i‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq _).symm
      _ = 1 := by simp
  have hx : Matrix.mulVec (G.adjMatrix ℝ) x = r • x := by
    simpa only [x, hi] using hA.mulVec_eigenvectorBasis i
  let E : ℝ := dotProduct x (Matrix.mulVec (G.lapMatrix ℝ) x)
  have hLx : Matrix.mulVec (G.lapMatrix ℝ) x =
      Matrix.mulVec (G.degMatrix ℝ) x - r • x := by
    rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, hx]
  have henergy_id : E + (∑ v : V, (M - (G.degree v : ℝ)) * x v ^ 2) = M - r := by
    calc
      _ = ∑ v : V, (x v * ((G.degree v : ℝ) * x v - r * x v) +
          (M - (G.degree v : ℝ)) * x v ^ 2) := by
        dsimp only [E]
        rw [hLx]
        simp only [dotProduct, Pi.sub_apply, SimpleGraph.degMatrix_mulVec_apply,
          Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_add_distrib]
      _ = ∑ v : V, (M - r) * x v ^ 2 := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = (M - r) * (∑ v : V, x v ^ 2) := (Finset.mul_sum _ _ _).symm
      _ = M - r := by rw [hnorm, mul_one]
  have hb (v : V) : 0 ≤ (M - (G.degree v : ℝ)) * x v ^ 2 := by
    apply mul_nonneg
    · apply sub_nonneg.mpr
      dsimp only [M]
      exact_mod_cast G.degree_le_maxDegree v
    · exact sq_nonneg _
  have hdefect : d * x w ^ 2 ≤ ∑ v : V, (M - (G.degree v : ℝ)) * x v ^ 2 := by
    calc
      d * x w ^ 2 = (M - (G.degree w : ℝ)) * x w ^ 2 := by
        dsimp only [d]
        rw [hw]
      _ ≤ _ := Finset.single_le_sum (fun v _ => hb v) (Finset.mem_univ w)
  let m : ℝ := (∑ v : V, x v) / n
  let y : V → ℝ := fun v => x v - m
  let S : ℝ := ∑ v : V, y v ^ 2
  have hm : n * m = ∑ v : V, x v := by
    dsimp only [m]
    field_simp [ne_of_gt hn] <;> ring
  have hsum_y : (∑ v : V, y v) = 0 := by
    change (∑ v : V, (x v - m)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ v : V, x v) - n * m = 0
    rw [hm, sub_self]
  have hS : 0 ≤ S := Finset.sum_nonneg (fun v _ => sq_nonneg (y v))
  have hvar : S + n * m ^ 2 = 1 := by
    have hs : S = (∑ v : V, x v ^ 2) - 2 * m * (∑ v : V, x v) + n * m ^ 2 := by
      calc
        S = ∑ v : V, (x v ^ 2 - 2 * m * x v + m ^ 2) := by
          dsimp only [S, y]
          apply Finset.sum_congr rfl
          intro v _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
    rw [hnorm, ← hm] at hs
    nlinarith only [hs]
  have hmean_energy : dotProduct y (Matrix.mulVec (G.lapMatrix ℝ) y) = E := by
    have hyfun : y = x - m • (1 : V → ℝ) := by
      ext v
      simp [y, smul_eq_mul]
    have hLy : Matrix.mulVec (G.lapMatrix ℝ) y =
        Matrix.mulVec (G.lapMatrix ℝ) x := by
      rw [hyfun, Matrix.mulVec_sub, Matrix.mulVec_smul,
        G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, sub_zero]
    have hone : dotProduct (1 : V → ℝ) (Matrix.mulVec (G.lapMatrix ℝ) x) = 0 := by
      rw [(G.isSymm_lapMatrix ℝ).dotProduct_mulVec_comm,
        G.lapMatrix_mulVec_one_eq_zero ℝ, dotProduct_zero]
    rw [hLy, hyfun, sub_dotProduct, smul_dotProduct, hone, smul_zero, sub_zero]
  have hP : a * S ≤ E := by
    have hh := hgap y hsum_y
    rw [hmean_energy] at hh
    exact hh
  have henergy : a * S + d * x w ^ 2 ≤ M - r := by
    linarith only [hP, hdefect, henergy_id]
  let F : Finset V := Finset.univ.erase w
  have hFcard : (F.card : ℝ) = n - 1 := by
    have hh : F.card + 1 = Fintype.card V := by
      simpa only [F, Finset.card_univ] using
        (Finset.card_erase_add_one (Finset.mem_univ w))
    have hhR : (F.card : ℝ) + 1 = n := by
      dsimp only [n]
      exact_mod_cast hh
    linarith only [hhR]
  have hFsum : (∑ v ∈ F, y v) = -y w := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset V) y (Finset.mem_univ w)
    change (∑ v ∈ F, y v) + y w = ∑ v : V, y v at hh
    rw [hsum_y] at hh
    linarith only [hh]
  have hFsq : (∑ v ∈ F, y v ^ 2) = S - y w ^ 2 := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset V)
      (fun v => y v ^ 2) (Finset.mem_univ w)
    change (∑ v ∈ F, y v ^ 2) + y w ^ 2 = S at hh
    linarith only [hh]
  have hC : n * y w ^ 2 ≤ (n - 1) * S := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq F y (fun _ : V => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hh
    rw [hFsum, hFsq, hFcard] at hh
    nlinarith only [hh]
  have hbound : a * d ≤ n * (a + d) * (a * S + d * x w ^ 2) := by
    have hsos : 0 ≤ n * (a * y w + d * x w) ^ 2 +
        a * (a + d) * ((n - 1) * S - n * y w ^ 2) + a ^ 2 * S := by
      apply add_nonneg
      · apply add_nonneg
        · exact mul_nonneg (le_of_lt hn) (sq_nonneg _)
        · exact mul_nonneg (mul_nonneg ha (add_nonneg ha hd))
            (sub_nonneg.mpr hC)
      · exact mul_nonneg (sq_nonneg a) hS
    have hid : n * (a + d) * (a * S + d * x w ^ 2) - a * d =
        n * (a * y w + d * x w) ^ 2 +
          a * (a + d) * ((n - 1) * S - n * y w ^ 2) + a ^ 2 * S := by
      calc
        _ = n * (a + d) * (a * S + d * x w ^ 2) - a * d * (S + n * m ^ 2) := by
          rw [hvar, mul_one]
        _ = _ := by
          dsimp only [y]
          ring
    rw [← hid] at hsos
    exact sub_nonneg.mp hsos
  calc
    a * d ≤ n * (a + d) * (a * S + d * x w ^ 2) := hbound
    _ ≤ n * (a + d) * (M - r) :=
      mul_le_mul_of_nonneg_left henergy
        (mul_nonneg (le_of_lt hn) (add_nonneg ha hd))
    _ = n * (M - r) * (a + d) := by ring
