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

theorem model_64b918fcd8a802d68329 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) > (10000001 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))) := by
  classical
  have hconn : G.Connected := h_guard.1
  have hnR : (1 : ℝ) < (Fintype.card V : ℝ) := by
    linarith only [h_guard.2.2.1]
  have hnN : 1 < Fintype.card V := by
    exact_mod_cast hnR
  have hn : 2 ≤ Fintype.card V := by omega
  letI : Nonempty V := hconn.nonempty
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hnN
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let L : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
  have hL : L.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  have hgap : (10000001 / 10000000 : ℝ) <
      hL.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ := by
    simpa only [if_pos hconn, dif_pos hn] using h_guard.2.2.2
  have hentry (u v : V) : L u v =
      (Real.sqrt (G.degree u : ℝ))⁻¹ * G.lapMatrix ℝ u v *
        (Real.sqrt (G.degree v : ℝ))⁻¹ := by
    simp [L, D, Matrix.diagonal_conjTranspose]
  have hdiag (u : V) : L u u = 1 := by
    have hu : (0 : ℝ) < (G.degree u : ℝ) := by
      exact_mod_cast hconn.preconnected.degree_pos_of_nontrivial u
    have hs : Real.sqrt (G.degree u : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hu)
    have hsq := Real.mul_self_sqrt hu.le
    have hlap : G.lapMatrix ℝ u u = (G.degree u : ℝ) := by
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
    rw [hentry, hlap]
    field_simp [hs] <;> nlinarith only [hsq]
  have hoff {u v : V} (huv : u ≠ v) (hnot : ¬ G.Adj u v) : L u v = 0 := by
    rw [hentry]
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      Matrix.diagonal_apply, huv, hnot]
  let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := L.toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hL
  let b : OrthonormalBasis (Fin (Fintype.card V)) ℝ (EuclideanSpace ℝ V) :=
    hT.eigenvectorBasis finrank_euclideanSpace
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have hlarge (i : Fin (Fintype.card V)) (hi : i ≠ last) :
      1 < hL.eigenvalues₀ i := by
    have hneval : i.val ≠ Fintype.card V - 1 := by
      intro heq
      exact hi (Fin.ext heq)
    have hile : i ≤ (⟨Fintype.card V - 2, by omega⟩ : Fin (Fintype.card V)) := by
      change i.val ≤ Fintype.card V - 2
      have hil := i.isLt
      omega
    have hbound := hL.eigenvalues₀_antitone hile
    linarith only [hbound, hgap]
  have hrepr (x : EuclideanSpace ℝ V) (i : Fin (Fintype.card V)) :
      b.repr (T x) i = hL.eigenvalues₀ i * b.repr x i :=
    hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace x i
  have hstrict (x : EuclideanSpace ℝ V) (hx : x ≠ 0)
      (hlast : b.repr x last = 0) : inner ℝ x x < inner ℝ x (T x) := by
    have hsome : ∃ i, b.repr x i ≠ 0 := by
      by_contra hh
      push_neg at hh
      apply hx
      apply b.repr.injective
      apply PiLp.ext
      intro i
      simpa only [map_zero, PiLp.zero_apply] using hh i
    obtain ⟨i, hi⟩ := hsome
    have hine : i ≠ last := by
      intro heq
      exact hi (heq.symm ▸ hlast)
    have hdiff : inner ℝ x (T x) - inner ℝ x x =
        ∑ j : Fin (Fintype.card V), (hL.eigenvalues₀ j - 1) * (b.repr x j) ^ 2 := by
      rw [← b.repr.inner_map_map x (T x), ← b.repr.inner_map_map x x]
      simp only [PiLp.inner_apply, Real.inner_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hrepr]
      ring
    have hsum : 0 <
        ∑ j : Fin (Fintype.card V), (hL.eigenvalues₀ j - 1) * (b.repr x j) ^ 2 := by
      apply Finset.sum_pos'
      · intro j hj
        by_cases hje : j = last
        · rw [hje, hlast]
          simp
        · exact mul_nonneg (le_of_lt (sub_pos.mpr (hlarge j hje))) (sq_nonneg _)
      · exact ⟨i, Finset.mem_univ i,
          mul_pos (sub_pos.mpr (hlarge i hine)) (sq_pos_of_ne_zero hi)⟩
    linarith only [hdiff, hsum]
  have hsingle (u v : V) :
      inner ℝ (EuclideanSpace.single u 1) (T (EuclideanSpace.single v 1)) = L u v := by
    simp [T, Matrix.toLpLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, EuclideanSpace.inner_single_left]
  have hcomplete (u v : V) (huv : u ≠ v) : G.Adj u v := by
    by_contra hnot
    have huv0 : L u v = 0 := hoff huv hnot
    have hvu0 : L v u = 0 := hoff huv.symm (fun h => hnot h.symm)
    by_cases hzu : (b last) u = 0
    · let x : EuclideanSpace ℝ V := EuclideanSpace.single u 1
      have hx : x ≠ 0 := by
        change EuclideanSpace.single u (1 : ℝ) ≠ 0
        exact (PiLp.single_eq_zero_iff 2 u).not.mpr one_ne_zero
      have hl : b.repr x last = 0 := by
        rw [b.repr_apply_apply]
        simp [x, EuclideanSpace.inner_single_right, hzu]
      have hq : inner ℝ x (T x) = inner ℝ x x := by
        simp [x, hsingle, hdiag, EuclideanSpace.inner_single_left, PiLp.single_apply]
      have hh := hstrict x hx hl
      linarith only [hh, hq]
    · let x : EuclideanSpace ℝ V :=
        (b last) v • EuclideanSpace.single u 1 +
          (-((b last) u)) • EuclideanSpace.single v 1
      have hx : x ≠ 0 := by
        intro hh
        have hv := congrArg (fun w : EuclideanSpace ℝ V => w v) hh
        have hz : (b last) u = 0 := by
          simpa [x, PiLp.single_apply, huv, huv.symm, smul_eq_mul] using hv
        exact hzu hz
      have hl : b.repr x last = 0 := by
        rw [b.repr_apply_apply]
        simp only [x, inner_add_right, real_inner_smul_right,
          EuclideanSpace.inner_single_right, conj_trivial, one_mul]
        ring
      have hq : inner ℝ x (T x) = inner ℝ x x := by
        simp only [x, map_add, map_smul, RingHom.id_apply,
          inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hsingle]
        simp [hdiag, huv0, hvu0, EuclideanSpace.inner_single_left,
          PiLp.single_apply, huv, huv.symm] <;> ring
      have hh := hstrict x hx hl
      linarith only [hh, hq]
  have hmatrix : G.adjMatrix (ZMod 2) = Matrix.of 1 - 1 := by
    ext u v
    by_cases huv : u = v
    · subst v
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, huv, hcomplete u v huv]
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker A
  obtain ⟨a⟩ := hconn.nonempty
  have hrow (x : K) (u : V) : (∑ w : V, x.1 w) = x.1 u := by
    have hx := congrFun (LinearMap.mem_ker.mp x.property) u
    change Matrix.mulVec (G.adjMatrix (ZMod 2)) x.1 u = 0 at hx
    rw [hmatrix, Matrix.sub_mulVec, Matrix.one_mulVec] at hx
    have hh : (∑ w : V, x.1 w) - x.1 u = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hx
    exact sub_eq_zero.mp hh
  have hconst (x : K) (u : V) : x.1 u = x.1 a :=
    (hrow x u).symm.trans (hrow x a)
  let S : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj a).domRestrict K
  have hSi : Function.Injective S := by
    intro x y hxy
    change x.1 a = y.1 a at hxy
    apply Subtype.ext
    funext u
    exact (hconst x u).trans (hxy.trans (hconst y u).symm)
  have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
    simpa only [CommSemiring.finrank_self] using
      LinearMap.finrank_le_finrank_of_injective hSi
  have hrem (m : ℕ) : (m : ℝ) - 2 * (Int.floor ((m : ℝ) / 2) : ℝ) =
      ((m % 2 : ℕ) : ℝ) := by
    let q : ℕ := m / 2
    have hm : m = 2 * q + m % 2 := by
      dsimp [q]
      omega
    have hmr : (m : ℝ) = 2 * (q : ℝ) + ((m % 2 : ℕ) : ℝ) := by
      exact_mod_cast hm
    have hr0 : (0 : ℝ) ≤ ((m % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrlt : ((m % 2 : ℕ) : ℝ) < 2 := by
      exact_mod_cast (Nat.mod_lt m (by decide : 0 < (2 : ℕ)))
    have hfloor : Int.floor ((m : ℝ) / 2) = (q : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hmr, hr0, hrlt]
    rw [hfloor]
    push_cast
    linarith only [hmr]
  change (Module.finrank (ZMod 2) K : ℝ) =
    (Fintype.card V : ℝ) - 2 * (Int.floor ((Fintype.card V : ℝ) / 2) : ℝ)
  rw [hrem]
  rcases Nat.mod_two_eq_zero_or_one (Fintype.card V) with hn0 | hn1
  · have hncast : (Fintype.card V : ZMod 2) = 0 := by
      rw [← ZMod.natCast_mod (Fintype.card V) 2, hn0]
      rfl
    have hKzero (x : K) : x = 0 := by
      have hsum : (∑ w : V, x.1 w) = (Fintype.card V : ZMod 2) * x.1 a := by
        simp [hconst x, nsmul_eq_mul]
      have hx := hrow x a
      rw [hsum, hncast, zero_mul] at hx
      apply Subtype.ext
      funext u
      change x.1 u = 0
      exact (hconst x u).trans hx.symm
    letI : Subsingleton K := ⟨fun x y => (hKzero x).trans (hKzero y).symm⟩
    have hk : Module.finrank (ZMod 2) K = 0 := Module.finrank_zero_of_subsingleton
    rw [hk, hn0]
  · have hncast : (Fintype.card V : ZMod 2) = 1 := by
      rw [← ZMod.natCast_mod (Fintype.card V) 2, hn1]
      rfl
    let C0 : ZMod 2 →ₗ[ZMod 2] (V → ZMod 2) := LinearMap.const
    have hC0 (t : ZMod 2) : C0 t ∈ K := by
      rw [LinearMap.mem_ker]
      funext u
      change Matrix.mulVec (G.adjMatrix (ZMod 2)) (C0 t) u = 0
      rw [hmatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
      simp [C0, Matrix.mulVec, dotProduct, nsmul_eq_mul, hncast]
    let C : ZMod 2 →ₗ[ZMod 2] K := C0.codRestrict K hC0
    have hCi : Function.Injective C := by
      intro x y hxy
      have hh := congrArg (fun z : K => z.1 a) hxy
      change x = y at hh
      exact hh
    have hge1 : 1 ≤ Module.finrank (ZMod 2) K := by
      simpa only [CommSemiring.finrank_self] using
        LinearMap.finrank_le_finrank_of_injective hCi
    have hk : Module.finrank (ZMod 2) K = 1 := le_antisymm hle1 hge1
    rw [hk, hn1]
theorem model_3666c21f3f0671245865 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsTree) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))) := by
  sorry
