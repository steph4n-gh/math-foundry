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

theorem model_f625da6cfd36c5bd35d9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.floor ((G.cliqueNum : ℝ) / (2 : ℝ))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let q : ℕ := G.cliqueNum / 2
  obtain ⟨c, hc⟩ := G.exists_isNClique_cliqueNum
  have hq : 2 * q ≤ c.card := by
    rw [hc.card_eq]
    dsimp only [q]
    omega
  obtain ⟨s, hsc, hscard⟩ := Finset.exists_subset_card_eq (s := c) (n := 2 * q) hq
  have hsclique : G.IsClique (s : Set V) := by
    intro v hv w hw hne
    exact hc.isClique (hsc hv) (hsc hw) hne
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hzero (x : V → ZMod 2) (hx : A x = 0)
      (hout : ∀ v : V, v ∉ s → x v = 0) : x = 0 := by
    let z : ZMod 2 := ∑ w ∈ s, x w
    have hrow (v : V) (hv : v ∈ s) :
        A x v = ∑ w ∈ s.erase v, x w := by
      change (∑ w : V, (G.adjMatrix (ZMod 2)) v w * x w) = _
      calc
        _ = ∑ w ∈ s.erase v, (G.adjMatrix (ZMod 2)) v w * x w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ (s.erase v))
          intro w _ hw
          by_cases hws : w ∈ s
          · have hwv : w = v := by
              by_contra hne
              exact hw (Finset.mem_erase.mpr ⟨hne, hws⟩)
            subst w
            simp
          · rw [hout w hws, mul_zero]
        _ = ∑ w ∈ s.erase v, x w := by
          apply Finset.sum_congr rfl
          intro w hw
          have hw' := Finset.mem_erase.mp hw
          have hadj : G.Adj v w := hsclique hv hw'.2 (Ne.symm hw'.1)
          simp [hadj]
    have hval (v : V) (hv : v ∈ s) : x v = z := by
      have hr : (∑ w ∈ s.erase v, x w) = 0 := by
        have hh := congrFun hx v
        rw [hrow v hv] at hh
        exact hh
      have hh := Finset.sum_erase_add s x hv
      rw [hr, zero_add] at hh
      exact hh
    have hz : z = 0 := by
      calc
        z = ∑ w ∈ s, z := Finset.sum_congr rfl (fun w hw => hval w hw)
        _ = (s.card : ZMod 2) * z := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = 0 := by
          rw [hscard, Nat.cast_mul, Nat.cast_ofNat, htwo, zero_mul, zero_mul]
    funext v
    by_cases hv : v ∈ s
    · exact (hval v hv).trans hz
    · exact hout v hv
  let p : K →ₗ[ZMod 2] ((sᶜ : Finset V) → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) v.1
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hx : A (x : V → ZMod 2) = 0 := x.property
    have hy : A (y : V → ZMod 2) = 0 := y.property
    have hker : A ((x : V → ZMod 2) - (y : V → ZMod 2)) = 0 := by
      rw [map_sub, hx, hy, sub_self]
    have hout : ∀ v : V, v ∉ s →
        ((x : V → ZMod 2) - (y : V → ZMod 2)) v = 0 := by
      intro v hv
      have hh := congrFun hxy ⟨v, Finset.mem_compl.mpr hv⟩
      change (x : V → ZMod 2) v = (y : V → ZMod 2) v at hh
      simp only [Pi.sub_apply, hh, sub_self]
    exact sub_eq_zero.mp (hzero _ hker hout)
  have hdim : Module.finrank (ZMod 2) K ≤ (sᶜ).card := by
    calc
      _ ≤ Module.finrank (ZMod 2) ((sᶜ : Finset V) → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hinj
      _ = (sᶜ).card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hcount : s.card + (sᶜ).card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hnat : Module.finrank (ZMod 2) K + 2 * q ≤ Fintype.card V := by
    omega
  have hfloor : Int.floor ((G.cliqueNum : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    have hlo : 2 * q ≤ G.cliqueNum := by
      dsimp only [q]
      omega
    have hhi : G.cliqueNum < 2 * (q + 1) := by
      dsimp only [q]
      omega
    have hloR : (2 : ℝ) * (q : ℝ) ≤ (G.cliqueNum : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (G.cliqueNum : ℝ) < (2 : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast hhi
    constructor <;> simp only [Int.cast_natCast] <;> linarith only [hloR, hhiR]
  change (Module.finrank (ZMod 2) K : ℝ) +
    (2 : ℝ) * (Int.floor ((G.cliqueNum : ℝ) / 2) : ℝ) ≤ (Fintype.card V : ℝ)
  rw [hfloor, Int.cast_natCast]
  exact_mod_cast hnat

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]
theorem chung_normalized_laplacian_gap_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) ≤ ((Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - (1 : ℝ))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hsmall : Fintype.card V ≤ 1 := by omega
    have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hsmall
    linarith only [h_guard, hsmallR]
  have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hden : 0 < (Fintype.card V : ℝ) - 1 := by linarith only [hnR]
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  dsimp only
  by_cases hconn : G.Connected
  · rw [if_pos hconn, dif_pos hn]
    let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
    let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
    have hM : M.IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
    have hp : M.PosSemidef :=
      (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
    let f : Fin (Fintype.card V) → ℝ := hM.eigenvalues₀
    let e : Fin (Fintype.card V) ≃ V :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
    let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
    change f k ≤ (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1)
    have heig (i : Fin (Fintype.card V)) : hM.eigenvalues (e i) = f i := by
      simp only [Matrix.IsHermitian.eigenvalues, e, f, Equiv.symm_apply_apply]
    have hnn (i : Fin (Fintype.card V)) : 0 ≤ f i := by
      rw [← heig i, hM.eigenvalues_eq (e i)]
      simpa only [RCLike.re_to_real] using
        hp.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e i)))
    have hsum : (∑ i : Fin (Fintype.card V), f i) = M.trace := by
      calc
        _ = ∑ v : V, hM.eigenvalues v :=
          Fintype.sum_equiv e f hM.eigenvalues (fun i => (heig i).symm)
        _ = M.trace := hM.trace_eq_sum_eigenvalues.symm
    have hdet : M.det = 0 := by
      simp only [M, Matrix.det_mul, G.det_lapMatrix_eq_zero ℝ, mul_zero, zero_mul]
    have hprod : (∏ v : V, hM.eigenvalues v) = 0 := by
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using
        (hM.det_eq_prod_eigenvalues.symm.trans hdet)
    obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hz : f (e.symm v) = 0 := by
      rw [← heig (e.symm v), Equiv.apply_symm_apply]
      exact hv
    have hlz : e.symm v ≤ l := by
      change (e.symm v).val ≤ Fintype.card V - 1
      have hlt := (e.symm v).isLt
      omega
    have hlast : f l = 0 := by
      apply le_antisymm
      · calc
          f l ≤ f (e.symm v) := hM.eigenvalues₀_antitone hlz
          _ = 0 := hz
      · exact hnn l
    have hdiag (v : V) : M v v ≤ (1 : ℝ) := by
      have hentry : M v v =
          (Real.sqrt (G.degree v : ℝ))⁻¹ * (G.degree v : ℝ) *
            (Real.sqrt (G.degree v : ℝ))⁻¹ := by
        simp [M, D, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
      rw [hentry]
      by_cases hzero : (G.degree v : ℝ) = 0
      · simp [hzero]
      · have hsqrt : Real.sqrt (G.degree v : ℝ) ≠ 0 :=
          (Real.sqrt_ne_zero (Nat.cast_nonneg _)).mpr hzero
        calc
          _ = (Real.sqrt (G.degree v : ℝ))⁻¹ *
              (Real.sqrt (G.degree v : ℝ) * Real.sqrt (G.degree v : ℝ)) *
                (Real.sqrt (G.degree v : ℝ))⁻¹ := by
            rw [Real.mul_self_sqrt (Nat.cast_nonneg (G.degree v))]
          _ = 1 := by
            rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul, mul_inv_cancel₀ hsqrt]
          _ ≤ 1 := le_rfl
    have htrace : M.trace ≤ (Fintype.card V : ℝ) := by
      calc
        M.trace = ∑ v : V, M v v := rfl
        _ ≤ ∑ _v : V, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hdiag v)
        _ = (Fintype.card V : ℝ) := by simp
    let s : Finset (Fin (Fintype.card V)) := Finset.univ.erase l
    have hscard : s.card = Fintype.card V - 1 := by simp [s]
    have hs : (∑ i ∈ s, f i) = M.trace := by
      have h := Finset.sum_erase_add
        (Finset.univ : Finset (Fin (Fintype.card V))) f (Finset.mem_univ l)
      rw [hlast, add_zero] at h
      exact h.trans hsum
    have havg : ((Fintype.card V - 1 : ℕ) : ℝ) * f k ≤ M.trace := by
      calc
        _ = ∑ i ∈ s, f k := by
          simp only [Finset.sum_const, nsmul_eq_mul, hscard]
        _ ≤ ∑ i ∈ s, f i := by
          apply Finset.sum_le_sum
          intro i hi
          have hi_ne : i ≠ l := (Finset.mem_erase.mp hi).1
          have hival : i.val ≠ Fintype.card V - 1 := by
            intro heq
            exact hi_ne (Fin.ext heq)
          have hik : i ≤ k := by
            change i.val ≤ Fintype.card V - 2
            have hlt := i.isLt
            omega
          exact hM.eigenvalues₀_antitone hik
        _ = M.trace := hs
    have hnat : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply (le_div_iff₀ hden).mpr
    calc
      f k * ((Fintype.card V : ℝ) - 1) =
          ((Fintype.card V - 1 : ℕ) : ℝ) * f k := by rw [hnat, mul_comm]
      _ ≤ M.trace := havg
      _ ≤ (Fintype.card V : ℝ) := htrace
  · rw [if_neg hconn]
    exact div_nonneg (Nat.cast_nonneg _) hden.le
