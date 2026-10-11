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
theorem model_83f7fb63f03a8baa2809 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues))) + (((Fintype.card V : ℝ) - (2 : ℝ)) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))) ≤ (Fintype.card V : ℝ) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hleR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [h_guard.2, hleR]
  have hnzero : Fintype.card V ≠ 0 := by omega
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
  have hM : M.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  have hPSD : M.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hdiag (v : V) : M v v ≤ 1 := by
    have heq : M v v =
        (Real.sqrt (G.degree v : ℝ))⁻¹ * (G.degree v : ℝ) *
          (Real.sqrt (G.degree v : ℝ))⁻¹ := by
      dsimp only [M, D]
      rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
    rw [heq]
    by_cases hd : G.degree v = 0
    · simp [hd]
    · have hs : Real.sqrt (G.degree v : ℝ) ≠ 0 :=
        (Real.sqrt_ne_zero (Nat.cast_nonneg _)).2 (by exact_mod_cast hd)
      calc
        _ = (Real.sqrt (G.degree v : ℝ))⁻¹ *
            (Real.sqrt (G.degree v : ℝ) * Real.sqrt (G.degree v : ℝ)) *
            (Real.sqrt (G.degree v : ℝ))⁻¹ := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg (G.degree v))]
        _ = ((Real.sqrt (G.degree v : ℝ))⁻¹ * Real.sqrt (G.degree v : ℝ)) *
            (Real.sqrt (G.degree v : ℝ) * (Real.sqrt (G.degree v : ℝ))⁻¹) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hs, mul_inv_cancel₀ hs, mul_one]
        _ ≤ 1 := le_rfl
  have htrace : M.trace ≤ (Fintype.card V : ℝ) := by
    calc
      M.trace = ∑ v : V, M v v := rfl
      _ ≤ ∑ _v : V, (1 : ℝ) := Finset.sum_le_sum (fun v _ => hdiag v)
      _ = (Fintype.card V : ℝ) := by simp
  let e : V ≃ Fin (Fintype.card V) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm
  let f : Fin (Fintype.card V) → ℝ := hM.eigenvalues₀
  let a : Fin (Fintype.card V) := ⟨0, by omega⟩
  let b : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let c : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  have hnonneg (i : Fin (Fintype.card V)) : 0 ≤ f i := by
    have hi : hM.eigenvalues (e.symm i) = f i := by
      change f (e (e.symm i)) = f i
      rw [e.apply_symm_apply]
    rw [← hi, hM.eigenvalues_eq]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e.symm i)))
  have hsup : sSup (Set.range hM.eigenvalues) ≤ f a := by
    refine csSup_le ?_ ?_
    · exact ⟨hM.eigenvalues (e.symm a), ⟨e.symm a, rfl⟩⟩
    · rintro x ⟨v, rfl⟩
      change f (e v) ≤ f a
      apply hM.eigenvalues₀_antitone
      change 0 ≤ (e v).val
      exact Nat.zero_le _
  have hsum : (∑ i, f i) = M.trace := by
    calc
      _ = ∑ v : V, f (e v) := (e.sum_comp f).symm
      _ = ∑ v : V, hM.eigenvalues v := rfl
      _ = M.trace := by simpa using hM.trace_eq_sum_eigenvalues.symm
  have hba : b ≠ a := by
    intro h
    have hv := congrArg Fin.val h
    dsimp only [a, b] at hv
    omega
  have hbmem : b ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase a := by
    simp [hba]
  let s : Finset (Fin (Fintype.card V)) := (Finset.univ.erase a).erase b
  have hscard : s.card = Fintype.card V - 2 := by
    dsimp only [s]
    rw [Finset.card_erase_of_mem hbmem,
      Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hbound : ∀ i ∈ s, f c ≤ f i := by
    intro i hi
    have hib : i ≠ b := (Finset.mem_erase.mp hi).1
    have hival : i.val ≠ Fintype.card V - 1 := by
      intro hv
      apply hib
      exact Fin.ext hv
    apply hM.eigenvalues₀_antitone
    change i.val ≤ Fintype.card V - 2
    have hiLt := i.isLt
    omega
  have hmid : ((Fintype.card V : ℝ) - 2) * f c ≤ ∑ i ∈ s, f i := by
    have hh : (∑ _i ∈ s, f c) ≤ ∑ i ∈ s, f i := Finset.sum_le_sum hbound
    simpa only [Finset.sum_const, nsmul_eq_mul, hscard,
      Nat.cast_sub hn, Nat.cast_ofNat] using hh
  have hsplit : (∑ i ∈ s, f i) + f b + f a = ∑ i, f i := by
    exact (congrArg (fun x : ℝ => x + f a)
      (Finset.sum_erase_add (Finset.univ.erase a) f hbmem)).trans
      (Finset.sum_erase_add Finset.univ f (Finset.mem_univ a))
  have htarget : sSup (Set.range hM.eigenvalues) +
      ((Fintype.card V : ℝ) - 2) * f c ≤ (Fintype.card V : ℝ) := by
    have hb0 := hnonneg b
    linarith only [hsup, hmid, hsplit, hsum, htrace, hb0]
  simp only [hnzero, h_guard.1, hn, ↓reduceIte]
  exact htarget
