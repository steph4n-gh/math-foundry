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

theorem model_f1abeb346d4f50c57240 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) := by
  classical
  rcases h_guard with ⟨hc, ⟨d, hd⟩, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hn : Fintype.card V ≤ 1 := by omega
    have hnr : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
  have hsum_real : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn0
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff hcard).2
    exact hsum_real.symm.trans (mul_comm _ _)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let N : Matrix V V ℝ := D * G.lapMatrix ℝ * Matrix.conjTranspose D
  let hN : N.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  simp only [if_neg hn0, if_pos hc, dif_pos htwo]
  change (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥
    (2 * ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) *
      (1 + max 0 (1 - hN.eigenvalues₀ j))
  rw [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : D = (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix V V ℝ) := by
    simp only [D, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hcoef : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hdnonneg]
  have hNsmul : N = (d : ℝ)⁻¹ • G.lapMatrix ℝ := by
    simp only [N, hD, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hcoef]
  have hdN : (d : ℝ) • N = G.lapMatrix ℝ := by
    rw [hNsmul, smul_smul, mul_inv_cancel₀ hdne, one_smul]
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    simp only [SimpleGraph.degMatrix, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hA : G.adjMatrix ℝ =
      (d : ℝ) • (1 : Matrix V V ℝ) - (d : ℝ) • N := by
    rw [hdN, SimpleGraph.lapMatrix, hdeg]
    abel
  let m : V → ℝ := fun v => (d : ℝ) * (1 - hN.eigenvalues v)
  let U := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hN.eigenvectorUnitary
  have hspec : N = U (Matrix.diagonal hN.eigenvalues) := by
    simpa [U] using hN.spectral_theorem
  have hdiag : Matrix.diagonal m =
      (d : ℝ) • (1 : Matrix V V ℝ) -
        (d : ℝ) • Matrix.diagonal hN.eigenvalues := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext v
    simp only [m, Pi.smul_apply, smul_eq_mul]
    ring
  have hAconj : G.adjMatrix ℝ = U (Matrix.diagonal m) := by
    rw [hdiag]
    simpa only [map_sub, map_smul, map_one, ← hspec] using hA
  have hcp : (G.adjMatrix ℝ).charpoly = (Matrix.diagonal m).charpoly := by
    rw [hAconj]
    change (((hN.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal m) *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)).charpoly =
        (Matrix.diagonal m).charpoly
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hroots :
      (Finset.univ : Finset V).val.map (G.isHermitian_adjMatrix ℝ).eigenvalues =
        (Finset.univ : Finset V).val.map m := by
    calc
      _ = (G.adjMatrix ℝ).charpoly.roots := by
        simpa using (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues.symm
      _ = (Matrix.diagonal m).charpoly.roots :=
        congrArg (fun p : Polynomial ℝ => p.roots) hcp
      _ = (Finset.univ : Finset V).val.map m := by
        rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
        · simp
        · exact Finset.prod_ne_zero_iff.mpr
            (fun v _ => Polynomial.X_sub_C_ne_zero (m v))
  have hsum : (∑ v : V, m v) = 0 := by
    have h := congrArg Multiset.sum hroots
    simp only [Finset.sum_map_val] at h
    rw [← h]
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have henergy : (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
      ∑ v : V, |m v| := by
    have h := congrArg
      (fun s : Multiset ℝ => (s.map (fun x : ℝ => |x|)).sum) hroots
    simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply] using h
  have hPSD : N.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg (v : V) : 0 ≤ hN.eigenvalues v := by
    rw [hN.eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hN.eigenvectorBasis v))
  have hzero : (0 : ℝ) ∈ spectrum ℝ N := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : V → ℝ))
      ⟨Module.End.mem_genEigenspace_one.mpr ?_, by simp⟩
    simp only [Matrix.toLin'_apply, hNsmul, Matrix.smul_mulVec,
      G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, zero_smul]
  rw [hN.spectrum_real_eq_range_eigenvalues] at hzero
  obtain ⟨z, hz⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have heig (i : Fin (Fintype.card V)) :
      hN.eigenvalues (e i) = hN.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hk0 : hN.eigenvalues₀ k = 0 := by
    have hk_nonneg : 0 ≤ hN.eigenvalues₀ k := by
      simpa only [heig] using hnonneg (e k)
    change hN.eigenvalues₀ (e.symm z) = 0 at hz
    have hzk : e.symm z ≤ k := by
      change (e.symm z).val ≤ Fintype.card V - 1
      have hzlt := (e.symm z).isLt
      omega
    exact le_antisymm ((hN.eigenvalues₀_antitone hzk).trans_eq hz) hk_nonneg
  have hmu_k : m (e k) = (d : ℝ) := by
    simp only [m, heig, hk0, sub_zero, mul_one]
  have hmu_j : m (e j) = (d : ℝ) * (1 - hN.eigenvalues₀ j) := by
    simp only [m, heig]
  have hne : e k ≠ e j := by
    intro h
    have hkj := e.injective h
    have hv := congrArg Fin.val hkj
    dsimp only [k, j] at hv
    omega
  have hpoint (v : V) : 0 ≤ |m v| + m v := by
    linarith [neg_abs_le (m v)]
  have hpair : (|m (e k)| + m (e k)) + (|m (e j)| + m (e j)) ≤
      ∑ v : V, (|m v| + m v) := by
    calc
      _ = ∑ v ∈ ({e k, e j} : Finset V), (|m v| + m v) :=
        (Finset.sum_pair hne).symm
      _ ≤ ∑ v : V, (|m v| + m v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ => hpoint v)
  simp only [Finset.sum_add_distrib, hsum, add_zero] at hpair
  simp only [hmu_k, hmu_j, abs_of_nonneg hdnonneg] at hpair
  rw [henergy]
  by_cases ht : 0 ≤ 1 - hN.eigenvalues₀ j
  · rw [max_eq_right ht]
    have hp : 0 ≤ (d : ℝ) * (1 - hN.eigenvalues₀ j) := mul_nonneg hdnonneg ht
    rw [abs_of_nonneg hp] at hpair
    nlinarith only [hpair]
  · have ht' : 1 - hN.eigenvalues₀ j ≤ 0 := (lt_of_not_ge ht).le
    rw [max_eq_left ht']
    have hp : (d : ℝ) * (1 - hN.eigenvalues₀ j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdnonneg ht'
    rw [abs_of_nonpos hp] at hpair
    nlinarith only [hpair]

theorem model_6bde2f687ba9b3e6e8a5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (max (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) ((((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * (((Fintype.card V : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))) / (max (1 : ℝ) ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))))) := by
  classical
  refine max_le (model_f1abeb346d4f50c57240 G h_guard) ?_
  rcases h_guard with ⟨hc, ⟨d, hd⟩, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hn : Fintype.card V ≤ 1 := by omega
    have hnr : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
  have hsum_real : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn0
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff hcard).2
    exact hsum_real.symm.trans (mul_comm _ _)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let N : Matrix V V ℝ := D * G.lapMatrix ℝ * Matrix.conjTranspose D
  let hN : N.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  simp only [if_neg hn0, if_pos hc, dif_pos htwo]
  change (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥
    (2 * ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) *
      (((Fintype.card V : ℝ) -
          (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
        ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
          max 0 (1 - hN.eigenvalues₀ j)) /
      max 1
        ((sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
          ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
            max 0 (1 - hN.eigenvalues₀ j))
  simp only [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul, zero_div]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : D = (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix V V ℝ) := by
    simp only [D, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hcoef : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hdnonneg]
  have hNsmul : N = (d : ℝ)⁻¹ • G.lapMatrix ℝ := by
    simp only [N, hD, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hcoef]
  have hdN : (d : ℝ) • N = G.lapMatrix ℝ := by
    rw [hNsmul, smul_smul, mul_inv_cancel₀ hdne, one_smul]
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    simp only [SimpleGraph.degMatrix, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hA : G.adjMatrix ℝ =
      (d : ℝ) • (1 : Matrix V V ℝ) - (d : ℝ) • N := by
    rw [hdN, SimpleGraph.lapMatrix, hdeg]
    abel
  let m : V → ℝ := fun v => (d : ℝ) * (1 - hN.eigenvalues v)
  let U := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hN.eigenvectorUnitary
  have hspec : N = U (Matrix.diagonal hN.eigenvalues) := by
    simpa [U] using hN.spectral_theorem
  have hdiag : Matrix.diagonal m =
      (d : ℝ) • (1 : Matrix V V ℝ) -
        (d : ℝ) • Matrix.diagonal hN.eigenvalues := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext v
    simp only [m, Pi.smul_apply, smul_eq_mul]
    ring
  have hAconj : G.adjMatrix ℝ = U (Matrix.diagonal m) := by
    rw [hdiag]
    simpa only [map_sub, map_smul, map_one, ← hspec] using hA
  have hcp : (G.adjMatrix ℝ).charpoly = (Matrix.diagonal m).charpoly := by
    rw [hAconj]
    change (((hN.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal m) *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)).charpoly =
        (Matrix.diagonal m).charpoly
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hroots :
      (Finset.univ : Finset V).val.map (G.isHermitian_adjMatrix ℝ).eigenvalues =
        (Finset.univ : Finset V).val.map m := by
    calc
      _ = (G.adjMatrix ℝ).charpoly.roots := by
        simpa using (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues.symm
      _ = (Matrix.diagonal m).charpoly.roots :=
        congrArg (fun p : Polynomial ℝ => p.roots) hcp
      _ = (Finset.univ : Finset V).val.map m := by
        rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
        · simp
        · exact Finset.prod_ne_zero_iff.mpr
            (fun v _ => Polynomial.X_sub_C_ne_zero (m v))
  have hsum : (∑ v : V, m v) = 0 := by
    have h := congrArg Multiset.sum hroots
    simp only [Finset.sum_map_val] at h
    rw [← h]
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have henergy : (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
      ∑ v : V, |m v| := by
    have h := congrArg
      (fun s : Multiset ℝ => (s.map (fun x : ℝ => |x|)).sum) hroots
    simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply] using h
  have hrange : Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues =
      Set.range m := by
    ext x
    have hx := congrArg (fun s : Multiset ℝ => x ∈ s) hroots
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and, Set.mem_range] using (Iff.of_eq hx)
  have htr (B : Matrix V V ℝ) : Matrix.trace (U B) = Matrix.trace B := by
    change Matrix.trace ((hN.eigenvectorUnitary : Matrix V V ℝ) * B *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hAA : G.adjMatrix ℝ * G.adjMatrix ℝ =
      U (Matrix.diagonal m * Matrix.diagonal m) := by
    rw [map_mul, ← hAconj]
  have hsquare : (∑ v : V, m v ^ 2) =
      (Fintype.card V : ℝ) * (d : ℝ) := by
    calc
      _ = Matrix.trace (Matrix.diagonal m * Matrix.diagonal m) := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]
      _ = Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) := by
        rw [hAA, htr]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self, hd.degree_eq,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hPSD : N.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg (v : V) : 0 ≤ hN.eigenvalues v := by
    rw [hN.eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hN.eigenvectorBasis v))
  have hzero : (0 : ℝ) ∈ spectrum ℝ N := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : V → ℝ))
      ⟨Module.End.mem_genEigenspace_one.mpr ?_, by simp⟩
    simp only [Matrix.toLin'_apply, hNsmul, Matrix.smul_mulVec,
      G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, zero_smul]
  rw [hN.spectrum_real_eq_range_eigenvalues] at hzero
  obtain ⟨z, hz⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have heig (i : Fin (Fintype.card V)) :
      hN.eigenvalues (e i) = hN.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hk0 : hN.eigenvalues₀ k = 0 := by
    have hk_nonneg : 0 ≤ hN.eigenvalues₀ k := by
      simpa only [heig] using hnonneg (e k)
    change hN.eigenvalues₀ (e.symm z) = 0 at hz
    have hzk : e.symm z ≤ k := by
      change (e.symm z).val ≤ Fintype.card V - 1
      have hzlt := (e.symm z).isLt
      omega
    exact le_antisymm ((hN.eigenvalues₀_antitone hzk).trans_eq hz) hk_nonneg
  have hmu_k : m (e k) = (d : ℝ) := by
    simp only [m, heig, hk0, sub_zero, mul_one]
  have hupper (v : V) : m v ≤ (d : ℝ) := by
    have hp := mul_nonneg hdnonneg (hnonneg v)
    dsimp only [m]
    nlinarith only [hp]
  have hmax : sSup (Set.range m) = (d : ℝ) := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty m)
      rintro x ⟨v, rfl⟩
      exact hupper v
    · rw [← hmu_k]
      exact le_csSup (Set.finite_range m).bddAbove ⟨e k, rfl⟩
  let a : ℝ := (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
  let b : ℝ := -sInf (Set.range m)
  let E : ℝ := ∑ v : V, |m v|
  have hEnonneg : 0 ≤ E := Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hlower (v : V) : -b ≤ m v := by
    simpa only [b, neg_neg] using
      (csInf_le (Set.finite_range m).bddBelow
        (show m v ∈ Set.range m from ⟨v, rfl⟩))
  have hcap (v : V) (hv : v ≠ e k) : m v ≤ a := by
    have hidx : e.symm v ≠ k := by
      intro hi
      apply hv
      simpa only [Equiv.apply_symm_apply] using congrArg e hi
    have hi : e.symm v ≤ j := by
      have hlt := (e.symm v).isLt
      have hval : (e.symm v).val ≠ Fintype.card V - 1 := by
        intro h
        exact hidx (Fin.ext h)
      change (e.symm v).val ≤ Fintype.card V - 2
      omega
    have hEigOrder := hN.eigenvalues₀_antitone hi
    change hN.eigenvalues₀ j ≤ hN.eigenvalues v at hEigOrder
    change (d : ℝ) * (1 - hN.eigenvalues v) ≤
      (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
    exact mul_le_mul_of_nonneg_left
      ((sub_le_sub_left hEigOrder 1).trans (le_max_right _ _)) hdnonneg
  have hpoint (v : V) : m v ^ 2 ≤
      (a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
        (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0) := by
    by_cases hv : v = e k
    · rw [hv, if_pos rfl, hmu_k, abs_of_nonneg hdnonneg]
      nlinarith only []
    · rw [if_neg hv, add_zero]
      by_cases hm : 0 ≤ m v
      · rw [abs_of_nonneg hm]
        have hp := mul_nonneg (sub_nonneg.mpr (hcap v hv)) hm
        nlinarith only [hp]
      · have hm' : m v ≤ 0 := (lt_of_not_ge hm).le
        rw [abs_of_nonpos hm']
        have hp := mul_nonneg
          (show 0 ≤ m v + b by linarith only [hlower v])
          (neg_nonneg.mpr hm')
        nlinarith only [hp]
  have hquad : (Fintype.card V : ℝ) * (d : ℝ) ≤
      (a + b) * E / 2 + (d : ℝ) ^ 2 - a * (d : ℝ) := by
    calc
      _ = ∑ v : V, m v ^ 2 := hsquare.symm
      _ ≤ ∑ v : V,
          ((a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
            (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0)) :=
        Finset.sum_le_sum (fun v _ => hpoint v)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_div, ← Finset.mul_sum, hsum, add_zero, sub_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, E]
        ring
  have hmono : (b + a) * E ≤ max 1 (b + a) * E :=
    mul_le_mul_of_nonneg_right (le_max_right 1 (b + a)) hEnonneg
  have hprod : (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) ≤
      E * max 1 (b + a) := by
    nlinarith only [hquad, hmono]
  have hdenpos : (0 : ℝ) < max 1 (b + a) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 (b + a))
  have hsecond :
      (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
        max 1 (b + a) ≤ E :=
    (div_le_iff₀ hdenpos).2 hprod
  rw [henergy, hrange, hmax]
  change E ≥
    (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
      max 1 (((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a)
  have hdenexpr : ((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a = b + a := by
    dsimp only [b]
    ring
  rw [hdenexpr]
  exact hsecond
theorem model_73adc8d60ed10eeee215 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) > (0 : ℝ) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hsmall : Fintype.card V ≤ 1 := by omega
    have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hsmall
    linarith only [h_guard.2, hsmallR]
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  dsimp only
  rw [if_pos h_guard.1, dif_pos hn]
  let q : V → ℝ := fun v => (Real.sqrt (G.degree v : ℝ))⁻¹
  let D : Matrix V V ℝ := Matrix.diagonal q
  let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
  have hM : M.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  have hPSD : M.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  change 0 < hM.eigenvalues₀ j
  have heig (i : Fin (Fintype.card V)) :
      hM.eigenvalues (e i) = hM.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hnonneg (i : Fin (Fintype.card V)) : 0 ≤ hM.eigenvalues₀ i := by
    rw [← heig i, hM.eigenvalues_eq (e i)]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e i)))
  by_contra hpos
  have hj0 : hM.eigenvalues₀ j = 0 :=
    le_antisymm (le_of_not_gt hpos) (hnonneg j)
  have hjk : j ≤ k := by
    change Fintype.card V - 2 ≤ Fintype.card V - 1
    omega
  have hk0 : hM.eigenvalues₀ k = 0 :=
    le_antisymm ((hM.eigenvalues₀_antitone hjk).trans_eq hj0) (hnonneg k)
  have hq (v : V) : q v ≠ 0 := by
    have hd : 0 < G.degree v :=
      h_guard.1.preconnected.degree_pos_of_nontrivial v
    have hdR : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast hd
    dsimp only [q]
    exact inv_ne_zero
      ((Real.sqrt_ne_zero (Nat.cast_nonneg (G.degree v))).2 (ne_of_gt hdR))
  have hDself : D.conjTranspose = D := by
    simp only [D, Matrix.diagonal_conjTranspose, star_trivial]
  have hinj (u : V → ℝ) (hu : Matrix.mulVec D u = 0) : u = 0 := by
    funext v
    have hv : q v * u v = 0 := by
      simpa only [D, Matrix.mulVec_diagonal, Pi.zero_apply] using congrFun hu v
    exact (mul_eq_zero.mp hv).resolve_left (hq v)
  have hconst (u : V → ℝ) (hu : Matrix.mulVec M u = 0) (v w : V) :
      q v * u v = q w * u w := by
    have hu' : Matrix.mulVec D
        (Matrix.mulVec (G.lapMatrix ℝ) (Matrix.mulVec D u)) = 0 := by
      simpa only [M, hDself, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hu
    have hL : Matrix.mulVec (G.lapMatrix ℝ) (Matrix.mulVec D u) = 0 := hinj _ hu'
    have hc := (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hL)
      v w (h_guard.1.preconnected v w)
    simpa only [D, Matrix.mulVec_diagonal] using hc
  let x : EuclideanSpace ℝ V := hM.eigenvectorBasis (e j)
  let y : EuclideanSpace ℝ V := hM.eigenvectorBasis (e k)
  have hx : Matrix.mulVec M (⇑x) = 0 := by
    simpa only [x, heig, hj0, zero_smul] using
      hM.mulVec_eigenvectorBasis (e j)
  have hy : Matrix.mulVec M (⇑y) = 0 := by
    simpa only [y, heig, hk0, zero_smul] using
      hM.mulVec_eigenvectorBasis (e k)
  let α : ℝ := q (e j) * x (e j)
  let β : ℝ := q (e j) * y (e j)
  have hxconst (v : V) : q v * x v = α := hconst ⇑x hx v (e j)
  have hyconst (v : V) : q v * y v = β := hconst ⇑y hy v (e j)
  have hα : α ≠ 0 := by
    intro ha
    apply hM.eigenvectorBasis.orthonormal.ne_zero (e j)
    change x = 0
    apply PiLp.ext
    intro v
    exact (mul_eq_zero.mp ((hxconst v).trans ha)).resolve_left (hq v)
  have hlin : α • y = β • x := by
    apply PiLp.ext
    intro v
    change α * y v = β * x v
    apply mul_left_cancel₀ (hq v)
    calc
      q v * (α * y v) = α * (q v * y v) := by ring
      _ = α * β := by rw [hyconst v]
      _ = β * α := mul_comm _ _
      _ = β * (q v * x v) := by rw [hxconst v]
      _ = q v * (β * x v) := by ring
  have hsame : e k = e j :=
    hM.eigenvectorBasis.orthonormal.linearIndependent.eq_of_smul_apply_eq_smul_apply
      α β (e k) (e j) hα hlin
  have hval := congrArg Fin.val (e.injective hsame)
  dsimp only [j, k] at hval
  omega
