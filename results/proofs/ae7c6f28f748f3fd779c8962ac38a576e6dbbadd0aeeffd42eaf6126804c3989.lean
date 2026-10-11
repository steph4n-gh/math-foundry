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

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity

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

theorem hull3d_unique_neighbor_radius_ge_1_0_normalized_laplacian_spectral_gap_order_0_is_bipartite_f9946b253195 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) := by
  classical
  dsimp only
  by_cases hconn : G.Connected
  · rw [if_pos hconn]
    by_cases hn : 2 ≤ Fintype.card V
    · rw [dif_pos hn]
      haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
      let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
      have hsw : sw.Nonempty := by simp [sw]
      let q : V → ℝ := fun v => (Real.sqrt (G.degree v : ℝ))⁻¹
      let D : Matrix V V ℝ := Matrix.diagonal q
      let M : Matrix V V ℝ := D * G.lapMatrix ℝ * D.conjTranspose
      have hM : M.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
      let f : Fin (Fintype.card V) → ℝ := hM.eigenvalues₀
      let e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
      let k : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
      let l : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
      change f k ≤ ((sw.min' hsw - 1 : ℕ) : ℝ)
      have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
      have hden : 0 < (Fintype.card V : ℝ) - 1 := by linarith only [hnR]
      have hg : f k ≤ (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1) := by
        have hh := chung_normalized_laplacian_gap_upper G (by linarith only [hnR])
        dsimp only at hh
        rw [if_pos hconn, dif_pos hn] at hh
        exact hh
      have hratio : (Fintype.card V : ℝ) / ((Fintype.card V : ℝ) - 1) ≤ 2 := by
        apply (div_le_iff₀ hden).mpr
        linarith only [hnR]
      have hg2 : f k ≤ 2 := hg.trans hratio
      by_cases hlarge : 3 ≤ sw.min' hsw
      · have hrad : 2 ≤ sw.min' hsw - 1 := by omega
        have hradR : (2 : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) := by exact_mod_cast hrad
        exact hg2.trans hradR
      · have hsmall : sw.min' hsw ≤ 2 := by omega
        have hm : sw.min' hsw ∈ sw := Finset.min'_mem sw hsw
        rcases Finset.mem_union.mp hm with hm | hm
        · have heq : sw.min' hsw = Fintype.card V + 1 := Finset.mem_singleton.mp hm
          exfalso
          omega
        · obtain ⟨S, hS, hScard⟩ := Finset.mem_image.mp hm
          have hnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2.1
          have hstop : ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w) := (Finset.mem_filter.mp hS).2.2
          have hScardle : S.card ≤ 2 := by omega
          have hnotone : S.card ≠ 1 := by
            intro hone
            obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
            have hwS : w ∈ S := by rw [hw]; simp
            obtain ⟨v, hwv⟩ := (G.degree_pos_iff_exists_adj w).mp (hconn.preconnected.degree_pos_of_nontrivial w)
            apply hstop
            refine ⟨v, w, hwS, hwv.symm, ?_⟩
            intro u hu huv
            rw [hw] at hu
            exact Finset.mem_singleton.mp hu
          have htwo : S.card = 2 := by
            have hpos := hnonempty.card_pos
            omega
          have hmin2 : sw.min' hsw = 2 := hScard.symm.trans htwo
          obtain ⟨a, b, hab, hSpair⟩ := Finset.card_eq_two.mp htwo
          have htwins (v : V) : G.Adj v a ↔ G.Adj v b := by
            constructor
            · intro hva
              by_contra hvb
              apply hstop
              refine ⟨v, a, ?_, hva, ?_⟩
              · rw [hSpair]
                simp
              · intro u hu hvu
                have hu' : u = a ∨ u = b := by
                  simpa only [hSpair, Finset.mem_insert, Finset.mem_singleton] using hu
                rcases hu' with hua | hub
                · exact hua
                · subst u
                  exact (hvb hvu).elim
            · intro hvb
              by_contra hva
              apply hstop
              refine ⟨v, b, ?_, hvb, ?_⟩
              · rw [hSpair]
                simp
              · intro u hu hvu
                have hu' : u = a ∨ u = b := by
                  simpa only [hSpair, Finset.mem_insert, Finset.mem_singleton] using hu
                rcases hu' with hua | hub
                · subst u
                  exact (hva hvu).elim
                · exact hub
          let z : V → ℝ := Pi.single a 1 - Pi.single b 1
          have hAz : Matrix.mulVec (G.adjMatrix ℝ) z = 0 := by
            funext v
            simp only [z, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.sub_apply]
            change G.adjMatrix ℝ v a - G.adjMatrix ℝ v b = 0
            by_cases hva : G.Adj v a
            · have hvb := (htwins v).mp hva
              simp [hva, hvb]
            · have hvb : ¬ G.Adj v b := fun h => hva ((htwins v).mpr h)
              simp [hva, hvb]
          let r : V → ℝ := fun v => Real.sqrt (G.degree v : ℝ)
          have hrne (v : V) : r v ≠ 0 := by
            have hd : 0 < G.degree v := hconn.preconnected.degree_pos_of_nontrivial v
            have hdR : (0 : ℝ) < (G.degree v : ℝ) := by exact_mod_cast hd
            exact (Real.sqrt_ne_zero (Nat.cast_nonneg (G.degree v))).2 (ne_of_gt hdR)
          let x : V → ℝ := fun v => r v * z v
          have hza : z a = 1 := by simp [z, Pi.single_apply, hab, Ne.symm hab]
          have hxne : x ≠ 0 := by
            intro hx
            have hxa : r a * z a = 0 := congrFun hx a
            rw [hza, mul_one] at hxa
            exact hrne a hxa
          have hDself : D.conjTranspose = D := by
            simp only [D, Matrix.diagonal_conjTranspose, star_trivial]
          have hDx : Matrix.mulVec D x = z := by
            funext v
            simp only [D, Matrix.mulVec_diagonal]
            change (r v)⁻¹ * (r v * z v) = z v
            rw [← mul_assoc, inv_mul_cancel₀ (hrne v), one_mul]
          have hDz : Matrix.mulVec D (Matrix.mulVec (G.degMatrix ℝ) z) = x := by
            funext v
            simp only [D, Matrix.mulVec_diagonal, SimpleGraph.degMatrix_mulVec_apply]
            change (r v)⁻¹ * ((G.degree v : ℝ) * z v) = r v * z v
            have hsquare : r v * r v = (G.degree v : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg (G.degree v))
            rw [← hsquare]
            calc
              (r v)⁻¹ * ((r v * r v) * z v) = ((r v)⁻¹ * r v) * (r v * z v) := by ring
              _ = r v * z v := by rw [inv_mul_cancel₀ (hrne v), one_mul]
          have hMx : Matrix.mulVec M x = x := by
            calc
              Matrix.mulVec M x = Matrix.mulVec D (Matrix.mulVec (G.lapMatrix ℝ) (Matrix.mulVec D x)) := by
                simp only [M, hDself, Matrix.mulVec_mulVec, Matrix.mul_assoc]
              _ = Matrix.mulVec D (Matrix.mulVec (G.lapMatrix ℝ) z) := by rw [hDx]
              _ = Matrix.mulVec D (Matrix.mulVec (G.degMatrix ℝ) z) := by
                rw [SimpleGraph.lapMatrix, Matrix.sub_mulVec, hAz, sub_zero]
              _ = x := hDz
          have hspec : (1 : ℝ) ∈ spectrum ℝ M := by
            rw [← Matrix.spectrum_toLin']
            apply Module.End.HasEigenvalue.mem_spectrum
            refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hxne⟩
            apply Module.End.mem_genEigenspace_one.mpr
            simpa only [Matrix.toLin'_apply, one_smul] using hMx
          rw [hM.spectrum_real_eq_range_eigenvalues] at hspec
          obtain ⟨v, hv⟩ := hspec
          have heig (i : Fin (Fintype.card V)) : hM.eigenvalues (e i) = f i := by
            simp only [Matrix.IsHermitian.eigenvalues, e, f, Equiv.symm_apply_apply]
          have hp : M.PosSemidef := (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
          have hnn (i : Fin (Fintype.card V)) : 0 ≤ f i := by
            rw [← heig i, hM.eigenvalues_eq (e i)]
            simpa only [RCLike.re_to_real] using hp.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis (e i)))
          have hdet : M.det = 0 := by
            simp only [M, Matrix.det_mul, G.det_lapMatrix_eq_zero ℝ, mul_zero, zero_mul]
          have hprod : (∏ w : V, hM.eigenvalues w) = 0 := by
            simpa only [RCLike.ofReal_real_eq_id, id_eq] using (hM.det_eq_prod_eigenvalues.symm.trans hdet)
          obtain ⟨w, _, hw⟩ := Finset.prod_eq_zero_iff.mp hprod
          have hz : f (e.symm w) = 0 := by
            rw [← heig (e.symm w), Equiv.apply_symm_apply]
            exact hw
          have hwl : e.symm w ≤ l := by
            change (e.symm w).val ≤ Fintype.card V - 1
            have hlt := (e.symm w).isLt
            omega
          have hlast : f l = 0 := by
            apply le_antisymm
            · calc
                f l ≤ f (e.symm w) := hM.eigenvalues₀_antitone hwl
                _ = 0 := hz
            · exact hnn l
          have hvone : f (e.symm v) = 1 := by
            rw [← heig (e.symm v), Equiv.apply_symm_apply]
            exact hv
          have hne : e.symm v ≠ l := by
            intro hi
            have hbad := hvone
            rw [hi, hlast] at hbad
            norm_num at hbad
          have hindex : e.symm v ≤ k := by
            change (e.symm v).val ≤ Fintype.card V - 2
            have hlt := (e.symm v).isLt
            have hneval : (e.symm v).val ≠ Fintype.card V - 1 := by
              intro heq
              apply hne
              exact Fin.ext heq
            omega
          calc
            f k ≤ f (e.symm v) := hM.eigenvalues₀_antitone hindex
            _ = 1 := hvone
            _ = ((sw.min' hsw - 1 : ℕ) : ℝ) := by rw [hmin2]; norm_num
    · rw [dif_neg hn]
      exact unique_neighbor_radius_nonnegative G
  · rw [if_neg hconn]
    exact unique_neighbor_radius_nonnegative G
