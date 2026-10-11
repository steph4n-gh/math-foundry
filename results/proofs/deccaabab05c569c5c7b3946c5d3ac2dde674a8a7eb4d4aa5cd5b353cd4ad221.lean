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

theorem model_de47993e34075cfd3cba {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((1 : ℝ) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * ((2 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))))) := by
  classical
  let n : ℕ := Fintype.card V
  let d : ℕ := G.minDegree
  let M : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := M.mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) K
  change (k : ℝ) ≥ (1 - ((d : ℝ) - 2 * (Int.floor ((d : ℝ) / 2) : ℝ))) *
    (2 - ((n : ℝ) - 2 * (Int.floor ((n : ℝ) / 2) : ℝ)))
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
  rw [hrem d, hrem n]
  rcases Nat.mod_two_eq_zero_or_one d with he | ho
  · simp only [he, Nat.cast_zero, sub_zero, one_mul]
    have hdpos : 0 < d := by
      have h : (0 : ℝ) < (d : ℝ) := by
        change (0 : ℝ) < (G.minDegree : ℝ)
        linarith only [h_guard.2]
      exact_mod_cast h
    haveI : Nonempty V := by
      rcases isEmpty_or_nonempty V with h | h
      · letI : IsEmpty V := h
        have hz : d = 0 := by simp [d]
        omega
      · exact h
    obtain ⟨a⟩ := ‹Nonempty V›
    have hnpos : 0 < n := Fintype.card_pos
    obtain ⟨r, hr⟩ := h_guard.1
    have hdegree (v : V) : G.degree v = d :=
      (hr.degree_eq v).trans hr.minDegree_eq.symm
    have hd0 : (d : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr he)
    have hone : A (1 : V → ZMod 2) = 0 := by
      funext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2))
        (Function.const V (1 : ZMod 2))) v = 0
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hdegree v, hd0, mul_one]
    let c : K := ⟨(1 : V → ZMod 2), hone⟩
    have hc : c ≠ 0 := by
      intro h
      have hh := congrArg (fun z : K => z.1 a) h
      change (1 : ZMod 2) = 0 at hh
      exact one_ne_zero hh
    have hge1 : 1 ≤ k := by
      have hpos : 0 < Module.finrank (ZMod 2) K :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨c, hc⟩
      change 1 ≤ Module.finrank (ZMod 2) K
      omega
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have hge2 : 2 ≤ k := by
        by_contra h
        have hk1 : Module.finrank (ZMod 2) K = 1 := by
          change k = 1
          omega
        let s : Finset V := ({a} : Finset V)ᶜ
        have hscard : Fintype.card s = n - 1 := by
          simp only [Fintype.card_coe, s, Finset.card_compl,
            Finset.card_singleton, n]
        have hsodd : Odd (Fintype.card s) := by
          apply Nat.not_even_iff_odd.mp
          intro hs
          have hmod : Fintype.card s % 2 = 0 := Nat.even_iff.mp hs
          omega
        let B : Matrix s s (ZMod 2) := fun i j => M (i : V) (j : V)
        have hM : M.IsSymm := G.isSymm_adjMatrix
        have hBsymm (i j : s) : B i j = B j i :=
          hM.apply (j : V) (i : V)
        have hBdiag (i : s) : B i i = 0 := by simp [B, M]
        have htwo (t : ZMod 2) : t + t = 0 := by
          simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel t
        have hdet : B.det = 0 := by
          let F : Equiv.Perm s → ZMod 2 := fun σ =>
            Equiv.Perm.sign σ • ∏ i : s, B (σ i) i
          have hFinv (σ : Equiv.Perm s) : F σ⁻¹ = F σ := by
            dsimp only [F]
            rw [Equiv.Perm.sign_inv]
            apply congrArg (fun z : ZMod 2 => Equiv.Perm.sign σ • z)
            apply Fintype.prod_equiv σ.symm
            intro i
            simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using
              hBsymm (σ.symm i) i
          have hFzero (σ : Equiv.Perm s) (hσ : σ⁻¹ = σ) : F σ = 0 := by
            have hfix : ∃ i : s, σ i = i := by
              by_contra hno
              have hnf (i : s) : σ i ≠ i := fun hi => hno ⟨i, hi⟩
              have hinvol (i : s) : σ (σ i) = i := by
                calc
                  σ (σ i) = σ⁻¹ (σ i) :=
                    congrArg (fun τ : Equiv.Perm s => τ (σ i)) hσ.symm
                  _ = i := σ.symm_apply_apply i
              have hsum : (∑ i : s, (1 : ZMod 2)) = 0 := by
                apply Finset.sum_ninvolution (fun i : s => σ i)
                · intro i
                  exact htwo 1
                · intro i hi
                  exact hnf i
                · intro i
                  exact Finset.mem_univ _
                · exact hinvol
              have hcard : (Fintype.card s : ZMod 2) = 0 := by
                simpa using hsum
              exact (Nat.not_even_iff_odd.mpr hsodd)
                (ZMod.natCast_eq_zero_iff_even.mp hcard)
            obtain ⟨i, hi⟩ := hfix
            have hprod : (∏ j : s, B (σ j) j) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ i)
              rw [hi]
              exact hBdiag i
            dsimp only [F]
            rw [hprod, smul_zero]
          rw [Matrix.det_apply]
          change (∑ σ : Equiv.Perm s, F σ) = 0
          apply Finset.sum_ninvolution (fun σ : Equiv.Perm s => σ⁻¹)
          · intro σ
            rw [hFinv]
            exact htwo _
          · intro σ hne hfix
            exact hne (hFzero σ hfix)
          · intro σ
            exact Finset.mem_univ _
          · intro σ
            exact inv_inv σ
        have htrivial (z : s → ZMod 2) (hz : B.mulVecLin z = 0) : z = 0 := by
          let y : V → ZMod 2 := fun v =>
            if hv : v ∈ s then z ⟨v, hv⟩ else 0
          have hya : y a = 0 := by simp [y, s]
          have hrow (v : s) : A y (v : V) = B.mulVecLin z v := by
            change (∑ w : V, M (v : V) w * y w) =
              ∑ w : s, M (v : V) (w : V) * z w
            calc
              _ = ∑ w ∈ s, M (v : V) w * y w := by
                symm
                apply Finset.sum_subset (Finset.subset_univ s)
                intro w hw hws
                simp [y, hws]
              _ = ∑ w : s, M (v : V) (w : V) * y (w : V) :=
                (Finset.sum_coe_sort s (fun w => M (v : V) w * y w)).symm
              _ = ∑ w : s, M (v : V) (w : V) * z w := by
                apply Finset.sum_congr rfl
                intro w hw
                simp [y, w.property]
          have hrows (v : s) : A y (v : V) = 0 :=
            (hrow v).trans (congrFun hz v)
          have hsum : (∑ v : V, A y v) = 0 := by
            have hh := hM.dotProduct_mulVec_comm
              (x := (1 : V → ZMod 2)) (y := y)
            change dotProduct (1 : V → ZMod 2) (A y) =
              dotProduct y (A (1 : V → ZMod 2)) at hh
            simpa only [hone, one_dotProduct, dotProduct_zero] using hh
          have hsuma : (∑ v : V, A y v) = A y a := by
            apply Finset.sum_eq_single a
            · intro v hv hva
              exact hrows ⟨v, by simp [s, hva]⟩
            · intro ha
              exact (ha (Finset.mem_univ a)).elim
          have hrowa : A y a = 0 := hsuma.symm.trans hsum
          have hyA : A y = 0 := by
            funext v
            change A y v = 0
            by_cases hva : v = a
            · simpa only [hva] using hrowa
            · exact hrows ⟨v, by simp [s, hva]⟩
          obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hk1 hc (⟨y, hyA⟩ : K)
          have ht0 : t = 0 := by
            have hh := congrArg (fun z : K => z.1 a) ht
            change t • (1 : ZMod 2) = y a at hh
            simpa only [smul_eq_mul, mul_one, hya] using hh
          have hyzero : y = 0 := by
            have hh := congrArg (fun z : K => z.1) ht
            change t • (1 : V → ZMod 2) = y at hh
            simpa only [ht0, zero_smul] using hh.symm
          funext v
          have hh := congrFun hyzero (v : V)
          simpa [y, v.property] using hh
        have hBi : Function.Injective B.mulVec := by
          intro z w hzw
          apply sub_eq_zero.mp
          apply htrivial
          change Matrix.mulVec B (z - w) = 0
          rw [Matrix.mulVec_sub, hzw, sub_self]
        have hunit : IsUnit B.det :=
          (Matrix.isUnit_iff_isUnit_det B).mp
            (Matrix.mulVec_injective_iff_isUnit.mp hBi)
        rw [hdet] at hunit
        exact not_isUnit_zero hunit
      have hR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge2
      simpa only [hn0, Nat.cast_zero, sub_zero] using hR
    · have hR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge1
      simp only [hn1, Nat.cast_one]
      linarith only [hR]
  · simp only [ho, Nat.cast_one, sub_self, zero_mul]
    exact Nat.cast_nonneg k

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem model_86d5f85f179c31163952 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let E : (s → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x v => if hv : v ∈ s then x ⟨v, hv⟩ else 0
      map_add' := by
        intro x y
        funext v
        by_cases hv : v ∈ s <;> simp [hv]
      map_smul' := by
        intro c x
        funext v
        by_cases hv : v ∈ s <;> simp [hv] }
  have hE : Function.Injective E := by
    intro x y hxy
    funext v
    have h := congrFun hxy (v : V)
    simpa [E, v.property] using h
  have hzero (x : s → ZMod 2) (v : V) (hv : v ∈ s) :
      A (E x) v = 0 := by
    change (∑ w : V, G.adjMatrix (ZMod 2) v w * E x w) = 0
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hws : w ∈ s
    · have hnot : ¬ G.Adj v w := by
        intro hadj
        exact ((SimpleGraph.compl_adj G v w).mp
          (hs.isClique hv hws hadj.ne)).2 hadj
      simp [SimpleGraph.adjMatrix_apply, hnot]
    · simp [E, hws]
  let f : (s → ZMod 2) →ₗ[ZMod 2] (↥(sᶜ) → ZMod 2) :=
    { toFun := fun x v => A (E x) (v : V)
      map_add' := by
        intro x y
        funext v
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext v
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hker : ∀ x : LinearMap.ker f,
      E (x : s → ZMod 2) ∈ LinearMap.ker A := by
    intro x
    rw [LinearMap.mem_ker]
    funext v
    change A (E (x : s → ZMod 2)) v = 0
    by_cases hv : v ∈ s
    · exact hzero (x : s → ZMod 2) v hv
    · have hx := congrFun (LinearMap.mem_ker.mp x.property)
        (⟨v, Finset.mem_compl.mpr hv⟩ : ↥(sᶜ))
      exact hx
  let e : LinearMap.ker f →ₗ[ZMod 2] LinearMap.ker A :=
    (E.domRestrict (LinearMap.ker f)).codRestrict (LinearMap.ker A) hker
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply hE
    exact congrArg (fun z : LinearMap.ker A => (z : V → ZMod 2)) hxy
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) ≤ sᶜ.card := by
    calc
      _ ≤ Module.finrank (ZMod 2) (↥(sᶜ) → ZMod 2) := Submodule.finrank_le _
      _ = sᶜ.card := by
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) +
      Module.finrank (ZMod 2) (LinearMap.ker f) = s.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker f
  have hcards : s.card + sᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hsize : s.card = Gᶜ.cliqueNum := hs.card_eq
  have hnat : 2 * Gᶜ.cliqueNum ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) + Fintype.card V := by
    omega
  have hreal : (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) ≤
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) + (Fintype.card V : ℝ) := by
    exact_mod_cast hnat
  change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) ≥
    (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) - (Fintype.card V : ℝ)
  linarith

theorem model_45f837d4bac6b9091532 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((2 : ℝ) * ((Int.floor ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) / (2 : ℝ))) : ℝ)) := by
  classical
  have hnposR : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have hbound := parity_code_dimension_le_order G
    linarith only [hbound, h_guard.2.2.2]
  have hnpos : 0 < Fintype.card V := by exact_mod_cast hnposR
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  obtain ⟨d, hreg⟩ := h_guard.2.1
  have hdpos : 0 < d := by
    have h : (0 : ℝ) < (G.minDegree : ℝ) := by
      linarith only [h_guard.2.2.1]
    rw [hreg.minDegree_eq] at h
    exact_mod_cast h
  obtain ⟨c⟩ := h_guard.1
  let s : Finset V := Finset.univ.filter (fun v => c v = 0)
  let t : Finset V := sᶜ
  have hs0 (v : V) (hv : v ∈ s) : c v = 0 :=
    (Finset.mem_filter.mp hv).2
  have ht1 (v : V) (hv : v ∈ t) : c v = 1 := by
    have hv0 : c v ≠ 0 := by
      intro h
      have hvs : v ∈ s := by simp [s, h]
      exact (Finset.mem_compl.mp hv) hvs
    have hval : (c v).val ≠ 0 := by
      intro h
      exact hv0 (Fin.ext h)
    have hlt := (c v).isLt
    apply Fin.ext
    change (c v).val = 1
    omega
  have hbip : G.IsBipartiteWith (s : Set V) (t : Set V) := by
    refine ⟨?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro v hvs hvt
      exact (Finset.mem_compl.mp hvt) hvs
    · intro v w hvw
      by_cases hv : v ∈ s
      · left
        refine ⟨hv, ?_⟩
        change w ∈ sᶜ
        apply Finset.mem_compl.mpr
        intro hw
        exact c.valid hvw ((hs0 v hv).trans (hs0 w hw).symm)
      · right
        refine ⟨Finset.mem_compl.mpr hv, ?_⟩
        by_contra hw
        have hvt : v ∈ t := Finset.mem_compl.mpr hv
        have hwt : w ∈ t := Finset.mem_compl.mpr hw
        exact c.valid hvw ((ht1 v hvt).trans (ht1 w hwt).symm)
  have hmult : s.card * d = t.card * d := by
    calc
      _ = ∑ v ∈ s, G.degree v :=
        (Finset.sum_const_nat (fun v _ => hreg.degree_eq v)).symm
      _ = ∑ v ∈ t, G.degree v :=
        SimpleGraph.isBipartiteWith_sum_degrees_eq hbip
      _ = _ := Finset.sum_const_nat (fun v _ => hreg.degree_eq v)
  have hbalanced : s.card = t.card := Nat.mul_right_cancel hdpos hmult
  have hcards : s.card + t.card = Fintype.card V :=
    Finset.card_add_card_compl s
  let M := G.adjMatrix (ZMod 2)
  let A := M.mulVecLin
  let K := LinearMap.ker A
  let E (u : Finset V) : (u → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x v => if hv : v ∈ u then x ⟨v, hv⟩ else 0
      map_add' := by
        intro x y
        funext v
        by_cases hv : v ∈ u <;> simp [hv]
      map_smul' := by
        intro c x
        funext v
        by_cases hv : v ∈ u <;> simp [hv] }
  have hE (u : Finset V) : Function.Injective (E u) := by
    intro x y hxy
    funext v
    have h := congrFun hxy (v : V)
    simpa [E, v.property] using h
  have hs_zero (v w : V) (hv : v ∈ s) (hw : w ∈ s) : M v w = 0 := by
    have hnot : ¬ G.Adj v w := by
      intro h
      exact c.valid h ((hs0 v hv).trans (hs0 w hw).symm)
    simp [M, SimpleGraph.adjMatrix_apply, hnot]
  have ht_zero (v w : V) (hv : v ∈ t) (hw : w ∈ t) : M v w = 0 := by
    have hnot : ¬ G.Adj v w := by
      intro h
      exact c.valid h ((ht1 v hv).trans (ht1 w hw).symm)
    simp [M, SimpleGraph.adjMatrix_apply, hnot]
  have hsym (v w : V) : M v w = M w v :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply w v
  have hrow (u : Finset V) (x : u → ZMod 2) (v : V) :
      A (E u x) v = ∑ w : u, M v (w : V) * x w := by
    change (∑ w : V, M v w * (E u x) w) = _
    calc
      _ = ∑ w ∈ u, M v w * (E u x) w := by
        symm
        apply Finset.sum_subset (Finset.subset_univ u)
        intro w _ hw
        simp [E, hw]
      _ = ∑ w : u, M v (w : V) * (E u x) (w : V) :=
        (Finset.sum_coe_sort u (fun w => M v w * (E u x) w)).symm
      _ = ∑ w : u, M v (w : V) * x w := by
        apply Finset.sum_congr rfl
        intro w _
        simp [E, w.property]
  let B : Matrix t s (ZMod 2) := fun v w => M (v : V) (w : V)
  have hAs : A.comp (E s) = (E t).comp B.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext v
    change A (E s x) v = (E t (B.mulVecLin x)) v
    rw [hrow]
    by_cases hv : v ∈ s
    · rw [show (E t (B.mulVecLin x)) v = 0 by simp [E, t, hv]]
      apply Finset.sum_eq_zero
      intro w _
      rw [hs_zero v (w : V) hv w.property, zero_mul]
    · have hvt : v ∈ t := Finset.mem_compl.mpr hv
      rw [show (E t (B.mulVecLin x)) v = B.mulVecLin x ⟨v, hvt⟩ by
        simp [E, hvt]]
      rfl
  have hAt : A.comp (E t) = (E s).comp B.transpose.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext v
    change A (E t x) v = (E s (B.transpose.mulVecLin x)) v
    rw [hrow]
    by_cases hv : v ∈ s
    · rw [show (E s (B.transpose.mulVecLin x)) v =
          B.transpose.mulVecLin x ⟨v, hv⟩ by simp [E, hv]]
      change (∑ w : t, M v (w : V) * x w) =
        ∑ w : t, M (w : V) v * x w
      apply Finset.sum_congr rfl
      intro w _
      rw [hsym v (w : V)]
    · rw [show (E s (B.transpose.mulVecLin x)) v = 0 by simp [E, hv]]
      have hvt : v ∈ t := Finset.mem_compl.mpr hv
      apply Finset.sum_eq_zero
      intro w _
      rw [ht_zero v (w : V) hvt w.property, zero_mul]
  have hrs : Module.finrank (ZMod 2) (LinearMap.range (A.comp (E s))) = B.rank := by
    rw [hAs, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective (E t) (hE t)
      (LinearMap.range B.mulVecLin)).finrank_eq.symm
  have hrt : Module.finrank (ZMod 2) (LinearMap.range (A.comp (E t))) = B.rank := by
    calc
      _ = B.transpose.rank := by
        rw [hAt, LinearMap.range_comp]
        exact (Submodule.equivMapOfInjective (E s) (hE s)
          (LinearMap.range B.transpose.mulVecLin)).finrank_eq.symm
      _ = B.rank := Matrix.rank_transpose B
  have hrange : LinearMap.range A =
      LinearMap.range (A.comp (E s)) ⊔ LinearMap.range (A.comp (E t)) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x = E s (fun v : s => x (v : V)) +
          E t (fun v : t => x (v : V)) := by
        funext v
        by_cases hv : v ∈ s <;> simp [E, t, hv]
      rw [hx, map_add]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · exact sup_le (LinearMap.range_comp_le_range (E s) A)
        (LinearMap.range_comp_le_range (E t) A)
  have hdisjoint : Disjoint (LinearMap.range (A.comp (E s)))
      (LinearMap.range (A.comp (E t))) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    rw [hAs] at ha
    rw [hAt] at hb
    funext v
    by_cases hv : v ∈ s
    · have h := congrFun ha v
      change (E t (B.mulVecLin a)) v = x v at h
      simpa [E, t, hv] using h.symm
    · have h := congrFun hb v
      change (E s (B.transpose.mulVecLin b)) v = x v at h
      simpa [E, hv] using h.symm
  have hArank : Module.finrank (ZMod 2) (LinearMap.range A) = 2 * B.rank := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (A.comp (E s))) (LinearMap.range (A.comp (E t)))
    rw [← hrange, hdisjoint.eq_bot, finrank_bot, add_zero, hrs, hrt] at hdim
    omega
  have hn : 2 * B.rank + Module.finrank (ZMod 2) K = Fintype.card V := by
    simpa only [hArank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Module.finrank (ZMod 2) K = 2 * k := by
    refine ⟨s.card - B.rank, ?_⟩
    omega
  have hquot : (Module.finrank (ZMod 2) K : ℝ) / 2 = (k : ℝ) := by
    rw [hk]
    push_cast
    ring
  have hfloor : Int.floor ((Module.finrank (ZMod 2) K : ℝ) / 2) = (k : ℤ) := by
    rw [hquot, Int.floor_natCast]
  change (Module.finrank (ZMod 2) K : ℝ) =
    2 * (Int.floor ((Module.finrank (ZMod 2) K : ℝ) / 2) : ℝ)
  rw [hfloor, hk]
  push_cast <;> ring

theorem model_3666c21f3f0671245865 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsTree) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))) := by
  classical
  have ht : G.IsTree := h_guard.1
  have hmR : (G.maxDegree : ℝ) < 3 := by
    linarith only [h_guard.2]
  have hmN : G.maxDegree < 3 := by
    exact_mod_cast hmR
  have hd (v : V) : G.degree v ≤ 2 := by
    have hv := G.degree_le_maxDegree v
    omega
  have haexists : ∃ a : V, G.degree a ≤ 1 := by
    by_cases hV : Nontrivial V
    · letI : Nontrivial V := hV
      obtain ⟨a, ha⟩ := ht.exists_vert_degree_one_of_nontrivial
      exact ⟨a, by omega⟩
    · letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      obtain ⟨a⟩ := ht.connected.nonempty
      refine ⟨a, ?_⟩
      rw [SimpleGraph.degree_eq_zero_of_subsingleton a]
      omega
  obtain ⟨a, ha⟩ := haexists
  let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hsum (x : K) (u : V) :
      (∑ v ∈ G.neighborFinset u, x.val v) = 0 := by
    have hx := congrFun (LinearMap.mem_ker.mp x.property) u
    simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      Pi.zero_apply] using hx
  have hstep (x : K) {u v : V} (huv : G.Adj u v)
      (hu : x.val u = 0) : ∀ w, G.Adj v w → x.val w = 0 := by
    intro w hvw
    by_cases hwu : w = u
    · simpa only [hwu] using hu
    · have hsub : ({u, w} : Finset V) ⊆ G.neighborFinset v := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · simpa only [SimpleGraph.mem_neighborFinset] using huv.symm
        · simpa only [SimpleGraph.mem_neighborFinset] using hvw
      have hc : (G.neighborFinset v).card ≤ ({u, w} : Finset V).card := by
        rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pair (Ne.symm hwu)]
        exact hd v
      have heq : G.neighborFinset v = {u, w} :=
        (Finset.eq_of_subset_of_card_le hsub hc).symm
      simpa only [heq, Finset.sum_pair (Ne.symm hwu), hu, zero_add] using hsum x v
  have hzero (x : K) (ha0 : x.val a = 0) : x = 0 := by
    have hbase : x.val a = 0 ∧ ∀ v, G.Adj a v → x.val v = 0 := by
      refine ⟨ha0, ?_⟩
      intro v hav
      have hsub : ({v} : Finset V) ⊆ G.neighborFinset a := by
        intro z hz
        have hz' : z = v := Finset.mem_singleton.mp hz
        subst z
        simpa only [SimpleGraph.mem_neighborFinset] using hav
      have hc : (G.neighborFinset a).card ≤ ({v} : Finset V).card := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree,
          Finset.card_singleton] using ha
      have heq : G.neighborFinset a = {v} :=
        (Finset.eq_of_subset_of_card_le hsub hc).symm
      simpa only [heq, Finset.sum_singleton] using hsum x a
    have hwalk : ∀ {u v : V}, G.Walk u v →
        (x.val u = 0 ∧ ∀ w, G.Adj u w → x.val w = 0) → x.val v = 0 := by
      intro u v p
      induction p with
      | nil =>
        intro hu
        exact hu.1
      | @cons u v w huv p ih =>
        intro hu
        exact ih ⟨hu.2 v huv, hstep x huv hu.1⟩
    apply Subtype.ext
    funext v
    change x.val v = 0
    obtain ⟨p⟩ := ht.connected a v
    exact hwalk p hbase
  let S : K →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj a).domRestrict K
  have hSi : Function.Injective S := by
    intro x y hxy
    change x.val a = y.val a at hxy
    have hxy0 : (x - y).val a = 0 := by
      change x.val a - y.val a = 0
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (hzero (x - y) hxy0)
  have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
    simpa only [CommSemiring.finrank_self] using
      LinearMap.finrank_le_finrank_of_injective hSi
  let c : G.Coloring (Fin 2) := ht.coloringTwo
  let p : V → Prop := fun v => c v = 0
  let U := {v : V // p v}
  let W := {v : V // ¬ p v}
  let e : U ⊕ W ≃ V := Equiv.sumCompl p
  let B : Matrix U W (ZMod 2) :=
    (G.adjMatrix (ZMod 2)).submatrix Subtype.val Subtype.val
  let H : Matrix (U ⊕ W) (U ⊕ W) (ZMod 2) :=
    Matrix.fromBlocks 0 B B.transpose 0
  have hp1 {v : V} (hv : ¬ p v) : c v = 1 := by
    have hv0 : (c v).val ≠ 0 := by
      intro heq
      apply hv
      change c v = 0
      apply Fin.ext
      exact heq
    apply Fin.ext
    have hvlt := (c v).isLt
    change (c v).val = 1
    omega
  have hH : (G.adjMatrix (ZMod 2)).submatrix e e = H := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · have hij : ¬ G.Adj i.val j.val := by
        intro hij
        apply c.valid hij
        exact i.property.trans j.property.symm
      change G.adjMatrix (ZMod 2) i.val j.val = 0
      simp only [SimpleGraph.adjMatrix_apply, if_neg hij]
    · rfl
    · change G.adjMatrix (ZMod 2) i.val j.val =
        G.adjMatrix (ZMod 2) j.val i.val
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.adj_comm]
    · have hij : ¬ G.Adj i.val j.val := by
        intro hij
        apply c.valid hij
        exact (hp1 i.property).trans (hp1 j.property).symm
      change G.adjMatrix (ZMod 2) i.val j.val = 0
      simp only [SimpleGraph.adjMatrix_apply, if_neg hij]
  have hHr : H.rank = (G.adjMatrix (ZMod 2)).rank := by
    rw [← hH]
    exact Matrix.rank_submatrix _ e e
  let K1 := LinearMap.ker B.transpose.mulVecLin
  let K2 := LinearMap.ker B.mulVecLin
  let KH := LinearMap.ker H.mulVecLin
  let E : (U ⊕ W → ZMod 2) ≃ₗ[ZMod 2]
      ((U → ZMod 2) × (W → ZMod 2)) :=
    LinearEquiv.sumArrowLequivProdArrow U W (ZMod 2) (ZMod 2)
  let P := K1.prod K2
  have hKH : KH = P.comap E.toLinearMap := by
    ext x
    change (Matrix.mulVec H x = 0) ↔
      (Matrix.mulVec B.transpose (x ∘ Sum.inl) = 0 ∧
        Matrix.mulVec B (x ∘ Sum.inr) = 0)
    change (Matrix.mulVec (Matrix.fromBlocks 0 B B.transpose 0) x = 0) ↔
      (Matrix.mulVec B.transpose (x ∘ Sum.inl) = 0 ∧
        Matrix.mulVec B (x ∘ Sum.inr) = 0)
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, zero_add, add_zero]
    constructor
    · intro hx
      constructor
      · funext i
        exact congrFun hx (Sum.inr i)
      · funext i
        exact congrFun hx (Sum.inl i)
    · rintro ⟨h1, h2⟩
      rw [h1, h2]
      funext i
      cases i <;> rfl
  have hKdim : Module.finrank (ZMod 2) KH =
      Module.finrank (ZMod 2) K1 + Module.finrank (ZMod 2) K2 := by
    let f : KH ≃ₗ[ZMod 2] K1 × K2 :=
      (LinearEquiv.ofEq KH (P.comap E.toLinearMap) hKH).trans
        ((E.ofSubmodule' P).trans (Submodule.prodEquiv K1 K2))
    simpa only [Module.finrank_prod] using f.finrank_eq
  have hcard : Fintype.card U + Fintype.card W = Fintype.card V := by
    simpa only [Fintype.card_sum] using Fintype.card_congr e
  have hN : (G.adjMatrix (ZMod 2)).rank + Module.finrank (ZMod 2) K =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      (G.adjMatrix (ZMod 2)).mulVecLin.finrank_range_add_finrank_ker
  have hM : H.rank + Module.finrank (ZMod 2) KH =
      Fintype.card U + Fintype.card W := by
    simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_sum] using
      H.mulVecLin.finrank_range_add_finrank_ker
  rw [hHr, hcard] at hM
  have hB : B.rank + Module.finrank (ZMod 2) K2 = Fintype.card W := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      B.mulVecLin.finrank_range_add_finrank_ker
  have hBt0 : B.transpose.rank + Module.finrank (ZMod 2) K1 =
      Fintype.card U := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      B.transpose.mulVecLin.finrank_range_add_finrank_ker
  have hBt : B.rank + Module.finrank (ZMod 2) K1 = Fintype.card U := by
    simpa only [Matrix.rank_transpose] using hBt0
  have hKeq : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) KH := by
    omega
  have hpar : Fintype.card V = 2 * B.rank + Module.finrank (ZMod 2) K := by
    omega
  have hk : Module.finrank (ZMod 2) K = Fintype.card V % 2 := by
    omega
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
  rw [hrem, hk]

theorem model_498663d70c6a4882faec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((2 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ)))) := by
  classical
  have hconn : G.Connected := h_guard.1
  letI : Nonempty V := hconn.nonempty
  have hlo : (1 : ℝ) < (G.minDegree : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).1
    linarith
  have hhi : (G.minDegree : ℝ) < (3 : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).2
    linarith
  have hlo' : 1 < G.minDegree := by exact_mod_cast hlo
  have hhi' : G.minDegree < 3 := by exact_mod_cast hhi
  have hmin : G.minDegree = 2 := by omega
  obtain ⟨d, hreg⟩ := h_guard.2.1
  have hd : d = 2 := hreg.minDegree_eq.symm.trans hmin
  have hdeg (u : V) : G.degree u = 2 := (hreg.degree_eq u).trans hd
  have hnotacyc : ¬ G.IsAcyclic := by
    intro hac
    have htree : G.IsTree := ⟨hconn, hac⟩
    have hedges := htree.card_edgeFinset
    have hsum : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
      simpa [hdeg, Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges
    omega
  have hexcycle : ∃ a, ∃ p : G.Walk a a, p.IsCycle := by
    by_contra h
    apply hnotacyc
    intro a p hp
    exact h ⟨a, p, hp⟩
  obtain ⟨a, p, hp⟩ := hexcycle
  have hn : 2 < p.length := by
    have h := hp.three_le_length
    omega
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨a, p, hp, rfl⟩
  have hcycledeg : ∀ i : Fin p.length,
      (SimpleGraph.cycleGraph p.length).degree i = 2 := by
    have hn3 : p.length - 3 + 3 = p.length := by omega
    rw [← hn3]
    exact fun i => SimpleGraph.cycleGraph_degree_three_le
  have hns (i : Fin p.length) : Function.Surjective (f.mapNeighborSet i) := by
    have hbij : Function.Bijective (f.mapNeighborSet i) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(f.mapNeighborSet i).injective, by
          simp only [SimpleGraph.card_neighborSet_eq_degree, hcycledeg, hdeg]⟩
    exact hbij.2
  have hclosed {i : Fin p.length} {w : V} (hw : G.Adj (f i) w) :
      ∃ j : Fin p.length, f j = w := by
    obtain ⟨j, hj⟩ := hns i ⟨w, hw⟩
    exact ⟨j.1, congrArg Subtype.val hj⟩
  have hreach {u w : V} (q : G.Walk u w) :
      (∃ i : Fin p.length, f i = u) → (∃ i : Fin p.length, f i = w) := by
    induction q with
    | nil => exact fun h => h
    | @cons u t w hut q ih =>
      rintro ⟨i, rfl⟩
      exact ih (hclosed hut)
  let i0 : Fin p.length := ⟨0, by omega⟩
  have hfs : Function.Surjective f := by
    intro w
    exact hreach (hconn (f i0) w).some ⟨i0, rfl⟩
  let e : SimpleGraph.cycleGraph p.length ≃g G :=
    { toEquiv := Equiv.ofBijective f ⟨f.injective, hfs⟩
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph p.length).Adj i j
        constructor
        · intro hij
          obtain ⟨k, hk⟩ := hns i ⟨f j, hij⟩
          have hval : f k.1 = f j := congrArg Subtype.val hk
          have hkval : k.1 = j := f.injective hval
          simpa only [SimpleGraph.mem_neighborSet, hkval] using k.property
        · intro hij
          exact f.toHom.map_adj hij }
  have hcard : p.length = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker A
  have hpairs (u : V) : ∃ v w, v ≠ w ∧ G.neighborFinset u = {v, w} := by
    apply Finset.card_eq_two.mp
    exact hdeg u
  have htwo (t : ZMod 2) : t + t = 0 := by
    simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel t
  have hrows (x : K) (u : V) : (∑ w ∈ G.neighborFinset u, x.1 w) = 0 := by
    have hx : A x.1 = 0 := LinearMap.mem_ker.mp x.property
    have h := congrFun hx u
    simpa only [A, Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      Pi.zero_apply] using h
  have hneighbors (x : K) {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) :
      x.1 v = x.1 w := by
    obtain ⟨s, t, hst, hs⟩ := hpairs u
    have hsum : x.1 s + x.1 t = 0 := by
      simpa [hs, hst] using hrows x u
    have heq : x.1 s = x.1 t := by
      have h : x.1 s = -x.1 t := eq_neg_of_add_eq_zero_left hsum
      simpa only [ZMod.neg_eq_self_mod_two] using h
    have hv : v = s ∨ v = t := by
      simpa [hs] using ((G.mem_neighborFinset u v).mpr huv)
    have hw : w = s ∨ w = t := by
      simpa [hs] using ((G.mem_neighborFinset u w).mpr huw)
    rcases hv with rfl | rfl
    · rcases hw with rfl | rfl
      · rfl
      · exact heq
    · rcases hw with rfl | rfl
      · exact heq.symm
      · rfl
  have hprop (x : K) {u w : V} (q : G.Walk u w) :
      ∀ z, G.Adj z u → x.1 z = 0 → x.1 u = 0 → x.1 w = 0 := by
    induction q with
    | nil =>
      intro z hz hz0 hu0
      exact hu0
    | @cons u t w hut q ih =>
      intro z hzu hz0 hu0
      exact ih u hut hu0 ((hneighbors x hzu.symm hut).symm.trans hz0)
  have hzero (x : K) {u v : V} (huv : G.Adj u v)
      (hu : x.1 u = 0) (hv : x.1 v = 0) : x = 0 := by
    apply Subtype.ext
    funext w
    exact hprop x (hconn v w).some u huv hu hv
  obtain ⟨b, b', hbb', hnb⟩ := hpairs a
  have hab : G.Adj a b := by
    apply (G.mem_neighborFinset a b).mp
    simp [hnb]
  let C0 : (ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := LinearMap.const
  have hC0 (t : ZMod 2) : C0 t ∈ K := by
    rw [LinearMap.mem_ker]
    funext u
    change Matrix.mulVec (G.adjMatrix (ZMod 2)) (C0 t) u = 0
    obtain ⟨v, w, hvw, hs⟩ := hpairs u
    rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
    change t + t = 0
    exact htwo t
  let C : (ZMod 2) →ₗ[ZMod 2] K := C0.codRestrict K hC0
  have hCi : Function.Injective C := by
    intro x y hxy
    have h := congrArg (fun z : K => z.1 a) hxy
    change x = y at h
    exact h
  have hge1 : 1 ≤ Module.finrank (ZMod 2) K := by
    simpa only [CommSemiring.finrank_self] using
      LinearMap.finrank_le_finrank_of_injective hCi
  let T : K →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi fun i =>
      if i = 0 then (LinearMap.proj a).domRestrict K
      else (LinearMap.proj b).domRestrict K
  have hTi : Function.Injective T := by
    intro x y hxy
    have h0 : x.1 a = y.1 a := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (0 : Fin 2)
    have h1 : x.1 b = y.1 b := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (1 : Fin 2)
    apply sub_eq_zero.mp
    apply hzero (x - y) hab
    · change x.1 a - y.1 a = 0
      exact sub_eq_zero.mpr h0
    · change x.1 b - y.1 b = 0
      exact sub_eq_zero.mpr h1
  have hle2 : Module.finrank (ZMod 2) K ≤ 2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_injective hTi
  change (Module.finrank (ZMod 2) K : ℝ) = _
  rw [← hcard]
  by_cases hEven : Even p.length
  · have hcolor : G.Colorable 2 :=
      (SimpleGraph.IsBipartite.cycleGraph_of_even hEven).of_hom e.symm.toHom
    obtain ⟨c⟩ := hcolor
    have hcsurj : Function.Surjective c := by
      intro i
      have hne : (c a).val ≠ (c b).val := by
        intro h
        exact c.valid hab (Fin.ext h)
      have ha2 := (c a).isLt
      have hb2 := (c b).isLt
      have hi2 := i.isLt
      have hi : i = c a ∨ i = c b := by
        by_cases hia : i = c a
        · exact Or.inl hia
        · right
          apply Fin.ext
          have hia' : i.val ≠ (c a).val := by
            intro h
            exact hia (Fin.ext h)
          omega
      rcases hi with hi | hi
      · exact ⟨a, hi.symm⟩
      · exact ⟨b, hi.symm⟩
    have hcolors {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : c v = c w := by
      apply Fin.ext
      have hv : (c u).val ≠ (c v).val := by
        intro h
        exact c.valid huv (Fin.ext h)
      have hw : (c u).val ≠ (c w).val := by
        intro h
        exact c.valid huw (Fin.ext h)
      have hu2 := (c u).isLt
      have hv2 := (c v).isLt
      have hw2 := (c w).isLt
      omega
    let D0 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
      LinearMap.pi fun u => LinearMap.proj (c u)
    have hD0 (t : Fin 2 → ZMod 2) : D0 t ∈ K := by
      rw [LinearMap.mem_ker]
      funext u
      change Matrix.mulVec (G.adjMatrix (ZMod 2)) (D0 t) u = 0
      obtain ⟨v, w, hvw, hs⟩ := hpairs u
      have huv : G.Adj u v := by
        apply (G.mem_neighborFinset u v).mp
        simp [hs]
      have huw : G.Adj u w := by
        apply (G.mem_neighborFinset u w).mp
        simp [hs]
      have heq := hcolors huv huw
      rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
      change t (c v) + t (c w) = 0
      rw [heq]
      exact htwo _
    let D : (Fin 2 → ZMod 2) →ₗ[ZMod 2] K := D0.codRestrict K hD0
    have hDi : Function.Injective D := by
      intro x y hxy
      funext i
      obtain ⟨u, hu⟩ := hcsurj i
      have h := congrArg (fun z : K => z.1 u) hxy
      change x (c u) = y (c u) at h
      simpa only [hu] using h
    have hge2 : 2 ≤ Module.finrank (ZMod 2) K := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        LinearMap.finrank_le_finrank_of_injective hDi
    have hdim : Module.finrank (ZMod 2) K = 2 := le_antisymm hle2 hge2
    obtain ⟨k, hk⟩ := hEven
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      rw [hquot, Int.floor_natCast]
    rw [hdim, hfloor, hk]
    push_cast <;> ring
  · have hOdd : Odd p.length := Nat.not_even_iff_odd.mp hEven
    have hnotcolor : ¬ G.Colorable 2 := by
      intro hc
      have hc' := hc.of_hom f.toHom
      have hchrom := SimpleGraph.chromaticNumber_cycleGraph_of_odd p.length
        (by omega) hOdd
      have hle := hc'.chromaticNumber_le
      rw [hchrom] at hle
      norm_num at hle
    have hsame (x : K) : x.1 a = x.1 b := by
      by_contra hx
      let c : G.Coloring (ZMod 2) :=
        SimpleGraph.Coloring.mk x.1 (by
          intro u w huw heq
          have hxconst : x = C (x.1 u) := by
            apply sub_eq_zero.mp
            apply hzero (x - C (x.1 u)) huw
            · change x.1 u - x.1 u = 0
              exact sub_self _
            · change x.1 w - x.1 u = 0
              exact sub_eq_zero.mpr heq.symm
          apply hx
          rw [hxconst]
          rfl)
      exact hnotcolor (by simpa only [ZMod.card] using c.colorable)
    let S : K →ₗ[ZMod 2] (ZMod 2) := (LinearMap.proj a).domRestrict K
    have hSi : Function.Injective S := by
      intro x y hxy
      have h : x.1 a = y.1 a := by
        simpa [S, LinearMap.proj_apply] using hxy
      have hz : (x - y).1 a = 0 := by
        change x.1 a - y.1 a = 0
        exact sub_eq_zero.mpr h
      apply sub_eq_zero.mp
      exact hzero (x - y) hab hz ((hsame (x - y)).symm.trans hz)
    have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
      simpa only [CommSemiring.finrank_self] using
        LinearMap.finrank_le_finrank_of_injective hSi
    have hdim : Module.finrank (ZMod 2) K = 1 := le_antisymm hle1 hge1
    obtain ⟨k, hk⟩ := hOdd
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) + (1 / 2 : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      rw [hquot]
      constructor <;> push_cast <;> linarith
    rw [hdim, hfloor, hk]
    push_cast <;> ring
theorem hull3d_parity_code_dimension_ge__1_0_min_degree_parity_code_distance_1_is_connected_d17614a8e073 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((-1 : ℝ) * (G.minDegree : ℝ)) + (1 : ℝ)) := by
  classical
  letI : Nonempty V := h_guard.nonempty
  have hnonneg : (0 : ℝ) ≤
      (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) :=
    Nat.cast_nonneg _
  by_cases hd : G.minDegree = 0
  · obtain ⟨a, ha⟩ := SimpleGraph.minDegree_eq_zero_iff.mp hd
    let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    have hmem : Pi.single a (1 : ZMod 2) ∈ K := by
      rw [LinearMap.mem_ker]
      funext v
      change Matrix.mulVec (G.adjMatrix (ZMod 2)) (Pi.single a 1) v = 0
      rw [Matrix.mulVec_single_one]
      change G.adjMatrix (ZMod 2) v a = 0
      have hnot : ¬ G.Adj v a := fun h => ha v h.symm
      simp only [SimpleGraph.adjMatrix_apply, if_neg hnot]
    let x : K := ⟨Pi.single a (1 : ZMod 2), hmem⟩
    have hx : x ≠ 0 := by
      intro h
      have hh := congrArg (fun y : K => y.val a) h
      have h10 : (1 : ZMod 2) = 0 := by
        simpa [x] using hh
      exact one_ne_zero h10
    have hk : 1 ≤ Module.finrank (ZMod 2) K := by
      have hp : 0 < Module.finrank (ZMod 2) K :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
      omega
    have hkR : (1 : ℝ) ≤ (Module.finrank (ZMod 2) K : ℝ) := by
      exact_mod_cast hk
    simpa only [hd, Nat.cast_zero, mul_zero, zero_add] using hkR
  · have hdN : 1 ≤ G.minDegree := Nat.one_le_iff_ne_zero.mpr hd
    have hdR : (1 : ℝ) ≤ (G.minDegree : ℝ) := by
      exact_mod_cast hdN
    linarith only [hdR, hnonneg]
