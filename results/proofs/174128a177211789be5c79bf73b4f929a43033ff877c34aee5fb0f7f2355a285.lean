import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  change (weights.min' hw : ℝ) ≤ (Fintype.card V : ℝ) + 1
  have h : weights.min' hw ≤ Fintype.card V + 1 :=
    Finset.min'_le _ _ (by simp [weights])
  exact_mod_cast h

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
theorem model_02ea1aa899a63c06ad70 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)))) ≤ ((Fintype.card V : ℝ) + (2 : ℝ)) := by
  classical
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d := weights.min' hw
  change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) + 2 * (d : ℝ) ≤ (Fintype.card V : ℝ) + 2
  by_cases hd : d = 0
  · have hn := parity_code_dimension_le_order G
    change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) ≤ (Fintype.card V : ℝ) at hn
    simp only [hd, Nat.cast_zero, mul_zero, add_zero]
    linarith
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hmin (x : V → ZMod 2) (hx : x ≠ 0) (hAx : A x = 0) :
      d ≤ hammingNorm x := by
    change weights.min' hw ≤ hammingNorm x
    apply Finset.min'_le _ _
    change hammingNorm x ∈ ({Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun y => y ≠ 0 ∧ A y = 0)).image hammingNorm)
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hAx⟩, rfl⟩))
  have hsmall (x : V → ZMod 2) (hx : A x = 0)
      (hn : hammingNorm x < d) : x = 0 := by
    by_contra hne
    exact (Nat.not_le_of_lt hn) (hmin x hne hx)
  have hweight (u : Finset V) (x : V → ZMod 2)
      (hx : ∀ v, v ∉ u → x v = 0) : hammingNorm x ≤ u.card := by
    change ((Finset.univ : Finset V).filter (fun v => x v ≠ 0)).card ≤ u.card
    apply Finset.card_le_card
    intro v hv
    by_contra h
    exact (Finset.mem_filter.mp hv).2 (hx v h)
  have hkpos : 0 < Module.finrank (ZMod 2) (LinearMap.ker A) := by
    by_contra h
    have hk0 : Module.finrank (ZMod 2) (LinearMap.ker A) = 0 := by omega
    have hg := h_guard.2
    change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) ≥ (9999999 / 10000000 : ℝ) at hg
    rw [hk0] at hg
    norm_num at hg
  obtain ⟨x0, hx0ker, hx0⟩ : ∃ x : V → ZMod 2, A x = 0 ∧ x ≠ 0 := by
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkpos
    refine ⟨(x : V → ZMod 2), LinearMap.mem_ker.mp x.property, ?_⟩
    intro heq
    apply hx
    apply Subtype.ext
    exact heq
  let cut (u : Finset V) (x : V → ZMod 2) : V → ZMod 2 :=
    fun v => if v ∈ u then x v else 0
  have hcutadd (u : Finset V) (x : V → ZMod 2) :
      cut u x + cut uᶜ x = x := by
    funext v
    by_cases hv : v ∈ u <;> simp [cut, hv]
  have hmask (u : Finset V)
      (hu : ∀ v ∈ u, ∀ w ∈ u, ¬ G.Adj v w)
      (huc : ∀ v ∈ uᶜ, ∀ w ∈ uᶜ, ¬ G.Adj v w)
      (x : V → ZMod 2) (hx : A x = 0) : A (cut u x) = 0 := by
    funext v
    change (∑ w : V, G.adjMatrix (ZMod 2) v w * cut u x w) = 0
    by_cases hv : v ∈ u
    · apply Finset.sum_eq_zero
      intro w hw
      by_cases hwu : w ∈ u
      · simp [SimpleGraph.adjMatrix_apply, hu v hv w hwu]
      · simp [cut, hwu]
    · calc
        (∑ w : V, G.adjMatrix (ZMod 2) v w * cut u x w) =
            ∑ w : V, G.adjMatrix (ZMod 2) v w * x w := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hwu : w ∈ u
          · simp [cut, hwu]
          · have hnot : ¬ G.Adj v w :=
              huc v (Finset.mem_compl.mpr hv) w (Finset.mem_compl.mpr hwu)
            simp [SimpleGraph.adjMatrix_apply, hnot]
        _ = 0 := congrFun hx v
  have hsize (u : Finset V)
      (hu : ∀ v ∈ u, ∀ w ∈ u, ¬ G.Adj v w)
      (huc : ∀ v ∈ uᶜ, ∀ w ∈ uᶜ, ¬ G.Adj v w) : d - 1 ≤ u.card := by
    by_contra hh
    have huSmall : u.card < d := by omega
    have hpu : hammingNorm (cut u x0) ≤ u.card :=
      hweight u (cut u x0) (by
        intro v hv
        simp [cut, hv])
    have hp : cut u x0 = 0 :=
      hsmall (cut u x0) (hmask u hu huc x0 hx0ker) (by omega)
    have hq : cut uᶜ x0 ≠ 0 := by
      intro hq0
      have h := hcutadd u x0
      rw [hp, hq0, zero_add] at h
      exact hx0 h.symm
    have hqker : A (cut uᶜ x0) = 0 :=
      hmask uᶜ huc (by simpa only [compl_compl] using hu) x0 hx0ker
    have hdc : d ≤ uᶜ.card :=
      le_trans (hmin (cut uᶜ x0) hq hqker)
        (hweight uᶜ (cut uᶜ x0) (by
          intro v hv
          simp [cut, hv]))
    obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq
      (show d - 1 ≤ uᶜ.card by omega)
    let E : (t → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
      { toFun := fun x v => if hv : v ∈ t then x ⟨v, hv⟩ else 0
        map_add' := by
          intro x y
          funext v
          by_cases hv : v ∈ t <;> simp [hv]
        map_smul' := by
          intro c x
          funext v
          by_cases hv : v ∈ t <;> simp [hv] }
    have hE : Function.Injective E := by
      intro x y hxy
      funext v
      have h := congrFun hxy (v : V)
      simpa [E, v.property] using h
    let f : (t → ZMod 2) →ₗ[ZMod 2] (u → ZMod 2) :=
      { toFun := fun x v => A (E x) (v : V)
        map_add' := by
          intro x y
          funext v
          simp only [map_add, Pi.add_apply]
        map_smul' := by
          intro c x
          funext v
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
    have hf : Function.Injective f := by
      intro x y hxy
      apply hE
      apply sub_eq_zero.mp
      apply hsmall (E x - E y)
      · funext v
        change A (E x - E y) v = 0
        by_cases hv : v ∈ u
        · have h := congrFun hxy (⟨v, hv⟩ : u)
          change A (E x) v = A (E y) v at h
          simp only [map_sub, Pi.sub_apply]
          exact sub_eq_zero.mpr h
        · change (∑ w : V, G.adjMatrix (ZMod 2) v w * (E x - E y) w) = 0
          apply Finset.sum_eq_zero
          intro w hw
          by_cases hwt : w ∈ t
          · have hnot : ¬ G.Adj v w :=
              huc v (Finset.mem_compl.mpr hv) w (ht hwt)
            simp [SimpleGraph.adjMatrix_apply, hnot]
          · simp [E, hwt]
      · have hn : hammingNorm (E x - E y) ≤ t.card :=
          hweight t (E x - E y) (by
            intro v hv
            simp [E, hv])
        omega
    have hdim : t.card ≤ u.card := by
      have h := LinearMap.finrank_le_finrank_of_injective hf
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h
    omega
  obtain ⟨C⟩ := h_guard.1
  let s : Finset V := Finset.univ.filter (fun v => C v = 0)
  have hs (v : V) : v ∈ s ↔ C v = 0 := by simp [s]
  have hi : ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w := by
    intro v hv w hw hadj
    apply C.valid hadj
    exact ((hs v).mp hv).trans (((hs w).mp hw).symm)
  have hcolor (v : V) (hv : v ∈ sᶜ) : C v = 1 := by
    apply Fin.eq_one_of_ne_zero
    intro heq
    exact (Finset.mem_compl.mp hv) ((hs v).mpr heq)
  have hci : ∀ v ∈ sᶜ, ∀ w ∈ sᶜ, ¬ G.Adj v w := by
    intro v hv w hw hadj
    apply C.valid hadj
    exact (hcolor v hv).trans ((hcolor w hw).symm)
  have hsz : d - 1 ≤ s.card := hsize s hi hci
  have hscz : d - 1 ≤ sᶜ.card :=
    hsize sᶜ hci (by simpa only [compl_compl] using hi)
  obtain ⟨a, has, hacard⟩ := Finset.exists_subset_card_eq hsz
  obtain ⟨b, hbs, hbcard⟩ := Finset.exists_subset_card_eq hscz
  have hab : Disjoint a b := by
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    exact (Finset.mem_compl.mp (hbs hvb)) (has hva)
  let f : LinearMap.ker A →ₗ[ZMod 2] (↥((a ∪ b)ᶜ) → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) (v : V)
      map_add' := by
        intro x y
        funext v
        rfl
      map_smul' := by
        intro c x
        funext v
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    let z : V → ZMod 2 := (x : V → ZMod 2) - (y : V → ZMod 2)
    have hzA : A z = 0 := by
      dsimp only [z]
      rw [map_sub, LinearMap.mem_ker.mp x.property,
        LinearMap.mem_ker.mp y.property, sub_self]
    have hzout (v : V) (hv : v ∉ a ∪ b) : z v = 0 := by
      have h := congrFun hxy (⟨v, Finset.mem_compl.mpr hv⟩ : ↥((a ∪ b)ᶜ))
      change (x : V → ZMod 2) v = (y : V → ZMod 2) v at h
      change (x : V → ZMod 2) v - (y : V → ZMod 2) v = 0
      exact sub_eq_zero.mpr h
    have hp : cut s z = 0 := by
      apply hsmall _ (hmask s hi hci z hzA)
      have hn : hammingNorm (cut s z) ≤ a.card := by
        apply hweight a
        intro v hva
        by_cases hvs : v ∈ s
        · have hvb : v ∉ b := by
            intro hvb
            exact (Finset.mem_compl.mp (hbs hvb)) hvs
          have hvout : v ∉ a ∪ b :=
            fun h => (Finset.mem_union.mp h).elim hva hvb
          simp [cut, hvs, hzout v hvout]
        · simp [cut, hvs]
      omega
    have hq : cut sᶜ z = 0 := by
      apply hsmall _ (hmask sᶜ hci (by simpa only [compl_compl] using hi) z hzA)
      have hn : hammingNorm (cut sᶜ z) ≤ b.card := by
        apply hweight b
        intro v hvb
        by_cases hvs : v ∈ sᶜ
        · have hva : v ∉ a := by
            intro hva
            exact (Finset.mem_compl.mp hvs) (has hva)
          have hvout : v ∉ a ∪ b :=
            fun h => (Finset.mem_union.mp h).elim hva hvb
          simp [cut, hvs, hzout v hvout]
        · simp [cut, hvs]
      omega
    apply Subtype.ext
    apply sub_eq_zero.mp
    change z = 0
    have h := hcutadd s z
    rw [hp, hq, zero_add] at h
    exact h.symm
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker A) ≤ (a ∪ b)ᶜ.card := by
    have h := LinearMap.finrank_le_finrank_of_injective hf
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h
  have hcard : (a ∪ b).card + (a ∪ b)ᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl (a ∪ b)
  have hunion : (a ∪ b).card = a.card + b.card :=
    Finset.card_union_of_disjoint hab
  have hnat : Module.finrank (ZMod 2) (LinearMap.ker A) + 2 * d ≤ Fintype.card V + 2 := by
    omega
  exact_mod_cast hnat
