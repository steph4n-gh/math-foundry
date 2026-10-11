import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
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

theorem model_50989e8eb15a8fad02e7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) + ((Int.ceil ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) / (2 : ℝ))) : ℝ)) ≤ ((Fintype.card V : ℝ) + (2 : ℝ)) := by
  classical
  let C : Submodule (ZMod 2) (V → ZMod 2) :=
    LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  let k : ℕ := Module.finrank (ZMod 2) C
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (k : ℝ) + (d : ℝ) + (Int.ceil ((d : ℝ) / 2) : ℝ) ≤
    (Fintype.card V : ℝ) + 2
  have hkR : (19999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k ≤ 1 := by omega
    have hcast : (k : ℝ) ≤ 1 := by exact_mod_cast hk1
    linarith only [hkR, hcast]
  have hk_le : k ≤ Fintype.card V := by
    calc
      k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hsle : k - 2 ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using (Nat.sub_le k 2).trans hk_le
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hsle
  let f : C →ₗ[ZMod 2] (s → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) (v : V)
      map_add' := by
        intro x y
        funext v
        rfl
      map_smul' := by
        intro c x
        funext v
        rfl }
  have hrange : Module.finrank (ZMod 2) (LinearMap.range f) ≤ s.card := by
    calc
      _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
      _ = s.card := by
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) +
      Module.finrank (ZMod 2) (LinearMap.ker f) = k :=
    LinearMap.finrank_range_add_finrank_ker f
  have htwo : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) := by omega
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := LinearMap.ker f) htwo
  let x : V → ZMod 2 := ((b (0 : Fin 2) : C) : V → ZMod 2)
  let y : V → ZMod 2 := ((b (1 : Fin 2) : C) : V → ZMod 2)
  have hx : x ≠ 0 := by
    intro h
    have h' : b (0 : Fin 2) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    exact (LinearIndependent.ne_zero (0 : Fin 2) hb) h'
  have hy : y ≠ 0 := by
    intro h
    have h' : b (1 : Fin 2) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    exact (LinearIndependent.ne_zero (1 : Fin 2) hb) h'
  have hxy : x ≠ y := by
    intro h
    have h' : b (0 : Fin 2) = b (1 : Fin 2) := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    exact (by decide : (0 : Fin 2) ≠ 1) (hb.injective h')
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hxC : x ∈ C := (b (0 : Fin 2) : C).property
  have hyC : y ∈ C := (b (1 : Fin 2) : C).property
  have hzC : x - y ∈ C := C.sub_mem hxC hyC
  have hd_le (u : V → ZMod 2) (hu : u ≠ 0) (huC : u ∈ C) :
      d ≤ hammingNorm u := by
    change weights.min' hw ≤ hammingNorm u
    apply Finset.min'_le
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hu, LinearMap.mem_ker.mp huC⟩
  have hdx : d ≤ hammingNorm x := hd_le x hx hxC
  have hdy : d ≤ hammingNorm y := hd_le y hy hyC
  have hdz : d ≤ hammingNorm (x - y) := hd_le (x - y) hz hzC
  have hxzero (v : V) (hv : v ∈ s) : x v = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp (b (0 : Fin 2)).property)
      (⟨v, hv⟩ : s)
    exact h
  have hyzero (v : V) (hv : v ∈ s) : y v = 0 := by
    have h := congrFun (LinearMap.mem_ker.mp (b (1 : Fin 2)).property)
      (⟨v, hv⟩ : s)
    exact h
  have hzzero (v : V) (hv : v ∈ s) : (x - y) v = 0 := by
    simp only [Pi.sub_apply, hxzero v hv, hyzero v hv, sub_self]
  have hsum (u : V → ZMod 2) (hu : ∀ v, v ∈ s → u v = 0) :
      hammingNorm u = ∑ v ∈ sᶜ, if u v ≠ 0 then (1 : ℕ) else 0 := by
    rw [Finset.sum_boole]
    change (Finset.univ.filter (fun v => u v ≠ 0)).card =
      (sᶜ.filter (fun v => u v ≠ 0)).card
    apply congrArg Finset.card
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · intro h
      exact ⟨fun hv => h (hu v hv), h⟩
    · intro h
      exact h.2
  have hbinary (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
    apply (ZMod.val_eq_one (by decide : (1 : ℕ) < 2) a).mp
    have hpos : 0 < a.val := ZMod.val_pos.mpr ha
    have hlt : a.val < 2 := ZMod.val_lt a
    omega
  have hthree : hammingNorm x + hammingNorm y + hammingNorm (x - y) ≤
      2 * sᶜ.card := by
    rw [hsum x hxzero, hsum y hyzero, hsum (x - y) hzzero]
    calc
      _ = ∑ v ∈ sᶜ,
          ((if x v ≠ 0 then (1 : ℕ) else 0) +
            (if y v ≠ 0 then (1 : ℕ) else 0) +
            (if (x - y) v ≠ 0 then (1 : ℕ) else 0)) := by
        simp only [Finset.sum_add_distrib]
      _ ≤ ∑ v ∈ sᶜ, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases ha : x v = 0
        · by_cases hb0 : y v = 0
          · simp [Pi.sub_apply, ha, hb0]
          · simp [Pi.sub_apply, ha, hb0]
        · by_cases hb0 : y v = 0
          · simp [Pi.sub_apply, ha, hb0]
          · have hab : x v = y v := (hbinary _ ha).trans (hbinary _ hb0).symm
            simp [Pi.sub_apply, hab, hb0]
      _ = 2 * sᶜ.card := by simp [mul_comm]
  have hbound : 3 * d ≤ 2 * sᶜ.card := by omega
  have hcards : s.card + sᶜ.card = Fintype.card V := Finset.card_add_card_compl s
  have hsize : k + sᶜ.card = Fintype.card V + 2 := by omega
  have hboundR : (3 : ℝ) * (d : ℝ) ≤ (2 : ℝ) * (sᶜ.card : ℝ) := by
    exact_mod_cast hbound
  have hsizeR : (k : ℝ) + (sᶜ.card : ℝ) = (Fintype.card V : ℝ) + 2 := by
    exact_mod_cast hsize
  have hceil : Int.ceil ((d : ℝ) / 2) ≤ (sᶜ.card : ℤ) - (d : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    linarith only [hboundR]
  have hceilR : (Int.ceil ((d : ℝ) / 2) : ℝ) ≤ (sᶜ.card : ℝ) - (d : ℝ) := by
    exact_mod_cast hceil
  linarith only [hsizeR, hceilR]

theorem model_4c93851913291e3da7ff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) + ((Int.ceil ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) / ((G.maxDegree : ℝ) - (1 : ℝ)))) : ℝ)) ≤ ((Fintype.card V : ℝ) + (2 : ℝ)) := by
  classical
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let r : ℕ := G.maxDegree - 1
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (k : ℝ) + (d : ℝ) +
    (Int.ceil ((k : ℝ) / ((G.maxDegree : ℝ) - 1)) : ℝ) ≤ (n : ℝ) + 2
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hg : (9999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2
    rw [hk0] at hg
    norm_num at hg
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := by omega
    have hg := h_guard.1
    rw [hz] at hg
    norm_num at hg
  have hmax : 2 ≤ G.maxDegree := by
    by_contra h
    have hle : (G.maxDegree : ℝ) ≤ 1 := by
      exact_mod_cast (show G.maxDegree ≤ 1 by omega)
    linarith only [h_guard.2.1, hle]
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hrmax : G.maxDegree = r + 1 := by
    dsimp [r]
    omega
  have hd_le (x : V → ZMod 2) (hx : x ≠ 0) (hCx : x ∈ C) :
      d ≤ hammingNorm x := by
    change weights.min' hw ≤ hammingNorm x
    apply Finset.min'_le
    change hammingNorm x ∈ ({n + 1} ∪
      ((Finset.univ : Finset (V → ZMod 2)).filter
        (fun y => y ≠ 0 ∧ A y = 0)).image hammingNorm)
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x, ?_, rfl⟩))
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hx, LinearMap.mem_ker.mp hCx⟩
  have hweight (s : Finset V) (x : V → ZMod 2)
      (hx : ∀ v, v ∉ s → x v = 0) : hammingNorm x ≤ s.card := by
    change ((Finset.univ : Finset V).filter (fun v => x v ≠ 0)).card ≤ s.card
    apply Finset.card_le_card
    intro v hv
    by_contra h
    exact (Finset.mem_filter.mp hv).2 (hx v h)
  let proj (D : Submodule (ZMod 2) (V → ZMod 2)) (s : Finset V) :
      D →ₗ[ZMod 2] (s → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) (v : V)
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro c x
        rfl }
  have hproj (D : Submodule (ZMod 2) (V → ZMod 2)) (s : Finset V) :
      Module.finrank (ZMod 2) (LinearMap.range (proj D s)) ≤ s.card := by
    calc
      _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
      _ = s.card := by
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hsing (s : Finset V) (D : Submodule (ZMod 2) (V → ZMod 2))
      (hDC : D ≤ C)
      (hDs : ∀ x : D, ∀ v, v ∉ s → (x : V → ZMod 2) v = 0)
      (hDpos : 0 < Module.finrank (ZMod 2) D) :
      Module.finrank (ZMod 2) D + d ≤ s.card + 1 := by
    have hqle : Module.finrank (ZMod 2) D ≤ s.card := by
      have hf : Function.Injective (proj D s) := by
        intro x y hxy
        apply Subtype.ext
        funext v
        by_cases hv : v ∈ s
        · have h := congrFun hxy (⟨v, hv⟩ : s)
          change (x : V → ZMod 2) v = (y : V → ZMod 2) v at h
          exact h
        · rw [hDs x v hv, hDs y v hv]
      have h := LinearMap.finrank_le_finrank_of_injective hf
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h
    obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq
      ((Nat.sub_le (Module.finrank (ZMod 2) D) 1).trans hqle)
    let p := proj D t
    have hp_le : Module.finrank (ZMod 2) (LinearMap.range p) ≤ t.card :=
      hproj D t
    have hp_dim : Module.finrank (ZMod 2) (LinearMap.range p) +
        Module.finrank (ZMod 2) (LinearMap.ker p) = Module.finrank (ZMod 2) D :=
      LinearMap.finrank_range_add_finrank_ker p
    have hp_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker p) := by omega
    obtain ⟨w, hwne⟩ :=
      (Module.finrank_pos_iff_exists_ne_zero
        (R := ZMod 2) (M := LinearMap.ker p)).mp hp_pos
    have hwval : ((w : D) : V → ZMod 2) ≠ 0 := by
      intro heq
      apply hwne
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    have hwzero (v : V) (hv : v ∈ t) : ((w : D) : V → ZMod 2) v = 0 := by
      have h := congrFun (LinearMap.mem_ker.mp w.property) (⟨v, hv⟩ : t)
      exact h
    have hwsupport : ∀ v, v ∉ s \ t → ((w : D) : V → ZMod 2) v = 0 := by
      intro v hv
      by_cases hvs : v ∈ s
      · have hvt : v ∈ t := by
          by_contra hvt
          exact hv (Finset.mem_sdiff.mpr ⟨hvs, hvt⟩)
        exact hwzero v hvt
      · exact hDs (w : D) v hvs
    have hdw : d ≤ (s \ t).card :=
      le_trans (hd_le _ hwval (hDC (w : D).property))
        (hweight (s \ t) ((w : D) : V → ZMod 2) hwsupport)
    have hcards : (s \ t).card + t.card = s.card :=
      Finset.card_sdiff_add_card_eq_card ht
    omega
  have hbound : ∀ m : ℕ, ∀ (s : Finset V)
      (D : Submodule (ZMod 2) (V → ZMod 2)),
      s.card = m → D ≤ C →
      (∀ x : D, ∀ v, v ∉ s → (x : V → ZMod 2) v = 0) →
      0 < Module.finrank (ZMod 2) D →
      Module.finrank (ZMod 2) D + r * (Module.finrank (ZMod 2) D + d) ≤
        r * (s.card + 2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro s D hsm hDC hDs hDpos
      let q : ℕ := Module.finrank (ZMod 2) D
      change q + r * (q + d) ≤ r * (s.card + 2)
      by_cases hqr : q ≤ r
      · have hsbound := hsing s D hDC hDs hDpos
        change q + d ≤ s.card + 1 at hsbound
        calc
          q + r * (q + d) ≤ r + r * (s.card + 1) :=
            Nat.add_le_add hqr (Nat.mul_le_mul_left r hsbound)
          _ = r * (s.card + 2) := by ring
      · have hrq : r < q := Nat.lt_of_not_ge hqr
        obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hDpos
        have hxval : (x : V → ZMod 2) ≠ 0 := by
          intro heq
          apply hx
          exact Subtype.ext heq
        obtain ⟨v, hv⟩ : ∃ v : V, (x : V → ZMod 2) v ≠ 0 := by
          by_contra h
          apply hxval
          funext v
          by_contra hv
          exact h ⟨v, hv⟩
        have hvs : v ∈ s := by
          by_contra hvs
          exact hv (hDs x v hvs)
        obtain ⟨u, hvu⟩ := (G.degree_pos_iff_exists_adj v).mp
          (lt_of_lt_of_le hdeg (G.minDegree_le_degree v))
        let t : Finset V := G.neighborFinset u ∩ s
        have hvt : v ∈ t := Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset u v).mpr (G.adj_symm hvu), hvs⟩
        have ht : t ⊆ s := Finset.inter_subset_right
        have htpos : 0 < t.card := Finset.card_pos.mpr ⟨v, hvt⟩
        have htmax : t.card ≤ r + 1 := by
          rw [← hrmax]
          calc
            t.card ≤ (G.neighborFinset u).card :=
              Finset.card_le_card Finset.inter_subset_left
            _ = G.degree u := rfl
            _ ≤ G.maxDegree := G.degree_le_maxDegree u
        have hsum (y : D) : (∑ w ∈ t, (y : V → ZMod 2) w) = 0 := by
          calc
            _ = ∑ w ∈ G.neighborFinset u, (y : V → ZMod 2) w := by
              apply Finset.sum_subset
              · exact Finset.inter_subset_left
              · intro w hw hwt
                apply hDs y w
                intro hws
                exact hwt (Finset.mem_inter.mpr ⟨hw, hws⟩)
            _ = 0 := by
              have hyA : A (y : V → ZMod 2) = 0 :=
                LinearMap.mem_ker.mp (hDC y.property)
              have h := congrFun hyA u
              simpa only [A, Matrix.mulVecLin_apply,
                SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using h
        let p := proj D (t.erase v)
        have hkerzero (y : D) (hy : y ∈ LinearMap.ker p) :
            ∀ w, w ∈ t → (y : V → ZMod 2) w = 0 := by
          have hyp : p y = 0 := LinearMap.mem_ker.mp hy
          have hz (w : V) (hw : w ∈ t.erase v) : (y : V → ZMod 2) w = 0 := by
            have h := congrFun hyp (⟨w, hw⟩ : ↥(t.erase v))
            exact h
          have hvzero : (y : V → ZMod 2) v = 0 := by
            have h := hsum y
            have hs : (∑ w ∈ t, (y : V → ZMod 2) w) = (y : V → ZMod 2) v :=
              Finset.sum_eq_single_of_mem v hvt (by
                intro w hw hwv
                exact hz w (Finset.mem_erase.mpr ⟨hwv, hw⟩))
            rw [hs] at h
            exact h
          intro w hw
          by_cases hwv : w = v
          · simpa only [hwv] using hvzero
          · exact hz w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
        let D' : Submodule (ZMod 2) (V → ZMod 2) :=
          (LinearMap.ker p).map D.subtype
        have hD'C : D' ≤ C := by
          intro z hz
          obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hz
          rw [← hyz]
          exact hDC y.property
        have hD's : ∀ z : D', ∀ w, w ∉ s \ t → (z : V → ZMod 2) w = 0 := by
          intro z w hw
          obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp z.property
          change D.subtype y = (z : V → ZMod 2) at hyz
          rw [← hyz]
          by_cases hws : w ∈ s
          · have hwt : w ∈ t := by
              by_contra hwt
              exact hw (Finset.mem_sdiff.mpr ⟨hws, hwt⟩)
            exact hkerzero y hy w hwt
          · exact hDs y w hws
        let q' : ℕ := Module.finrank (ZMod 2) D'
        let e : ℕ := Module.finrank (ZMod 2) (LinearMap.range p)
        have hq' : q' = Module.finrank (ZMod 2) (LinearMap.ker p) :=
          Submodule.finrank_map_subtype_eq D (LinearMap.ker p)
        have hdim : e + q' = q := by
          rw [hq']
          exact LinearMap.finrank_range_add_finrank_ker p
        have he_t : e + 1 ≤ t.card := by
          have h := hproj D (t.erase v)
          change e ≤ (t.erase v).card at h
          rw [Finset.card_erase_of_mem hvt] at h
          omega
        have he_r : e ≤ r := by omega
        have hD'pos : 0 < Module.finrank (ZMod 2) D' := by
          change 0 < q'
          omega
        have hcards : (s \ t).card + t.card = s.card :=
          Finset.card_sdiff_add_card_eq_card ht
        have hlt : (s \ t).card < m := by omega
        have hrec := ih (s \ t).card hlt (s \ t) D' rfl hD'C hD's hD'pos
        change q' + r * (q' + d) ≤ r * ((s \ t).card + 2) at hrec
        have hqe : q' + e = q := by omega
        have het : (r + 1) * e ≤ r * t.card := by
          calc
            (r + 1) * e = r * e + e := by ring
            _ ≤ r * e + r := Nat.add_le_add_left he_r _
            _ = r * (e + 1) := by ring
            _ ≤ r * t.card := Nat.mul_le_mul_left r he_t
        calc
          q + r * (q + d) = (q' + r * (q' + d)) + (r + 1) * e := by
            rw [← hqe]
            ring
          _ ≤ r * ((s \ t).card + 2) + r * t.card := Nat.add_le_add hrec het
          _ = r * (s.card + 2) := by
            rw [← Nat.mul_add]
            congr 1
            omega
  have hmain := hbound n (Finset.univ : Finset V) C (by simp [n]) le_rfl
    (by
      intro x v hv
      exact False.elim (hv (Finset.mem_univ v))) hkpos
  change k + r * (k + d) ≤ r * (n + 2) at hmain
  have hmainR : (k : ℝ) + (r : ℝ) * ((k : ℝ) + (d : ℝ)) ≤
      (r : ℝ) * ((n : ℝ) + 2) := by
    exact_mod_cast hmain
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrreal : (G.maxDegree : ℝ) - 1 = (r : ℝ) := by
    have hcast : (G.maxDegree : ℝ) = (r : ℝ) + 1 := by exact_mod_cast hrmax
    linarith only [hcast]
  have hdiv : (k : ℝ) / (r : ℝ) ≤ (n : ℝ) + 2 - (k : ℝ) - (d : ℝ) := by
    apply (div_le_iff₀ hrR).mpr
    nlinarith only [hmainR]
  have hceil : Int.ceil ((k : ℝ) / ((G.maxDegree : ℝ) - 1)) ≤
      (n : ℤ) + 2 - (k : ℤ) - (d : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    rw [hrreal]
    exact hdiv
  have hceilR : (Int.ceil ((k : ℝ) / ((G.maxDegree : ℝ) - 1)) : ℝ) ≤
      (n : ℝ) + 2 - (k : ℝ) - (d : ℝ) := by
    exact_mod_cast hceil
  linarith only [hceilR]

theorem model_4484035064be73e8a4fc {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (4 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let L : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  have hmin : G.minDegree = 4 := by
    have ha := abs_le.mp h_guard.2.1
    have hu : (G.minDegree : ℝ) < (5 : ℝ) := by
      linarith only [ha.2]
    have hl : (3 : ℝ) < (G.minDegree : ℝ) := by
      linarith only [ha.1]
    have hu' : G.minDegree < 5 := by exact_mod_cast hu
    have hl' : 3 < G.minDegree := by exact_mod_cast hl
    omega
  obtain ⟨d, hd⟩ := h_guard.1
  have hregular : G.IsRegularOfDegree 4 := by
    intro v
    letI : Nonempty V := ⟨v⟩
    calc
      G.degree v = d := hd v
      _ = G.minDegree := hd.minDegree_eq.symm
      _ = 4 := hmin
  have hone : L (1 : V → ZMod 2) = 0 := by
    ext v
    change (Matrix.mulVec (G.adjMatrix (ZMod 2))
      (Function.const V (1 : ZMod 2))) v = 0
    rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hregular, mul_one]
    exact (ZMod.natCast_eq_zero_iff 4 2).2 (by norm_num)
  have hdim : 1 < Module.finrank (ZMod 2) L.ker := by
    have hr : (Module.finrank (ZMod 2) L.ker : ℝ) ≥
        (19999999 / 10000000 : ℝ) := h_guard.2.2
    have hs : (1 : ℝ) < (Module.finrank (ZMod 2) L.ker : ℝ) := by
      linarith only [hr]
    exact_mod_cast hs
  have hex : ∃ x : V → ZMod 2, x ≠ 0 ∧ L x = 0 ∧ x ≠ 1 := by
    by_contra h
    have hle : L.ker ≤
        Submodule.span (ZMod 2) ({1} : Set (V → ZMod 2)) := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Submodule.mem_span_singleton_self _
      exact False.elim (h ⟨x, hx0, LinearMap.mem_ker.mp hx, hx1⟩)
    have hspan : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({1} : Set (V → ZMod 2))) ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod 2)
        ({(1 : V → ZMod 2)} : Set (V → ZMod 2)))
    exact (not_le_of_gt hdim) ((Submodule.finrank_mono hle).trans hspan)
  obtain ⟨x, hx0, hxker, hx1⟩ := hex
  have hy0 : (1 : V → ZMod 2) - x ≠ 0 := by
    intro h
    exact hx1 (sub_eq_zero.mp h).symm
  have hyker : L ((1 : V → ZMod 2) - x) = 0 := by
    rw [map_sub, hone, hxker, sub_self]
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
    intro a
    have hlt := ZMod.val_lt a
    have hv : a.val = 0 ∨ a.val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl ((ZMod.val_eq_zero a).mp hv)
    · exact Or.inr ((ZMod.val_eq_one (n := 2) (by norm_num) a).mp hv)
  have hw : hammingNorm x + hammingNorm ((1 : V → ZMod 2) - x) =
      Fintype.card V := by
    have hf : (Finset.univ : Finset V).filter
        (fun v => ((1 : V → ZMod 2) - x) v ≠ 0) =
        (Finset.univ : Finset V).filter (fun v => ¬(x v ≠ 0)) := by
      apply Finset.filter_congr
      intro v hv
      change ((1 : ZMod 2) - x v ≠ 0) ↔ ¬(x v ≠ 0)
      rcases hbinary (x v) with h | h <;> simp [h]
    unfold hammingNorm
    rw [hf]
    simpa using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (fun v => x v ≠ 0))
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun z => z ≠ 0 ∧ L z = 0)).image hammingNorm
  have hne : weights.Nonempty := by simp [weights]
  change (2 : ℝ) * (weights.min' hne : ℝ) ≤ (Fintype.card V : ℝ)
  have hbound : ∀ z : V → ZMod 2, z ≠ 0 → L z = 0 →
      weights.min' hne ≤ hammingNorm z := by
    intro z hz0 hzker
    apply Finset.min'_le
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz0, hzker⟩, rfl⟩
  have hbx := hbound x hx0 hxker
  have hby := hbound ((1 : V → ZMod 2) - x) hy0 hyker
  have hnat : 2 * weights.min' hne ≤ Fintype.card V := by omega
  exact_mod_cast hnat

theorem nonzero_parity_code_distance_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≤ (Fintype.card V : ℝ) := by
  classical
  let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hk : 0 < Module.finrank (ZMod 2) K := by
    have hr : (0 : ℝ) < (Module.finrank (ZMod 2) K : ℝ) := by
      dsimp [K]
      linarith [h_guard]
    exact_mod_cast hr
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := K)).mp hk
  have hxne : (x : V → ZMod 2) ≠ 0 := by
    intro heq
    apply hx
    exact Subtype.ext heq
  have hxcode : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 := x.property
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun y => y ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin y = 0)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  have hweights : weights.Nonempty := by simp [weights]
  have hxmem : (x : V → ZMod 2) ∈ words := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxcode⟩
  have hle : weights.min' hweights ≤ Fintype.card V :=
    le_trans (Finset.min'_le _ _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(x : V → ZMod 2), hxmem, rfl⟩)))) hammingNorm_le_card_fintype
  change (weights.min' hweights : ℝ) ≤ (Fintype.card V : ℝ)
  exact_mod_cast hle
theorem model_d72c4575e624d63da528 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ (G.Connected) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)))) = ((Fintype.card V : ℝ) + (2 : ℝ)) := by
  sorry
