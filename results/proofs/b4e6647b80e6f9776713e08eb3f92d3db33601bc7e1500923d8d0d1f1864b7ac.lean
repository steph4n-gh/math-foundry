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
