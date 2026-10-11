import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
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

theorem model_6a99e9dbd16d921e7d7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (29999999 / 10000000 : ℝ)))) :
    (((Fintype.card V : ℝ) / (2 : ℝ)) + (1 : ℝ)) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let M := G.adjMatrix (ZMod 2)
  let A := M.mulVecLin
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
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hwne : weights.Nonempty := by simp [weights]
  have hmin : (weights.min' hwne : ℝ) ≥ (29999999 / 10000000 : ℝ) := by
    simpa only [weights, A, M] using h_guard.2.2
  have hsmall (x : V → ZMod 2) (hx : A x = 0)
      (hn : hammingNorm x ≤ 2) : x = 0 := by
    by_contra hx0
    have hm : hammingNorm x ∈ weights := by
      dsimp only [weights]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx0, hx⟩, rfl⟩))
    have hle : weights.min' hwne ≤ hammingNorm x :=
      Finset.min'_le weights _ hm
    have hleR : (weights.min' hwne : ℝ) ≤ 2 := by
      exact_mod_cast hle.trans hn
    linarith only [hmin, hleR]
  let ind (u : Finset V) : V → ZMod 2 := fun v => if v ∈ u then 1 else 0
  have hind : Function.Injective ind := by
    intro u w h
    apply Finset.ext
    intro v
    constructor
    · intro hv
      by_contra hw
      simpa [ind, hv, hw] using congrFun h v
    · intro hw
      by_contra hv
      simpa [ind, hv, hw] using congrFun h v
  have hweight (u w : Finset V) :
      hammingNorm (ind u - ind w) ≤ u.card + w.card := by
    unfold hammingNorm
    calc
      _ ≤ (u ∪ w).card := by
        apply Finset.card_le_card
        intro v hv
        by_contra hnot
        have hu : v ∉ u := fun h => hnot (Finset.mem_union.mpr (Or.inl h))
        have hw : v ∉ w := fun h => hnot (Finset.mem_union.mpr (Or.inr h))
        have hh := (Finset.mem_filter.mp hv).2
        exact hh (by simp [ind, hu, hw])
      _ ≤ u.card + w.card := Finset.card_union_le u w
  have hExtend (u w : Finset V) (hw : w ⊆ u) :
      E u (fun v : u => ind w (v : V)) = ind w := by
    funext v
    by_cases hv : v ∈ u
    · simp [E, hv]
    · have hwv : v ∉ w := fun h => hv (hw h)
      simp [E, ind, hv, hwv]
  have hpack (u : Finset V) :
      (1 : ℝ) + (u.card : ℝ) ≤
        (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (A.comp (E u))) := by
    let Q := u.powersetCard 0 ∪ u.powersetCard 1
    have hQ (w : Finset V) (hw : w ∈ Q) : w ⊆ u ∧ w.card ≤ 1 := by
      rcases Finset.mem_union.mp hw with hw | hw
      · have h := Finset.mem_powersetCard.mp hw
        refine ⟨h.1, ?_⟩
        rw [h.2]
        omega
      · have h := Finset.mem_powersetCard.mp hw
        exact ⟨h.1, h.2.le⟩
    let f : Q → LinearMap.range (A.comp (E u)) := fun w =>
      ⟨A (ind w.val), by
        refine ⟨(fun v : u => ind w.val (v : V)), ?_⟩
        change A (E u (fun v : u => ind w.val (v : V))) = A (ind w.val)
        exact congrArg A (hExtend u w.val (hQ w.val w.property).1)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hsy : A (ind x.val) = A (ind y.val) :=
        congrArg (fun z : LinearMap.range (A.comp (E u)) => (z : V → ZMod 2)) hxy
      have hk : A (ind x.val - ind y.val) = 0 := by
        rw [map_sub, hsy, sub_self]
      have hnx := (hQ x.val x.property).2
      have hny := (hQ y.val y.property).2
      have hw := hweight x.val y.val
      have hn : hammingNorm (ind x.val - ind y.val) ≤ 2 := by omega
      have heq : ind x.val = ind y.val :=
        sub_eq_zero.mp (hsmall _ hk hn)
      exact Subtype.ext (hind heq)
    have hd01 : Disjoint (u.powersetCard 0) (u.powersetCard 1) :=
      Finset.disjoint_powersetCard_of_ne (by decide) u u
    have hcardQ : Q.card = 1 + u.card := by
      dsimp only [Q]
      rw [Finset.card_union_of_disjoint hd01]
      simp only [Finset.card_powersetCard, Nat.choose_zero_right, Nat.choose_one_right]
    have hc : Q.card ≤ 2 ^ Module.finrank (ZMod 2)
        (LinearMap.range (A.comp (E u))) := by
      calc
        _ = Fintype.card Q := (Fintype.card_coe Q).symm
        _ ≤ Fintype.card (LinearMap.range (A.comp (E u))) :=
          Fintype.card_le_of_injective f hf
        _ = _ := by
          rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    rw [hcardQ] at hc
    exact_mod_cast hc
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
  have hp := hpack s
  have hq := hpack t
  rw [hrs] at hp
  rw [hrt] at hq
  have hcardN : s.card + t.card = Fintype.card V := Finset.card_add_card_compl s
  have hcardR : (s.card : ℝ) + (t.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcardN
  have hpoly : (Fintype.card V : ℝ) / 2 + 1 ≤ (2 : ℝ) ^ B.rank := by
    linarith only [hp, hq, hcardR]
  have hn : 2 * B.rank + Module.finrank (ZMod 2) (LinearMap.ker A) =
      Fintype.card V := by
    simpa only [hArank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hnR : (2 : ℝ) * (B.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hn
  have hreal : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (2 : ℝ) * (B.rank : ℝ) := by
    linarith only [hnR]
  have hexp : Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 *
      Real.log (1 + (1 : ℝ))) = (2 : ℝ) ^ B.rank := by
    rw [hreal]
    have hh : (2 : ℝ) * (B.rank : ℝ) / 2 = (B.rank : ℝ) := by ring
    rw [hh, show (1 : ℝ) + 1 = 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change (Fintype.card V : ℝ) / 2 + 1 ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 * Real.log (1 + (1 : ℝ)))
  rw [hexp]
  exact hpoly

theorem model_76e242812f261f42bd47 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (49999999 / 10000000 : ℝ)))) :
    (((1 : ℝ) + ((Fintype.card V : ℝ) / (4 : ℝ))) + (((Fintype.card V : ℝ) ^ 2) / (8 : ℝ))) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let M := G.adjMatrix (ZMod 2)
  let A := M.mulVecLin
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
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hwne : weights.Nonempty := by simp [weights]
  have hmin : (weights.min' hwne : ℝ) ≥ (49999999 / 10000000 : ℝ) := by
    simpa only [weights, A, M] using h_guard.2.2
  have hsmall (x : V → ZMod 2) (hx : A x = 0)
      (hn : hammingNorm x ≤ 4) : x = 0 := by
    by_contra hx0
    have hm : hammingNorm x ∈ weights := by
      dsimp only [weights]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx0, hx⟩, rfl⟩))
    have hle : weights.min' hwne ≤ hammingNorm x :=
      Finset.min'_le weights _ hm
    have hleR : (weights.min' hwne : ℝ) ≤ 4 := by
      exact_mod_cast hle.trans hn
    linarith only [hmin, hleR]
  let ind (u : Finset V) : V → ZMod 2 := fun v => if v ∈ u then 1 else 0
  have hind : Function.Injective ind := by
    intro u w h
    apply Finset.ext
    intro v
    constructor
    · intro hv
      by_contra hw
      simpa [ind, hv, hw] using congrFun h v
    · intro hw
      by_contra hv
      simpa [ind, hv, hw] using congrFun h v
  have hweight (u w : Finset V) :
      hammingNorm (ind u - ind w) ≤ u.card + w.card := by
    unfold hammingNorm
    calc
      _ ≤ (u ∪ w).card := by
        apply Finset.card_le_card
        intro v hv
        by_contra hnot
        have hu : v ∉ u := fun h => hnot (Finset.mem_union.mpr (Or.inl h))
        have hw : v ∉ w := fun h => hnot (Finset.mem_union.mpr (Or.inr h))
        have hh := (Finset.mem_filter.mp hv).2
        exact hh (by simp [ind, hu, hw])
      _ ≤ u.card + w.card := Finset.card_union_le u w
  have hExtend (u w : Finset V) (hw : w ⊆ u) :
      E u (fun v : u => ind w (v : V)) = ind w := by
    funext v
    by_cases hv : v ∈ u
    · simp [E, hv]
    · have hwv : v ∉ w := fun h => hv (hw h)
      simp [E, ind, hv, hwv]
  have hpack (u : Finset V) :
      (1 : ℝ) + (u.card : ℝ) + (u.card : ℝ) * ((u.card : ℝ) - 1) / 2 ≤
        (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (A.comp (E u))) := by
    let Q := u.powersetCard 0 ∪ (u.powersetCard 1 ∪ u.powersetCard 2)
    have hQ (w : Finset V) (hw : w ∈ Q) : w ⊆ u ∧ w.card ≤ 2 := by
      rcases Finset.mem_union.mp hw with hw | hw
      · have h := Finset.mem_powersetCard.mp hw
        refine ⟨h.1, ?_⟩
        rw [h.2]
        omega
      · rcases Finset.mem_union.mp hw with hw | hw
        · have h := Finset.mem_powersetCard.mp hw
          refine ⟨h.1, ?_⟩
          rw [h.2]
          omega
        · have h := Finset.mem_powersetCard.mp hw
          refine ⟨h.1, ?_⟩
          rw [h.2]
    let f : Q → LinearMap.range (A.comp (E u)) := fun w =>
      ⟨A (ind w.val), by
        refine ⟨(fun v : u => ind w.val (v : V)), ?_⟩
        change A (E u (fun v : u => ind w.val (v : V))) = A (ind w.val)
        exact congrArg A (hExtend u w.val (hQ w.val w.property).1)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have hsy : A (ind x.val) = A (ind y.val) :=
        congrArg (fun z : LinearMap.range (A.comp (E u)) => (z : V → ZMod 2)) hxy
      have hk : A (ind x.val - ind y.val) = 0 := by
        rw [map_sub, hsy, sub_self]
      have hnx := (hQ x.val x.property).2
      have hny := (hQ y.val y.property).2
      have hw := hweight x.val y.val
      have hn : hammingNorm (ind x.val - ind y.val) ≤ 4 := by omega
      have heq : ind x.val = ind y.val :=
        sub_eq_zero.mp (hsmall _ hk hn)
      exact Subtype.ext (hind heq)
    have hd01 : Disjoint (u.powersetCard 0) (u.powersetCard 1) :=
      Finset.disjoint_powersetCard_of_ne (by decide) u u
    have hd02 : Disjoint (u.powersetCard 0) (u.powersetCard 2) :=
      Finset.disjoint_powersetCard_of_ne (by decide) u u
    have hd12 : Disjoint (u.powersetCard 1) (u.powersetCard 2) :=
      Finset.disjoint_powersetCard_of_ne (by decide) u u
    have hcardQ : Q.card = 1 + u.card + u.card.choose 2 := by
      dsimp only [Q]
      rw [Finset.card_union_of_disjoint
          (Finset.disjoint_union_right.mpr ⟨hd01, hd02⟩),
        Finset.card_union_of_disjoint hd12]
      simp only [Finset.card_powersetCard, Nat.choose_zero_right, Nat.choose_one_right]
      omega
    have hc : Q.card ≤ 2 ^ Module.finrank (ZMod 2)
        (LinearMap.range (A.comp (E u))) := by
      calc
        _ = Fintype.card Q := (Fintype.card_coe Q).symm
        _ ≤ Fintype.card (LinearMap.range (A.comp (E u))) :=
          Fintype.card_le_of_injective f hf
        _ = _ := by
          rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    rw [hcardQ] at hc
    have hcast : (1 : ℝ) + (u.card : ℝ) + (u.card.choose 2 : ℝ) ≤
        (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (A.comp (E u))) := by
      exact_mod_cast hc
    rw [Nat.cast_choose_two] at hcast
    exact hcast
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
  have hp := hpack s
  have hq := hpack t
  rw [hrs] at hp
  rw [hrt] at hq
  have hcardN : s.card + t.card = Fintype.card V := Finset.card_add_card_compl s
  have hcardR : (s.card : ℝ) + (t.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcardN
  have hpoly : (1 : ℝ) + (Fintype.card V : ℝ) / 4 +
      (Fintype.card V : ℝ) ^ 2 / 8 ≤ (2 : ℝ) ^ B.rank := by
    rw [← hcardR]
    nlinarith only [hp, hq, sq_nonneg ((s.card : ℝ) - (t.card : ℝ))]
  have hn : 2 * B.rank + Module.finrank (ZMod 2) (LinearMap.ker A) =
      Fintype.card V := by
    simpa only [hArank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hnR : (2 : ℝ) * (B.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hn
  have hreal : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (2 : ℝ) * (B.rank : ℝ) := by
    linarith only [hnR]
  have hexp : Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 *
      Real.log (1 + (1 : ℝ))) = (2 : ℝ) ^ B.rank := by
    rw [hreal]
    have hh : (2 : ℝ) * (B.rank : ℝ) / 2 = (B.rank : ℝ) := by ring
    rw [hh, show (1 : ℝ) + 1 = 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change (1 + (Fintype.card V : ℝ) / 4) + (Fintype.card V : ℝ) ^ 2 / 8 ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 * Real.log (1 + (1 : ℝ)))
  rw [hexp]
  exact hpoly

theorem model_af2f7de6fc0dc093a01d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (39999999 / 10000000 : ℝ)))) :
    (Fintype.card V : ℝ) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) - (1 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let L : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker L
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ L x = 0)).image hammingNorm
  have hmin : (39999999 / 10000000 : ℝ) ≤
      (weights.min' (by simp [weights]) : ℝ) := h_guard.2
  have hdist : ∀ x : V → ZMod 2, x ≠ 0 → L x = 0 →
      4 ≤ hammingNorm x := by
    intro x hx hL
    have hmem : hammingNorm x ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hL⟩
    have hle : (weights.min' (by simp [weights]) : ℝ) ≤
        (hammingNorm x : ℝ) := by
      exact_mod_cast (Finset.min'_le weights (hammingNorm x) hmem)
    have hr := hmin.trans hle
    by_contra hnot
    have hsmall : hammingNorm x ≤ 3 := by omega
    have hsmallR : (hammingNorm x : ℝ) ≤ 3 := by
      exact_mod_cast hsmall
    linarith
  have hsent : weights.min' (by simp [weights]) ≤ Fintype.card V + 1 :=
    Finset.min'_le weights (Fintype.card V + 1) (by simp [weights])
  have hsentR : (weights.min' (by simp [weights]) : ℝ) ≤
      ((Fintype.card V + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsent
  have hnpos : 0 < Fintype.card V := by
    by_contra hnot
    have hzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hnot
    have hbad := hmin.trans hsentR
    norm_num [hzero] at hbad
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hnpos
  letI : Fintype C := Fintype.ofFinite C
  let f : C × (V × ZMod 2) → V → ZMod 2 := fun p t =>
    (p.1 : V → ZMod 2) t +
      ((if t = p.2.1 then 1 else 0) + (if t = a then p.2.2 else 0))
  have hf : Function.Injective f := by
    rintro ⟨x, v, b⟩ ⟨y, w, c⟩ h
    have hxy : x = y := by
      have hx : L (x : V → ZMod 2) = 0 := x.property
      have hy : L (y : V → ZMod 2) = 0 := y.property
      have hker : L ((x : V → ZMod 2) - (y : V → ZMod 2)) = 0 := by
        simp only [map_sub, hx, hy, sub_self]
      have hweight : hammingNorm ((x : V → ZMod 2) - (y : V → ZMod 2)) ≤ 3 := by
        calc
          hammingNorm ((x : V → ZMod 2) - (y : V → ZMod 2)) ≤
              ({a, v, w} : Finset V).card := by
            apply Finset.card_le_card
            intro t ht
            by_contra hnot
            have ha : t ≠ a := by
              intro he
              apply hnot
              simp [he]
            have hv : t ≠ v := by
              intro he
              apply hnot
              simp [he]
            have hw : t ≠ w := by
              intro he
              apply hnot
              simp [he]
            have hh := congrFun h t
            dsimp [f] at hh
            have hval : (x : V → ZMod 2) t = (y : V → ZMod 2) t := by
              simpa only [if_neg ha, if_neg hv, if_neg hw, zero_add, add_zero] using hh
            exact (Finset.mem_filter.mp ht).2 (by simp [Pi.sub_apply, hval])
          _ ≤ 3 := Finset.card_le_three
      have hzero : (x : V → ZMod 2) - (y : V → ZMod 2) = 0 := by
        by_contra hne
        have hd := hdist _ hne hker
        omega
      exact Subtype.ext (sub_eq_zero.mp hzero)
    subst y
    have heq : ∀ t : V,
        (if t = v then (1 : ZMod 2) else 0) + (if t = a then b else 0) =
        (if t = w then (1 : ZMod 2) else 0) + (if t = a then c else 0) := by
      intro t
      have hh := congrFun h t
      dsimp [f] at hh
      exact add_left_cancel hh
    have hvw : v = w := by
      by_contra hne
      by_cases hva : v = a
      · have hwa : w ≠ a := by
          intro hwa
          exact hne (hva.trans hwa.symm)
        have hwv : w ≠ v := Ne.symm hne
        have hh := heq w
        simp only [if_neg hwv, if_pos rfl, if_neg hwa, zero_add, add_zero] at hh
        exact zero_ne_one hh
      · have hh := heq v
        simp only [if_pos rfl, if_neg hne, if_neg hva, add_zero] at hh
        exact one_ne_zero hh
    have hbc : b = c := by
      have hh := heq a
      rw [hvw] at hh
      simp only [if_pos rfl] at hh
      exact add_left_cancel hh
    exact Prod.ext rfl (Prod.ext hvw hbc)
  have hcardC : Fintype.card C = 2 ^ Module.finrank (ZMod 2) C := by
    simpa only [ZMod.card, Fintype.card_fin] using
      (Module.card_fintype (Module.finBasis (ZMod 2) C))
  have hcount : 2 ^ Module.finrank (ZMod 2) C * (Fintype.card V * 2) ≤
      2 ^ Fintype.card V := by
    have hc := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_prod, Fintype.card_fun, ZMod.card, hcardC] using hc
  have hcountR : (2 : ℝ) ^ Module.finrank (ZMod 2) C *
      ((Fintype.card V : ℝ) * 2) ≤ (2 : ℝ) ^ Fintype.card V := by
    exact_mod_cast hcount
  have hlog : Real.exp (Real.log (1 + (1 : ℝ))) = 2 := by
    rw [Real.exp_log (by norm_num)]
    norm_num
  have hexp : Real.exp ((((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) C : ℝ)) - 1) * Real.log (1 + (1 : ℝ))) =
      (2 : ℝ) ^ Fintype.card V / ((2 : ℝ) ^ Module.finrank (ZMod 2) C * 2) := by
    simp only [sub_mul, one_mul, Real.exp_sub, Real.exp_nat_mul, hlog, div_div]
  change (Fintype.card V : ℝ) ≤ Real.exp ((((Fintype.card V : ℝ) -
    (Module.finrank (ZMod 2) C : ℝ)) - 1) * Real.log (1 + (1 : ℝ)))
  rw [hexp]
  apply (le_div_iff₀ (by positivity :
    0 < (2 : ℝ) ^ Module.finrank (ZMod 2) C * 2)).2
  nlinarith only [hcountR]

theorem model_b019db4c751eaa507b7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (59999999 / 10000000 : ℝ)))) :
    ((1 : ℝ) + ((((Fintype.card V : ℝ) ^ 3) + ((20 : ℝ) * (Fintype.card V : ℝ))) / (48 : ℝ))) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧
      ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  have hg : (((weights.min' hw - 1 : ℕ) : ℝ)) ≥
      (59999999 / 10000000 : ℝ) := h_guard.2.2
  have hmin : 6 ≤ weights.min' hw - 1 := by
    by_contra h
    have hn : weights.min' hw - 1 ≤ 5 := by omega
    have hr : (((weights.min' hw - 1 : ℕ) : ℝ)) ≤ 5 := by
      exact_mod_cast hn
    linarith only [hg, hr]
  have hsmall (S : Finset V) (hS : S.Nonempty) (hcard : S.card ≤ 6) :
      ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    by_contra h
    have hm : S.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS, h⟩, rfl⟩
    have hl : weights.min' hw ≤ S.card := Finset.min'_le weights S.card hm
    omega
  obtain ⟨c⟩ := h_guard.1
  let s0 : Finset V := Finset.univ.filter (fun v => c v = 0)
  have hi0 : ∀ v ∈ s0, ∀ w ∈ s0, ¬ G.Adj v w := by
    intro v hv w hw' hadj
    have hv0 : c v = 0 := (Finset.mem_filter.mp hv).2
    have hw0 : c w = 0 := (Finset.mem_filter.mp hw').2
    exact c.valid hadj (hv0.trans hw0.symm)
  have hi1 : ∀ v ∉ s0, ∀ w ∉ s0, ¬ G.Adj v w := by
    intro v hv w hw' hadj
    have hv0 : c v ≠ 0 := by simpa [s0] using hv
    have hw0 : c w ≠ 0 := by simpa [s0] using hw'
    have hv1 : (c v).val = 1 := by
      have hlt := (c v).isLt
      have hnz : (c v).val ≠ 0 := by
        intro h
        exact hv0 (Fin.ext h)
      omega
    have hw1 : (c w).val = 1 := by
      have hlt := (c w).isLt
      have hnz : (c w).val ≠ 0 := by
        intro h
        exact hw0 (Fin.ext h)
      omega
    exact c.valid hadj (Fin.ext (hv1.trans hw1.symm))
  obtain ⟨s, hsize, hi, hj⟩ : ∃ s : Finset V,
      Fintype.card V ≤ 2 * s.card ∧
      (∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w) ∧
      (∀ v ∉ s, ∀ w ∉ s, ¬ G.Adj v w) := by
    by_cases h : Fintype.card V ≤ 2 * s0.card
    · exact ⟨s0, h, hi0, hi1⟩
    · refine ⟨s0ᶜ, ?_, ?_, ?_⟩
      · have hc := Finset.card_add_card_compl s0
        omega
      · simpa only [Finset.mem_compl] using hi1
      · simpa only [Finset.mem_compl, not_not] using hi0
  let B := {v : V // v ∉ s}
  let M : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let C : Matrix B s (ZMod 2) := fun i j => M i.val j.val
  let e : (↥s ⊕ B) ≃ V := Equiv.sumCompl (fun v : V => v ∈ s)
  let N : Matrix (↥s ⊕ B) (↥s ⊕ B) (ZMod 2) := M.submatrix e e
  have hN : N = Matrix.fromBlocks (0 : Matrix s s (ZMod 2))
      C.transpose C (0 : Matrix B B (ZMod 2)) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · change M i.val j.val = 0
        simp [M, SimpleGraph.adjMatrix_apply, hi i.val i.property j.val j.property]
      · change M i.val j.val = M j.val i.val
        exact (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply j.val i.val
    · rcases j with j | j
      · rfl
      · change M i.val j.val = 0
        simp [M, SimpleGraph.adjMatrix_apply, hj i.val i.property j.val j.property]
  let E : ((↥s ⊕ B) → ZMod 2) ≃ₗ[ZMod 2]
      ((s → ZMod 2) × (B → ZMod 2)) :=
    LinearEquiv.sumArrowLequivProdArrow s B (ZMod 2) (ZMod 2)
  let E' : ((↥s ⊕ B) → ZMod 2) ≃ₗ[ZMod 2]
      ((B → ZMod 2) × (s → ZMod 2)) :=
    E.trans (LinearEquiv.prodComm (ZMod 2) (s → ZMod 2) (B → ZMod 2))
  let P : ((s → ZMod 2) × (B → ZMod 2)) →ₗ[ZMod 2]
      ((B → ZMod 2) × (s → ZMod 2)) :=
    C.mulVecLin.prodMap C.transpose.mulVecLin
  have hconj : (E'.toLinearMap.comp N.mulVecLin).comp E.symm.toLinearMap = P := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change Matrix.mulVec N (Sum.elim x.1 x.2) (Sum.inr i) =
        Matrix.mulVec C x.1 i
      rw [hN, Matrix.fromBlocks_mulVec]
      simp [Function.comp_def]
    · funext i
      change Matrix.mulVec N (Sum.elim x.1 x.2) (Sum.inl i) =
        Matrix.mulVec C.transpose x.2 i
      rw [hN, Matrix.fromBlocks_mulVec]
      simp [Function.comp_def]
  have hPrange : Module.finrank (ZMod 2) (LinearMap.range P) = N.rank := by
    calc
      _ = Module.finrank (ZMod 2)
          (LinearMap.range (E'.toLinearMap.comp N.mulVecLin)) := by
        rw [← hconj, LinearMap.range_comp_of_range_eq_top _ E.symm.range]
      _ = N.rank := by
        rw [LinearMap.range_comp]
        exact E'.finrank_map_eq (LinearMap.range N.mulVecLin)
  have hPprod : Module.finrank (ZMod 2) (LinearMap.range P) =
      C.rank + C.transpose.rank := by
    calc
      _ = Module.finrank (ZMod 2)
          ((LinearMap.range C.mulVecLin).prod
            (LinearMap.range C.transpose.mulVecLin)) := by
        dsimp only [P]
        rw [LinearMap.range_prodMap]
      _ = Module.finrank (ZMod 2)
          ((LinearMap.range C.mulVecLin) ×
            (LinearMap.range C.transpose.mulVecLin)) :=
        (Submodule.prodEquiv _ _).finrank_eq
      _ = C.rank + C.transpose.rank := by
        simp only [Module.finrank_prod, Matrix.rank]
  have hMrank : M.rank = 2 * C.rank := by
    calc
      M.rank = N.rank := (Matrix.rank_submatrix M e e).symm
      _ = C.rank + C.transpose.rank := hPrange.symm.trans hPprod
      _ = 2 * C.rank := by simp only [Matrix.rank_transpose, two_mul]
  let L : Finset (Finset V) :=
    (Finset.range 4).biUnion (fun k => s.powersetCard k)
  have hL (S : Finset V) (hS : S ∈ L) : S ⊆ s ∧ S.card ≤ 3 := by
    obtain ⟨k, hk, hSk⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSk
    have hlt := Finset.mem_range.mp hk
    exact ⟨hsub, by omega⟩
  have hdisj : ((Finset.range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => s.powersetCard k) := by
    intro i hi' j hj' hij
    exact Finset.disjoint_powersetCard_of_ne hij s s
  have hLcard : L.card = 1 + s.card + s.card.choose 2 + s.card.choose 3 := by
    dsimp only [L]
    rw [Finset.card_biUnion hdisj]
    simp [Finset.card_powersetCard, Finset.sum_range_succ]
  let x : Finset V → (s → ZMod 2) := fun S u =>
    if u.val ∈ S then 1 else 0
  let q : Finset V → LinearMap.range C.mulVecLin := fun S =>
    ⟨C.mulVecLin (x S), ⟨x S, rfl⟩⟩
  have hq : Set.InjOn q (L : Set (Finset V)) := by
    intro S hS T hT hST
    obtain ⟨hSs, hSc⟩ := hL S hS
    obtain ⟨hTs, hTc⟩ := hL T hT
    by_contra hne
    let D : Finset V := symmDiff S T
    have hDnonempty : D.Nonempty := Finset.symmDiff_nonempty.mpr hne
    have hDcard : D.card ≤ 6 := by
      have hd : D.card ≤ (S ∪ T).card :=
        Finset.card_le_card Finset.symmDiff_subset_union
      have hu := Finset.card_union_le S T
      omega
    have hDsub : D ⊆ s := by
      intro u hu
      rcases Finset.mem_symmDiff.mp hu with h | h
      · exact hSs h.1
      · exact hTs h.1
    obtain ⟨v, w, hwD, hvw, huniq⟩ := hsmall D hDnonempty hDcard
    have hws : w ∈ s := hDsub hwD
    have hvns : v ∉ s := by
      intro hv
      exact hi v hv w hws hvw
    have hxD : x D = x S + x T := by
      funext u
      by_cases huS : u.val ∈ S <;> by_cases huT : u.val ∈ T <;>
        simp [x, D, Finset.mem_symmDiff, huS, huT, ZModModule.add_self]
    have hST' : C.mulVecLin (x S) = C.mulVecLin (x T) :=
      congrArg (fun z : LinearMap.range C.mulVecLin => z.val) hST
    have hzero : C.mulVecLin (x D) = 0 := by
      rw [hxD, map_add, hST']
      funext u
      exact ZModModule.add_self _
    have hvzero := congrFun hzero (⟨v, hvns⟩ : B)
    change (∑ u : s, M v u.val * (if u.val ∈ D then 1 else 0)) = 0 at hvzero
    have hvone : (∑ u : s, M v u.val * (if u.val ∈ D then 1 else 0)) = 1 := by
      calc
        _ = M v w * (if w ∈ D then 1 else 0) := by
          refine Finset.sum_eq_single (⟨w, hws⟩ : s) ?_ ?_
          · intro u hu hune
            by_cases huD : u.val ∈ D
            · have hnadj : ¬ G.Adj v u.val := by
                intro hadj
                apply hune
                exact Subtype.ext (huniq u.val huD hadj)
              simp [M, SimpleGraph.adjMatrix_apply, hnadj]
            · simp [huD]
          · simp
        _ = 1 := by simp [M, SimpleGraph.adjMatrix_apply, hvw, hwD]
    exact one_ne_zero (hvone.symm.trans hvzero)
  have hcount : 1 + s.card + s.card.choose 2 + s.card.choose 3 ≤ 2 ^ C.rank := by
    calc
      _ = L.card := hLcard.symm
      _ = (L.image q).card := (Finset.card_image_of_injOn hq).symm
      _ ≤ Fintype.card (LinearMap.range C.mulVecLin) := Finset.card_le_univ _
      _ = 2 ^ C.rank := by
        simpa only [ZMod.card, Matrix.rank] using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range C.mulVecLin))
  have hchoose3 (a : ℕ) : (6 : ℝ) * (a.choose 3 : ℝ) =
      (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ, Nat.cast_choose_two ℝ a]
      nlinarith only [ih]
  have hcountR : (1 : ℝ) + (s.card : ℝ) + (s.card.choose 2 : ℝ) +
      (s.card.choose 3 : ℝ) ≤ (2 : ℝ) ^ C.rank := by
    exact_mod_cast hcount
  have hvolume : (1 : ℝ) + ((s.card : ℝ) ^ 3 + 5 * (s.card : ℝ)) / 6 ≤
      (2 : ℝ) ^ C.rank := by
    rw [Nat.cast_choose_two ℝ s.card] at hcountR
    have hc3 := hchoose3 s.card
    nlinarith only [hc3, hcountR]
  have hsizeR : (Fintype.card V : ℝ) ≤ 2 * (s.card : ℝ) := by
    exact_mod_cast hsize
  have hcube : (Fintype.card V : ℝ) ^ 3 ≤ (2 * (s.card : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hsizeR 3
  have hlarge : (1 : ℝ) + ((Fintype.card V : ℝ) ^ 3 +
      20 * (Fintype.card V : ℝ)) / 48 ≤
      1 + ((s.card : ℝ) ^ 3 + 5 * (s.card : ℝ)) / 6 := by
    nlinarith only [hsizeR, hcube]
  have hdim : M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have htotal : Fintype.card V =
      Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * C.rank := by
    rw [hMrank] at hdim
    omega
  have hreal : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) =
      2 * (C.rank : ℝ) := by
    have hc : (Fintype.card V : ℝ) =
        (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) +
        2 * (C.rank : ℝ) := by
      exact_mod_cast htotal
    linarith only [hc]
  have hhalf : (2 : ℝ) * (C.rank : ℝ) / 2 = (C.rank : ℝ) := by ring
  have hexp : Real.exp ((C.rank : ℝ) * Real.log (1 + (1 : ℝ))) =
      (2 : ℝ) ^ C.rank := by
    simp only [show (1 : ℝ) + 1 = 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change (1 : ℝ) + ((Fintype.card V : ℝ) ^ 3 +
      20 * (Fintype.card V : ℝ)) / 48 ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ)) / 2 *
      Real.log (1 + (1 : ℝ)))
  rw [hreal, hhalf, hexp]
  exact hlarge.trans hvolume

theorem model_19ffa035acae97b080f4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  have hbit : ∀ a b : ZMod 2,
      (if a ≠ 0 then (1 : ℕ) else 0) +
        (if b ≠ 0 then 1 else 0) +
        (if a + b ≠ 0 then 1 else 0) ≤ 2 := by
    decide
  have hbit_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    decide
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  let d : ℕ := weights.min' (by simp [weights])
  change (k : ℝ) + (d : ℝ) ≤ (n : ℝ)
  have hkreal : (19999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2
  have hk : 2 ≤ k := by
    by_contra h
    have hle : (k : ℝ) ≤ 1 := by
      exact_mod_cast (show k ≤ 1 by omega)
    linarith
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have heq : G.minDegree = 0 := by omega
    have hg := h_guard.1
    rw [heq] at hg
    norm_num at hg
  have hkn : k ≤ n := by
    calc
      k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
      _ = n := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hn : 0 < Fintype.card V := by
    change 0 < n
    omega
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp
    (lt_of_lt_of_le hdeg (G.minDegree_le_degree u))
  let a : LinearMap.range A :=
    ⟨A (Pi.single u 1), ⟨Pi.single u 1, rfl⟩⟩
  let b : LinearMap.range A :=
    ⟨A (Pi.single v 1), ⟨Pi.single v 1, rfl⟩⟩
  have hb : b ≠ 0 := by
    intro heq
    have hh := congrArg
      (fun w : LinearMap.range A => (w : V → ZMod 2) u) heq
    simp [b, A, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, huv] at hh
  have hba : ∀ c : ZMod 2, c • b ≠ a := by
    intro c heq
    have hh := congrArg
      (fun w : LinearMap.range A => (w : V → ZMod 2) v) heq
    simp [a, b, A, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, G.adj_symm huv] at hh
  have hab : LinearIndependent (ZMod 2) ![a, b] :=
    linearIndependent_fin2.mpr ⟨hb, hba⟩
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range A) := by
    simpa using hab.fintype_card_le_finrank
  have hrk : Module.finrank (ZMod 2) (LinearMap.range A) + k = n := by
    simpa [k, C, n, Module.finrank_fintype_fun_eq_card]
      using LinearMap.finrank_range_add_finrank_ker A
  have hkn2 : k + 2 ≤ n := by omega
  obtain ⟨s, hsu, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset V)) (n := k - 2)
    (by simpa [n] using (Nat.sub_le k 2).trans hkn)
  let p : C →ₗ[ZMod 2] (s → ZMod 2) :=
    { toFun := fun w i => (w : V → ZMod 2) i.1
      map_add' := by intro w z; rfl
      map_smul' := by intro c w; rfl }
  have hpr : Module.finrank (ZMod 2) (LinearMap.range p) ≤ k - 2 := by
    calc
      _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
      _ = s.card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      _ = k - 2 := hs
  have hpdim : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker p) := by
    have heq := LinearMap.finrank_range_add_finrank_ker p
    change Module.finrank (ZMod 2) (LinearMap.range p) +
      Module.finrank (ZMod 2) (LinearMap.ker p) = k at heq
    omega
  obtain ⟨z, hz⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := LinearMap.ker p) hpdim
  let x : V → ZMod 2 := (z 0).val.val
  let y : V → ZMod 2 := (z 1).val.val
  have hxA : A x = 0 := LinearMap.mem_ker.mp (z 0).val.property
  have hyA : A y = 0 := LinearMap.mem_ker.mp (z 1).val.property
  have hx : x ≠ 0 := by
    intro heq
    apply hz.ne_zero 0
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hy : y ≠ 0 := by
    intro heq
    apply hz.ne_zero 1
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hxy : x + y ≠ 0 := by
    intro heq
    have hzeq : z 0 = z 1 := by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact hbit_eq (x i) (y i) (congrFun heq i)
    exact (by decide : (0 : Fin 2) ≠ 1) (hz.injective hzeq)
  have hxyA : A (x + y) = 0 := by
    rw [map_add, hxA, hyA, add_zero]
  have hxs : ∀ i ∈ s, x i = 0 := by
    intro i hi
    have heq : p (z 0).val = 0 := LinearMap.mem_ker.mp (z 0).property
    exact congrFun heq ⟨i, hi⟩
  have hys : ∀ i ∈ s, y i = 0 := by
    intro i hi
    have heq : p (z 1).val = 0 := LinearMap.mem_ker.mp (z 1).property
    exact congrFun heq ⟨i, hi⟩
  have hd : ∀ t : V → ZMod 2, t ≠ 0 → A t = 0 → d ≤ hammingNorm t := by
    intro t ht hAt
    have hm : hammingNorm t ∈ weights := by
      dsimp only [weights]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht, hAt⟩, rfl⟩))
    exact Finset.min'_le weights (hammingNorm t) hm
  have hdx := hd x hx hxA
  have hdy := hd y hy hyA
  have hdxy := hd (x + y) hxy hxyA
  have hpoint : ∀ i : V,
      (if x i ≠ 0 then (1 : ℕ) else 0) +
        (if y i ≠ 0 then 1 else 0) +
        (if (x + y) i ≠ 0 then 1 else 0) ≤
          if i ∈ s then 0 else 2 := by
    intro i
    by_cases hi : i ∈ s
    · simp [hi, hxs i hi, hys i hi, Pi.add_apply]
    · simpa [hi, Pi.add_apply] using hbit (x i) (y i)
  have hcomp : (Finset.univ : Finset V).filter (fun i => i ∉ s) = sᶜ := by
    ext i
    simp
  have hsum : hammingNorm x + hammingNorm y + hammingNorm (x + y) ≤
      2 * (n - s.card) := by
    calc
      _ = ∑ i : V,
          ((if x i ≠ 0 then (1 : ℕ) else 0) +
            (if y i ≠ 0 then 1 else 0) +
            (if (x + y) i ≠ 0 then 1 else 0)) := by
        simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
      _ ≤ ∑ i : V, if i ∈ s then (0 : ℕ) else 2 :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = 2 * (n - s.card) := by
        rw [Finset.sum_ite]
        simp [hcomp, Finset.card_compl, n, Nat.mul_comm]
  have h3d : 3 * d ≤ 2 * (n - s.card) := by omega
  have hfinal : k + d ≤ n := by omega
  exact_mod_cast hfinal
theorem model_639525f7a46b1b3dbd00 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (39999999 / 10000000 : ℝ)))) :
    (Fintype.card V : ℝ) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  sorry
