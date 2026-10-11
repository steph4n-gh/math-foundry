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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

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

theorem model_7f80b6911ecd9dc4c880 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) = ((2 : ℝ) * ((Int.floor (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ))) : ℝ)) := by
  classical
  suffices haux : ∀ (n : ℕ) (W : Type _) [Fintype W],
      Fintype.card W = n → ∀ (M : Matrix W W (ZMod 2)),
      (∀ i j, M i j = M j i) → (∀ i, M i i = 0) →
      ∃ k : ℕ, Fintype.card W =
        Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * k by
    obtain ⟨k, hk⟩ := haux (Fintype.card V) V rfl (G.adjMatrix (ZMod 2))
      (fun i j => (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply j i)
      (G.isAdjMatrix_adjMatrix (ZMod 2)).apply_diag
    have hcast : (Fintype.card V : ℝ) =
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) +
        (2 : ℝ) * (k : ℝ) := by
      exact_mod_cast hk
    have hreal : (Fintype.card V : ℝ) -
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) =
        (2 : ℝ) * (k : ℝ) := by
      linarith
    have hhalf : (2 : ℝ) * (k : ℝ) / 2 = (k : ℝ) := by
      ring
    simp [hreal, hhalf]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ hcard M hsym hdiag
    by_cases hM : M = 0
    · refine ⟨0, ?_⟩
      rw [hM, Matrix.mulVecLin_zero, LinearMap.ker_zero,
        finrank_top, Module.finrank_fintype_fun_eq_card, mul_zero, add_zero]
    obtain ⟨a, b, hne⟩ : ∃ a b, M a b ≠ 0 := by
      by_contra h
      push_neg at h
      apply hM
      ext a b
      exact h a b
    have hab : a ≠ b := by
      intro h
      subst b
      exact hne (hdiag a)
    have hba : b ≠ a := Ne.symm hab
    have hval : (M a b).val = 1 := by
      have hlt := ZMod.val_lt (M a b)
      have hnz := (ZMod.val_ne_zero (M a b)).mpr hne
      omega
    have hc : M a b = 1 := by
      calc
        M a b = ((M a b).val : ZMod 2) :=
          (ZMod.natCast_zmod_val (M a b)).symm
        _ = 1 := by simp only [hval, Nat.cast_one]
    have hc' : M b a = 1 := (hsym b a).trans hc
    let Wa := {v : W // v ≠ a}
    let b' : Wa := ⟨b, hba⟩
    let U := {v : Wa // v ≠ b'}
    have hcarda : Fintype.card Wa + 1 = Fintype.card W := by
      simpa only [Fintype.card_option] using
        Fintype.card_congr (Equiv.optionSubtypeNe a)
    have hcardb : Fintype.card U + 1 = Fintype.card Wa := by
      simpa only [Fintype.card_option] using
        Fintype.card_congr (Equiv.optionSubtypeNe b')
    have hcards : Fintype.card U + 2 = Fintype.card W := by
      omega
    have hsum (f : W → ZMod 2) : (∑ v : W, f v) =
        f a + f b + ∑ t : U, f t.val.val := by
      rw [Fintype.sum_eq_add_sum_subtype_ne f a]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun v : Wa => f v.val) b']
      exact (add_assoc _ _ _).symm
    have hrow (x : W → ZMod 2) (v : W) : M.mulVecLin x v =
        M v a * x a + M v b * x b +
        ∑ t : U, M v t.val.val * x t.val.val := by
      change (∑ w : W, M v w * x w) = _
      exact hsum (fun w => M v w * x w)
    let B : Matrix U U (ZMod 2) := fun i j =>
      M i.val.val j.val.val +
      M i.val.val a * M b j.val.val +
      M i.val.val b * M a j.val.val
    have hsymB : ∀ i j, B i j = B j i := by
      intro i j
      dsimp only [B]
      rw [hsym i.val.val j.val.val, hsym i.val.val a,
        hsym b j.val.val, hsym i.val.val b, hsym a j.val.val]
      ring
    have hdiagB : ∀ i, B i i = 0 := by
      intro i
      change M i.val.val i.val.val +
        M i.val.val a * M b i.val.val +
        M i.val.val b * M a i.val.val = 0
      rw [hdiag i.val.val, hsym b i.val.val, hsym a i.val.val,
        zero_add, mul_comm (M i.val.val b) (M i.val.val a)]
      exact ZModModule.add_self _
    have brow (y : U → ZMod 2) (v : U) : B.mulVecLin y v =
        (∑ t : U, M v.val.val t.val.val * y t) +
        M v.val.val a * (∑ t : U, M b t.val.val * y t) +
        M v.val.val b * (∑ t : U, M a t.val.val * y t) := by
      change (∑ t : U,
        (M v.val.val t.val.val + M v.val.val a * M b t.val.val +
          M v.val.val b * M a t.val.val) * y t) = _
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    have xa (x : LinearMap.ker M.mulVecLin) : x.val a =
        ∑ t : U, M b t.val.val * x.val t.val.val := by
      have hx := congrFun (LinearMap.mem_ker.mp x.property) b
      change M.mulVecLin x.val b = 0 at hx
      rw [hrow] at hx
      simp only [hc', hdiag b, one_mul, zero_mul, add_zero] at hx
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using
        congrArg (fun z : ZMod 2 =>
          z + ∑ t : U, M b t.val.val * x.val t.val.val) hx
    have xb (x : LinearMap.ker M.mulVecLin) : x.val b =
        ∑ t : U, M a t.val.val * x.val t.val.val := by
      have hx := congrFun (LinearMap.mem_ker.mp x.property) a
      change M.mulVecLin x.val a = 0 at hx
      rw [hrow] at hx
      simp only [hdiag a, hc, zero_mul, one_mul, zero_add] at hx
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using
        congrArg (fun z : ZMod 2 =>
          z + ∑ t : U, M a t.val.val * x.val t.val.val) hx
    have hmem : ∀ x : LinearMap.ker M.mulVecLin,
        (fun t : U => x.val t.val.val) ∈ LinearMap.ker B.mulVecLin := by
      intro x
      rw [LinearMap.mem_ker]
      funext u
      change B.mulVecLin (fun t : U => x.val t.val.val) u = 0
      rw [brow, ← xa x, ← xb x]
      have hx := congrFun (LinearMap.mem_ker.mp x.property) u.val.val
      change M.mulVecLin x.val u.val.val = 0 at hx
      rw [hrow] at hx
      convert hx using 1 <;> ring
    let r0 : (W → ZMod 2) →ₗ[ZMod 2] (U → ZMod 2) :=
      LinearMap.funLeft (ZMod 2) (ZMod 2) (fun t : U => t.val.val)
    let r : LinearMap.ker M.mulVecLin →ₗ[ZMod 2] LinearMap.ker B.mulVecLin :=
      (r0.domRestrict (LinearMap.ker M.mulVecLin)).codRestrict
        (LinearMap.ker B.mulVecLin) hmem
    have hinj : Function.Injective r := by
      intro x y hxy
      have ht (t : U) : x.val t.val.val = y.val t.val.val := by
        have h := congrFun
          (congrArg (fun z : LinearMap.ker B.mulVecLin => z.val) hxy) t
        change x.val t.val.val = y.val t.val.val at h
        exact h
      apply Subtype.ext
      funext v
      by_cases hva : v = a
      · subst v
        rw [xa x, xa y]
        apply Finset.sum_congr rfl
        intro t _
        rw [ht t]
      · by_cases hvb : v = b
        · subst v
          rw [xb x, xb y]
          apply Finset.sum_congr rfl
          intro t _
          rw [ht t]
        · let t : U := ⟨⟨v, hva⟩, by
            intro h
            exact hvb (congrArg Subtype.val h)⟩
          exact ht t
    have hsurj : Function.Surjective r := by
      intro y
      let x : W → ZMod 2 := fun v =>
        if hva : v = a then ∑ t : U, M b t.val.val * y.val t
        else if hvb : v = b then ∑ t : U, M a t.val.val * y.val t
        else y.val ⟨⟨v, hva⟩, by
          intro h
          exact hvb (congrArg Subtype.val h)⟩
      have x_a : x a = ∑ t : U, M b t.val.val * y.val t := by
        simp [x]
      have x_b : x b = ∑ t : U, M a t.val.val * y.val t := by
        simp [x, hba]
      have x_u (t : U) : x t.val.val = y.val t := by
        have hta : t.val.val ≠ a := t.val.property
        have htb : t.val.val ≠ b := by
          intro h
          apply t.property
          exact Subtype.ext h
        simp [x, hta, htb]
      have hx : x ∈ LinearMap.ker M.mulVecLin := by
        rw [LinearMap.mem_ker]
        funext v
        change M.mulVecLin x v = 0
        rw [hrow]
        by_cases hva : v = a
        · subst v
          simp only [hdiag a, hc, zero_mul, one_mul, zero_add]
          rw [x_b]
          simp_rw [x_u]
          exact ZModModule.add_self _
        · by_cases hvb : v = b
          · subst v
            simp only [hc', hdiag b, one_mul, zero_mul, add_zero]
            rw [x_a]
            simp_rw [x_u]
            exact ZModModule.add_self _
          · let t : U := ⟨⟨v, hva⟩, by
              intro h
              exact hvb (congrArg Subtype.val h)⟩
            have hy := congrFun (LinearMap.mem_ker.mp y.property) t
            change B.mulVecLin y.val t = 0 at hy
            rw [brow] at hy
            change (∑ s : U, M v s.val.val * y.val s) +
              M v a * (∑ s : U, M b s.val.val * y.val s) +
              M v b * (∑ s : U, M a s.val.val * y.val s) = 0 at hy
            rw [x_a, x_b]
            simp_rw [x_u]
            convert hy using 1 <;> ring
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      funext t
      change x t.val.val = y.val t
      exact x_u t
    have hdim : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
        Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) :=
      (LinearEquiv.ofBijective r ⟨hinj, hsurj⟩).finrank_eq
    have hlt : Fintype.card U < n := by
      omega
    obtain ⟨k, hk⟩ := ih (Fintype.card U) hlt U rfl B hsymB hdiagB
    refine ⟨k + 1, ?_⟩
    rw [hdim]
    omega
theorem model_b3dcf100435ee5144e0c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (29999999 / 10000000 : ℝ)))) :
    (max ((2 : ℝ) * (G.maxDegree : ℝ)) (((Fintype.card V : ℝ) + (2 : ℝ)) - ((2 : ℝ) * (G.maxDegree : ℝ)))) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  sorry
