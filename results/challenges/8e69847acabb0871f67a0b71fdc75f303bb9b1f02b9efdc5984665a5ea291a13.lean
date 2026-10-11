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
theorem model_6a99e9dbd16d921e7d7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (29999999 / 10000000 : ℝ)))) :
    (((Fintype.card V : ℝ) / (2 : ℝ)) + (1 : ℝ)) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  sorry
