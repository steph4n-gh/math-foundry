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

theorem model_fcf51e36faf8ebb9be9b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsAcyclic)) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  let H (s : Finset V) : SimpleGraph s := G.induce (s : Set V)
  let A (s : Finset V) : (s → ZMod 2) →ₗ[ZMod 2] (s → ZMod 2) :=
    (H s).adjMatrix (ZMod 2) |>.mulVecLin
  let K (s : Finset V) : Submodule (ZMod 2) (s → ZMod 2) := LinearMap.ker (A s)
  let E (s : Finset V) (x : s → ZMod 2) (v : V) : ZMod 2 :=
    if hv : v ∈ s then x ⟨v, hv⟩ else 0
  have hrow (s : Finset V) (x : s → ZMod 2) (v : s) :
      A s x v = ∑ w ∈ s, G.adjMatrix (ZMod 2) (v : V) w * E s x w := by
    change (∑ w : s, G.adjMatrix (ZMod 2) (v : V) (w : V) * x w) = _
    calc
      _ = ∑ w : s, G.adjMatrix (ZMod 2) (v : V) (w : V) * E s x (w : V) := by
        apply Finset.sum_congr rfl
        intro w hw
        simp [E, w.property]
      _ = _ := Finset.sum_coe_sort s
        (fun w => G.adjMatrix (ZMod 2) (v : V) w * E s x w)
  have aux : ∀ s : Finset V, ∃ r : Finset V,
      r ⊆ s ∧ G.IsIndepSet (r : Set V) ∧
        Module.finrank (ZMod 2) (K s) + s.card ≤ 2 * r.card := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih
    by_cases hnone : ∀ u v : s, ¬ (H s).Adj u v
    · refine ⟨s, (fun _ h => h), ?_, ?_⟩
      · intro u hu v hv huv
        exact hnone ⟨u, hu⟩ ⟨v, hv⟩
      · have hk : Module.finrank (ZMod 2) (K s) ≤ s.card := by
          calc
            _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
            _ = s.card := by
              simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
        omega
    · push_neg at hnone
      obtain ⟨u0, v0, h0⟩ := hnone
      letI : Nonempty s := ⟨u0⟩
      have hac : (H s).IsAcyclic := h_guard.induce (s : Set V)
      obtain ⟨u, v, p, hp, hmax⟩ :=
        SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (H s)
      have hlen : 1 ≤ p.length := by
        have hm := hmax u0 v0 h0.toWalk h0.isPath_toWalk
        simpa only [SimpleGraph.Adj.length_toWalk] using hm
      have hnil : ¬ p.Nil := by
        intro hn
        have hz := SimpleGraph.Walk.length_eq_zero_iff.mpr hn
        omega
      let b : s := p.snd
      have hab : (H s).Adj u b := p.adj_snd hnil
      have habG : G.Adj (u : V) (b : V) := hab
      have hleaf (w : s) (hw : (H s).Adj u w) : w = b := by
        apply hac.eq_snd_of_adj_start hp hw
        by_contra hn
        have hp' : (p.cons hw.symm).IsPath := hp.cons hn
        have hm := hmax w v (p.cons hw.symm) hp'
        simp only [SimpleGraph.Walk.length_cons] at hm
        omega
      have hub : (u : V) ≠ (b : V) := habG.ne
      let t : Finset V := (s.erase (u : V)).erase (b : V)
      have hts : t ⊆ s := by
        intro w hw
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2
      have hut : (u : V) ∉ t := by simp [t]
      have hbt : (b : V) ∉ t := by simp [t]
      have hlt : t ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hts, ?_⟩
        intro h
        exact hut (h.symm ▸ u.property)
      have hbmem : (b : V) ∈ s.erase (u : V) :=
        Finset.mem_erase.mpr ⟨hub.symm, b.property⟩
      have hcard : t.card + 2 = s.card := by
        have hc1 := Finset.card_erase_add_one u.property
        have hc2 := Finset.card_erase_add_one hbmem
        change t.card + 1 = (s.erase (u : V)).card at hc2
        omega
      have hno (w : V) (hw : w ∈ t) : ¬ G.Adj (u : V) w := by
        intro hadj
        have heq : w = (b : V) :=
          congrArg Subtype.val (hleaf ⟨w, hts hw⟩ hadj)
        exact hbt (heq ▸ hw)
      have hxb (x : K s) : x.1 b = 0 := by
        have hx := congrFun (LinearMap.mem_ker.mp x.property) u
        change (∑ w : s, G.adjMatrix (ZMod 2) (u : V) (w : V) * x.1 w) = 0 at hx
        have hs : (∑ w : s, G.adjMatrix (ZMod 2) (u : V) (w : V) * x.1 w) = x.1 b := by
          calc
            _ = G.adjMatrix (ZMod 2) (u : V) (b : V) * x.1 b := by
              apply Finset.sum_eq_single b
              · intro w hw hwb
                have hn : ¬ G.Adj (u : V) (w : V) := by
                  intro hadj
                  exact hwb (hleaf w hadj)
                simp [SimpleGraph.adjMatrix_apply, hn]
              · simp
            _ = x.1 b := by simp [SimpleGraph.adjMatrix_apply, habG]
        exact hs.symm.trans hx
      let R : (s → ZMod 2) →ₗ[ZMod 2] (t → ZMod 2) :=
        { toFun := fun x w => x ⟨(w : V), hts w.property⟩
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl }
      have hR (x : K s) : R x.1 ∈ K t := by
        change A t (R x.1) = 0
        funext w
        change A t (R x.1) w = 0
        let ws : s := ⟨(w : V), hts w.property⟩
        have hx : A s x.1 ws = 0 :=
          congrFun (LinearMap.mem_ker.mp x.property) ws
        calc
          _ = ∑ i ∈ t, G.adjMatrix (ZMod 2) (w : V) i * E t (R x.1) i :=
            hrow t (R x.1) w
          _ = ∑ i ∈ t, G.adjMatrix (ZMod 2) (w : V) i * E s x.1 i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [E, R, hi, hts hi]
          _ = ∑ i ∈ s, G.adjMatrix (ZMod 2) (w : V) i * E s x.1 i := by
            apply Finset.sum_subset hts
            intro i his hit
            have hrem : i = (u : V) ∨ i = (b : V) := by
              by_contra h
              have hiu : i ≠ (u : V) := fun hiu => h (Or.inl hiu)
              have hib : i ≠ (b : V) := fun hib => h (Or.inr hib)
              exact hit (Finset.mem_erase.mpr
                ⟨hib, Finset.mem_erase.mpr ⟨hiu, his⟩⟩)
            rcases hrem with rfl | rfl
            · have hn : ¬ G.Adj (w : V) (u : V) :=
                fun hadj => hno (w : V) w.property hadj.symm
              simp [SimpleGraph.adjMatrix_apply, hn]
            · simp [E, b.property, hxb x]
          _ = A s x.1 ws := (hrow s x.1 ws).symm
          _ = 0 := hx
      let f : K s →ₗ[ZMod 2] K t :=
        (R.domRestrict (K s)).codRestrict (K t) hR
      have hf : Function.Injective f := by
        intro x y hxy
        let z : K s := x - y
        have hzR : R z.1 = 0 := by
          have hxy' := congrArg (fun k : K t => (k : t → ZMod 2)) hxy
          change R x.1 = R y.1 at hxy'
          change R (x.1 - y.1) = 0
          rw [map_sub, hxy', sub_self]
        have hzval (w : s) (hwu : w ≠ u) : z.1 w = 0 := by
          by_cases hwb : w = b
          · subst w
            exact hxb z
          · have hiu : (w : V) ≠ (u : V) := fun h => hwu (Subtype.ext h)
            have hib : (w : V) ≠ (b : V) := fun h => hwb (Subtype.ext h)
            have hwt : (w : V) ∈ t :=
              Finset.mem_erase.mpr ⟨hib, Finset.mem_erase.mpr ⟨hiu, w.property⟩⟩
            have hh := congrFun hzR (⟨(w : V), hwt⟩ : t)
            change z.1 w = 0 at hh
            exact hh
        have hzrow := congrFun (LinearMap.mem_ker.mp z.property) b
        change (∑ w : s, G.adjMatrix (ZMod 2) (b : V) (w : V) * z.1 w) = 0 at hzrow
        have hs : (∑ w : s, G.adjMatrix (ZMod 2) (b : V) (w : V) * z.1 w) = z.1 u := by
          calc
            _ = G.adjMatrix (ZMod 2) (b : V) (u : V) * z.1 u := by
              apply Finset.sum_eq_single u
              · intro w hw hwu
                rw [hzval w hwu, mul_zero]
              · simp
            _ = z.1 u := by simp [SimpleGraph.adjMatrix_apply, habG.symm]
        have hzu : z.1 u = 0 := hs.symm.trans hzrow
        apply sub_eq_zero.mp
        apply Subtype.ext
        funext w
        change z.1 w = 0
        by_cases hwu : w = u
        · subst w
          exact hzu
        · exact hzval w hwu
      have hk : Module.finrank (ZMod 2) (K s) ≤ Module.finrank (ZMod 2) (K t) :=
        LinearMap.finrank_le_finrank_of_injective hf
      obtain ⟨r, hrs, hir, hdim⟩ := ih t hlt
      have hur : (u : V) ∉ r := fun hu => hut (hrs hu)
      refine ⟨insert (u : V) r, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact u.property
        · exact hts (hrs hw)
      · intro w hw z hz hwz hadj
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hadj.ne rfl
          · exact hno z (hrs hz) hadj
        · rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hno w (hrs hw) hadj.symm
          · exact hir hw hz hwz hadj
      · rw [Finset.card_insert_of_notMem hur]
        omega
  obtain ⟨r, hrs, hir, hdim⟩ := aux (Finset.univ : Finset V)
  have hr : r.card ≤ Gᶜ.cliqueNum := by
    simpa only [SimpleGraph.cliqueNum_compl] using hir.card_le_indepNum
  let B := (G.adjMatrix (ZMod 2)).mulVecLin
  let q : (V → ZMod 2) →ₗ[ZMod 2] (↥(Finset.univ : Finset V) → ZMod 2) :=
    { toFun := fun x v => x (v : V)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hq (x : LinearMap.ker B) : q x.1 ∈ K (Finset.univ : Finset V) := by
    change A (Finset.univ : Finset V) (q x.1) = 0
    funext v
    change A (Finset.univ : Finset V) (q x.1) v = 0
    have he : E (Finset.univ : Finset V) (q x.1) = x.1 := by
      funext w
      simp [E, q]
    rw [hrow, he]
    have hx := congrFun (LinearMap.mem_ker.mp x.property) (v : V)
    change (∑ w : V, G.adjMatrix (ZMod 2) (v : V) w * x.1 w) = 0 at hx
    exact hx
  let e : LinearMap.ker B →ₗ[ZMod 2] K (Finset.univ : Finset V) :=
    (q.domRestrict (LinearMap.ker B)).codRestrict (K (Finset.univ : Finset V)) hq
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    funext v
    have h := congrArg
      (fun k : K (Finset.univ : Finset V) => k.1 ⟨v, Finset.mem_univ v⟩) hxy
    change x.1 v = y.1 v at h
    exact h
  have hk : Module.finrank (ZMod 2) (LinearMap.ker B) ≤
      Module.finrank (ZMod 2) (K (Finset.univ : Finset V)) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hn : Module.finrank (ZMod 2) (LinearMap.ker B) + Fintype.card V ≤
      2 * Gᶜ.cliqueNum := by
    calc
      _ ≤ Module.finrank (ZMod 2) (K (Finset.univ : Finset V)) + Fintype.card V :=
        Nat.add_le_add_right hk _
      _ ≤ 2 * r.card := by simpa only [Finset.card_univ] using hdim
      _ ≤ 2 * Gᶜ.cliqueNum := Nat.mul_le_mul_left 2 hr
  have hnR : (Module.finrank (ZMod 2) (LinearMap.ker B) : ℝ) +
      (Fintype.card V : ℝ) ≤ (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) := by
    exact_mod_cast hn
  change (Module.finrank (ZMod 2) (LinearMap.ker B) : ℝ) ≤
    (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) - (Fintype.card V : ℝ)
  linarith only [hnR]

theorem model_4940d5883385d864ef0a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsAcyclic)) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (Fintype.card V : ℝ)) ≤ ((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) := by
  have h := model_fcf51e36faf8ebb9be9b G h_guard; linarith only [h]

theorem model_c36bd6bfd40d117b3da2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (((G.maxDegree : ℝ) + (1 : ℝ)) * (Gᶜ.cliqueNum : ℝ)) ≤ ((G.maxDegree : ℝ) * (Fintype.card V : ℝ)) := by
  classical
  have hmin : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := Nat.eq_zero_of_not_pos h
    rw [hz] at h_guard
    norm_num at h_guard
  have hn : ∀ v : V, ∃ w : V, G.Adj v w := by
    intro v
    exact (G.degree_pos_iff_exists_adj v).mp
      (lt_of_lt_of_le hmin (G.minDegree_le_degree v))
  choose f hf using hn
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  let t : Finset V := Finset.univ \ s
  have hft : ∀ v ∈ s, f v ∈ t := by
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hfv
    have hc : Gᶜ.Adj v (f v) := hs.isClique hv hfv (hf v).ne
    exact ((SimpleGraph.compl_adj G v (f v)).mp hc).2 (hf v)
  have hfiber : ∀ w ∈ t, (s.filter (fun v => f v = w)).card ≤ G.maxDegree := by
    intro w hw
    have hsub : s.filter (fun v => f v = w) ⊆ G.neighborFinset w := by
      intro v hv
      have heq : f v = w := (Finset.mem_filter.mp hv).2
      rw [G.mem_neighborFinset]
      simpa only [heq] using (hf v).symm
    calc
      (s.filter (fun v => f v = w)).card ≤ (G.neighborFinset w).card :=
        Finset.card_le_card hsub
      _ = G.degree w := G.card_neighborFinset_eq_degree w
      _ ≤ G.maxDegree := G.degree_le_maxDegree w
  have hcard : s.card ≤ t.card * G.maxDegree := by
    calc
      s.card = ∑ w ∈ t, (s.filter (fun v => f v = w)).card :=
        Finset.card_eq_sum_card_fiberwise hft
      _ ≤ ∑ _w ∈ t, G.maxDegree := Finset.sum_le_sum hfiber
      _ = t.card * G.maxDegree := by simp
  have hsum : t.card + s.card = Fintype.card V := by
    simpa only [t, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  have hnat : (G.maxDegree + 1) * Gᶜ.cliqueNum ≤
      G.maxDegree * Fintype.card V := by
    rw [← hs.card_eq, ← hsum]
    nlinarith [hcard]
  exact_mod_cast hnat

theorem model_256a48c23c065a850877 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((G.maxDegree : ℝ) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ (((G.maxDegree : ℝ) - (1 : ℝ)) * (Fintype.card V : ℝ)) := by
  classical
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := Nat.eq_zero_of_not_pos h
    have hh := h_guard.1
    rw [hz] at hh
    norm_num at hh
  obtain ⟨s, hs, hcard, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (Set.range A.col)
  let supp : (V → ZMod 2) → Finset V :=
    fun x => Finset.univ.filter (fun v => x v ≠ 0)
  have hcover : s.biUnion supp = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have hzero : ∀ x ∈ s, x v = 0 := by
      intro x hx
      by_contra hxv
      exact hv (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hxv⟩⟩)
    have hall : ∀ x ∈ Submodule.span (ZMod 2) (s : Set (V → ZMod 2)),
        x v = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hzero y hy
      | zero => rfl
      | add x y hx hy ihx ihy => simp [ihx, ihy]
      | smul a x hx ih => simp [ih]
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp
      (lt_of_lt_of_le hdeg (G.minDegree_le_degree v))
    have hmem : A.col w ∈ Submodule.span (ZMod 2) (s : Set (V → ZMod 2)) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self w)
    have hz := hall (A.col w) hmem
    change (if G.Adj v w then (1 : ZMod 2) else 0) = 0 at hz
    rw [if_pos hvw] at hz
    exact one_ne_zero hz
  have hsupp : ∀ x ∈ s, (supp x).card ≤ G.maxDegree := by
    intro x hx
    obtain ⟨w, rfl⟩ := hs hx
    calc
      (supp (A.col w)).card ≤ (G.neighborFinset w).card := by
        apply Finset.card_le_card
        intro v hv
        apply (G.mem_neighborFinset w v).mpr
        apply G.adj_symm
        by_contra h
        have hv' : A.col w v ≠ 0 := (Finset.mem_filter.mp hv).2
        apply hv'
        change (if G.Adj v w then (1 : ZMod 2) else 0) = 0
        exact if_neg h
      _ = G.degree w := G.card_neighborFinset_eq_degree w
      _ ≤ G.maxDegree := G.degree_le_maxDegree w
  have hbound : Fintype.card V ≤ s.card * G.maxDegree := by
    calc
      Fintype.card V = (s.biUnion supp).card := by
        rw [hcover, Finset.card_univ]
      _ ≤ s.card * G.maxDegree :=
        Finset.card_biUnion_le_card_mul s supp G.maxDegree hsupp
  have hnull : s.card + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
      Fintype.card V := by
    rw [hcard, ← Matrix.range_mulVecLin]
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hboundR : (Fintype.card V : ℝ) ≤ (s.card : ℝ) * (G.maxDegree : ℝ) := by
    exact_mod_cast hbound
  have hnullR : (s.card : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
      (Fintype.card V : ℝ) := by
    exact_mod_cast hnull
  change (G.maxDegree : ℝ) *
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) ≤
      ((G.maxDegree : ℝ) - 1) * (Fintype.card V : ℝ)
  nlinarith only [hboundR,
    congrArg (fun x : ℝ => (G.maxDegree : ℝ) * x) hnullR]

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
theorem model_6d91818f8f8347c7ef4c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((G.maxDegree : ℝ) + (1 : ℝ)) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ (((G.maxDegree : ℝ) - (1 : ℝ)) * (Fintype.card V : ℝ)) := by
  have checked_0 := model_fcf51e36faf8ebb9be9b G (by first | aesop | linarith); have checked_1 := model_4940d5883385d864ef0a G (by first | aesop | linarith); have checked_2 := model_c36bd6bfd40d117b3da2 G (by first | aesop | linarith); have checked_3 := model_256a48c23c065a850877 G (by first | aesop | linarith); have checked_4 := parity_code_dimension_le_order G; have checked_5 := model_86d5f85f179c31163952 G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]
