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

theorem model_8ce30216566f34c2605a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ)) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    let t : Finset V := Finset.univ \ s
    have hcover : G.edgeFinset ⊆ t.biUnion (fun v => G.incidenceFinset v) := by
      intro e
      refine Sym2.inductionOn e ?_
      intro v w he
      have hadj : G.Adj v w := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      by_cases hv : v ∈ s
      · have hw : w ∉ s := by
          intro hw
          exact ((SimpleGraph.compl_adj G v w).mp (hs.isClique hv hw hadj.ne)).2 hadj
        refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
        · simp [t, hw]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_right_iff] using hadj
      · refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
        · simp [t, hv]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_left_iff] using hadj
    have hn : G.edgeFinset.card ≤ t.card * G.maxDegree := by
      calc
        G.edgeFinset.card ≤ (t.biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ t, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ t, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ t, G.maxDegree :=
          Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
        _ = t.card * G.maxDegree := by simp
    have hcard : t.card + Gᶜ.cliqueNum = Fintype.card V := by
      simpa only [t, hs.card_eq, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcard_real : (t.card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have ht : (t.card : ℝ) = (Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ) := by
      linarith
    have hbound : (G.edgeFinset.card : ℝ) ≤ (t.card : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hn
    rw [ht] at hbound
    exact hbound

theorem hull3d_order_le_1_0_size_estrada_index_1_is_connected_982287c31193 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Fintype.card V : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  have h : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      h_guard.card_vert_le_card_edgeSet_add_one
  exact_mod_cast h

theorem model_255bb4d9cb35aa834f3d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.CliqueFree 3)) :
    (G.edgeFinset.card : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ))) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    have hi : G.IsIndepSet (s : Set V) := (G.isClique_compl).mp hs.isClique
    have hdeg : ∀ v : V, G.degree v ≤ Gᶜ.cliqueNum := by
      intro v
      have hn : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
        rw [G.isClique_compl, G.coe_neighborFinset]
        exact G.isIndepSet_neighborSet_of_triangleFree h_guard v
      exact hn.card_le_cliqueNum
    have hcover : G.edgeFinset ⊆ (sᶜ).biUnion (fun v => G.incidenceFinset v) := by
      intro e he
      have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨v, hv, hve⟩ :=
        SimpleGraph.IsIndepSet.nonempty_mem_compl_mem_edge G hi he'
      refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_compl.mpr hv, ?_⟩
      exact SimpleGraph.mem_incidenceFinset.mpr ⟨he', hve⟩
    have hnat : G.edgeFinset.card ≤ (sᶜ).card * Gᶜ.cliqueNum := by
      calc
        G.edgeFinset.card ≤ ((sᶜ).biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ sᶜ, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ sᶜ, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ sᶜ, Gᶜ.cliqueNum := Finset.sum_le_sum (fun v _ => hdeg v)
        _ = (sᶜ).card * Gᶜ.cliqueNum := by simp
    have hc : ((sᶜ).card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      have hn := Finset.card_compl_add_card s
      rw [hs.card_eq] at hn
      exact_mod_cast hn
    calc
      (G.edgeFinset.card : ℝ) ≤ ((sᶜ).card : ℝ) * (Gᶜ.cliqueNum : ℝ) := by
        exact_mod_cast hnat
      _ = (Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) := by
        rw [← hc]
        ring

theorem model_9d72068d4e2555d140e4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (G.edgeFinset.card : ℝ)) ≤ (Fintype.card V : ℝ) := by
  classical
  have hrow :
      ∀ (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj]
        (S : Set W) [DecidablePred (fun w => w ∈ S)]
        (x : W → ZMod 2) (z : S),
        (∀ w : W, w ∉ S → H.adjMatrix (ZMod 2) (z : W) w * x w = 0) →
        ((H.induce S).adjMatrix (ZMod 2)).mulVecLin (fun w : S => x (w : W)) z =
          (H.adjMatrix (ZMod 2)).mulVecLin x (z : W) := by
    intro W _ _ H _ S _ x z hz
    change (∑ w : S, (H.induce S).adjMatrix (ZMod 2) z w * x (w : W)) =
      ∑ w : W, H.adjMatrix (ZMod 2) (z : W) w * x w
    symm
    apply Finset.sum_congr_set S
    · intro w hw
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.induce_adj]
    · exact hz
  have haux :
      ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        Fintype.card W = n → H.IsAcyclic → (∀ w, H.degree w ≤ 2) →
        Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) +
          H.edgeFinset.card ≤ Fintype.card W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H _ hcard hac hdeg
      by_cases hadj : ∃ a b : W, H.Adj a b
      · obtain ⟨a, b, hab⟩ := hadj
        letI : Nonempty W := ⟨a⟩
        obtain ⟨u, z, p, hp, hmax⟩ :=
          SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
        have hnil : ¬ p.Nil := by
          intro hn
          have hh := hmax a b (SimpleGraph.Walk.cons hab .nil) (by simp [hab.ne])
          have hzero : p.length = 0 := hn.length_eq_zero
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hzero] at hh
          omega
        let v : W := p.snd
        have huv : H.Adj u v := p.adj_snd hnil
        have hleaf (w : W) (hw : H.Adj u w) : w = v := by
          apply hac.eq_snd_of_adj_start hp hw
          by_contra hnot
          have hpath : (p.cons hw.symm).IsPath := hp.cons hnot
          have hh := hmax w z (p.cons hw.symm) hpath
          simp only [SimpleGraph.Walk.length_cons] at hh
          omega
        have hnu : H.neighborFinset u = {v} := by
          ext w
          constructor
          · intro hw
            exact Finset.mem_singleton.mpr
              (hleaf w ((H.mem_neighborFinset u w).mp hw))
          · intro hw
            have hwv : w = v := Finset.mem_singleton.mp hw
            rw [hwv]
            exact (H.mem_neighborFinset u v).mpr huv
        let W1 := ↥(({v} : Set W)ᶜ)
        let H1 : SimpleGraph W1 := H.induce ({v} : Set W)ᶜ
        let u1 : W1 := ⟨u, by simpa using huv.ne⟩
        let W2 := ↥(({u1} : Set W1)ᶜ)
        let H2 : SimpleGraph W2 := H1.induce ({u1} : Set W1)ᶜ
        have hnone (w : W1) : ¬ H1.Adj u1 w := by
          intro hw
          have heq : (w : W) = v := hleaf (w : W) hw
          exact w.property (Set.mem_singleton_iff.mpr heq)
        have hu1deg : H1.degree u1 = 0 := by
          rw [← H1.card_neighborFinset_eq_degree u1]
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          exact hnone w ((H1.mem_neighborFinset u1 w).mp hw)
        have hc1 : Fintype.card W1 = Fintype.card W - 1 := by
          dsimp only [W1]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hc2 : Fintype.card W2 = Fintype.card W1 - 1 := by
          dsimp only [W2]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos1 : 0 < Fintype.card W1 := Fintype.card_pos_iff.mpr ⟨u1⟩
        have hcards : Fintype.card W2 + 2 = Fintype.card W := by omega
        have hlt : Fintype.card W2 < n := by omega
        let K := LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin
        let K2 := LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin
        have hxv (x : K) : (x : W → ZMod 2) v = 0 := by
          have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
            x.property
          have hh := congrFun hxA u
          simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
            hnu, Finset.sum_singleton, Pi.zero_apply] using hh
        have hres (x : K) :
            (H2.adjMatrix (ZMod 2)).mulVecLin
              (fun w : W2 => (x : W → ZMod 2) w.val.val) = 0 := by
          funext w
          have hz1 (j : W) (hj : j ∉ ({v} : Set W)ᶜ) :
              H.adjMatrix (ZMod 2) w.val.val j * (x : W → ZMod 2) j = 0 := by
            have heq : j = v := by simpa using hj
            subst j
            rw [hxv x, mul_zero]
          have hz2 (j : W1) (hj : j ∉ ({u1} : Set W1)ᶜ) :
              H1.adjMatrix (ZMod 2) w.val j * (x : W → ZMod 2) j.val = 0 := by
            have heq : j = u1 := by simpa using hj
            subst j
            have hn : ¬ H1.Adj w.val u1 := fun h => hnone w.val h.symm
            change (if H1.Adj w.val u1 then (1 : ZMod 2) else 0) *
              (x : W → ZMod 2) (u1 : W) = 0
            rw [if_neg hn, zero_mul]
          calc
            (H2.adjMatrix (ZMod 2)).mulVecLin
                (fun j : W2 => (x : W → ZMod 2) j.val.val) w =
                (H1.adjMatrix (ZMod 2)).mulVecLin
                  (fun j : W1 => (x : W → ZMod 2) j.val) w.val :=
              hrow W1 H1 ({u1} : Set W1)ᶜ
                (fun j : W1 => (x : W → ZMod 2) j.val) w hz2
            _ = (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) w.val.val :=
              hrow W H ({v} : Set W)ᶜ (x : W → ZMod 2) w.val hz1
            _ = 0 := congrFun
              (show (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 from
                x.property) w.val.val
        let R : K →ₗ[ZMod 2] K2 :=
          { toFun := fun x => ⟨fun w => (x : W → ZMod 2) w.val.val, hres x⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              rfl
            map_smul' := by
              intro c x
              apply Subtype.ext
              rfl }
        have hRinj : Function.Injective R := by
          have hzero (x : K) (hx : R x = 0) : x = 0 := by
            have hrest (j : W) (hju : j ≠ u) (hjv : j ≠ v) :
                (x : W → ZMod 2) j = 0 := by
              let j1 : W1 := ⟨j, by simpa using hjv⟩
              let j2 : W2 := ⟨j1, by
                change j1 ≠ u1
                intro heq
                exact hju (congrArg (fun t : W1 => (t : W)) heq)⟩
              have hh := congrArg (fun t : K2 => (t : W2 → ZMod 2) j2) hx
              change (x : W → ZMod 2) j = 0 at hh
              exact hh
            have hxu : (x : W → ZMod 2) u = 0 := by
              have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
                x.property
              have hr : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) v =
                  (x : W → ZMod 2) u := by
                rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
                apply Finset.sum_eq_single u
                · intro j hj hju
                  by_cases hjv : j = v
                  · simpa only [hjv] using hxv x
                  · exact hrest j hju hjv
                · intro hnot
                  exact (hnot ((H.mem_neighborFinset v u).mpr huv.symm)).elim
              exact hr.symm.trans (congrFun hxA v)
            apply Subtype.ext
            funext j
            change (x : W → ZMod 2) j = 0
            by_cases hju : j = u
            · simpa only [hju] using hxu
            by_cases hjv : j = v
            · simpa only [hjv] using hxv x
            exact hrest j hju hjv
          intro x y hxy
          apply sub_eq_zero.mp
          apply hzero
          rw [map_sub, hxy, sub_self]
        have hdim : Module.finrank (ZMod 2) K ≤ Module.finrank (ZMod 2) K2 :=
          LinearMap.finrank_le_finrank_of_injective hRinj
        change Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) ≤
          Module.finrank (ZMod 2) (LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin) at hdim
        have hdeg2 (w : W2) : H2.degree w ≤ 2 := by
          calc
            H2.degree w ≤ H1.degree w.val :=
              (SimpleGraph.Copy.induce H1 ({u1} : Set W1)ᶜ).degree_le w
            _ ≤ H.degree w.val.val :=
              (SimpleGraph.Copy.induce H ({v} : Set W)ᶜ).degree_le w.val
            _ ≤ 2 := hdeg w.val.val
        have hI := ih (Fintype.card W2) hlt W2 H2 rfl
          ((hac.induce ({v} : Set W)ᶜ).induce ({u1} : Set W1)ᶜ) hdeg2
        have hm1 : H1.edgeFinset.card = H.edgeFinset.card - H.degree v := by
          dsimp only [H1]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet]
        have hm2 : H2.edgeFinset.card = H1.edgeFinset.card := by
          dsimp only [H2]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet, hu1deg, Nat.sub_zero]
        have hdv := hdeg v
        have hem := H.degree_le_card_edgeFinset v
        omega
      · have hbot : H = ⊥ := by
          apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
          intro a b hab
          exact hadj ⟨a, b, hab⟩
        have hm : H.edgeFinset.card = 0 := by simp [hbot]
        rw [hm, Nat.add_zero]
        calc
          _ ≤ Module.finrank (ZMod 2) (W → ZMod 2) := Submodule.finrank_le _
          _ = Fintype.card W := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hmax : G.maxDegree ≤ 2 := by
    by_contra h
    have hh : 3 ≤ G.maxDegree := by omega
    have hhR : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hh
    linarith only [h_guard.2.1, hhR]
  have h := haux (Fintype.card V) V G rfl h_guard.1
    (fun v => (G.degree_le_maxDegree v).trans hmax)
  exact_mod_cast h

theorem model_fadaed797ff612bf4d71 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.CliqueFree 3)) :
    (G.edgeFinset.card : ℝ) ≤ ((G.maxDegree : ℝ) * ((Fintype.card V : ℝ) - (G.maxDegree : ℝ))) := by
  classical
  have hmax : G.maxDegree ≤ Gᶜ.cliqueNum := by
    refine G.maxDegree_le_of_forall_degree_le _ ?_
    intro v
    have hn : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
      rw [G.isClique_compl, G.coe_neighborFinset]
      exact G.isIndepSet_neighborSet_of_triangleFree h_guard v
    exact hn.card_le_cliqueNum
  have hmax_real : (G.maxDegree : ℝ) ≤ (Gᶜ.cliqueNum : ℝ) := by
    exact_mod_cast hmax
  calc
    (G.edgeFinset.card : ℝ) ≤
        ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ) :=
      model_8ce30216566f34c2605a G
    _ ≤ ((Fintype.card V : ℝ) - (G.maxDegree : ℝ)) * (G.maxDegree : ℝ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hmax_real _) (Nat.cast_nonneg _)
    _ = (G.maxDegree : ℝ) * ((Fintype.card V : ℝ) - (G.maxDegree : ℝ)) :=
      mul_comm _ _

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

theorem model_8507aba979de2b196665 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Int.floor (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ))) : ℝ) = (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) := by
  have h := model_7f80b6911ecd9dc4c880 G
  linarith only [h]

theorem model_c0b68b8f55a47e0a3735 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) := by
  classical
  let A := G.adjMatrix (ZMod 2)
  let r := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A.col))
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range A.col)
  choose a ha using hf
  have hspan' : Submodule.span (ZMod 2) (Set.range (A.col ∘ a)) =
      Submodule.span (ZMod 2) (Set.range A.col) := by
    have hfun : A.col ∘ a = f := by
      funext i
      exact ha i
    rw [hfun]
    exact hspan
  let T : Finset V := Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
  have hz : ∀ v : V, v ∉ T → G.degree v = 0 := by
    intro v hv
    have hbase (i : Fin r) : A.col (a i) v = 0 := by
      have hnot : ¬ G.Adj v (a i) := by
        intro h
        apply hv
        change v ∈ Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, (G.mem_neighborFinset (a i) v).mpr h.symm⟩
      simp [Matrix.col_apply, A, hnot]
    have hzero : ∀ x ∈ Submodule.span (ZMod 2) (Set.range (A.col ∘ a)), x v = 0 := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x v = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        exact hbase i
      · rfl
      · intro x y _ _ hx hy
        change x v + y v = 0
        rw [hx, hy, add_zero]
      · intro b x _ hx
        change b * x v = 0
        rw [hx, mul_zero]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hpos
    have hwzero : A.col w v = 0 := hzero (A.col w) (by
      rw [hspan']
      exact Submodule.subset_span ⟨w, rfl⟩)
    simpa [Matrix.col_apply, A, hw] using hwzero
  have hT : T.card ≤ r * G.maxDegree := by
    calc
      T.card ≤ ∑ i : Fin r, (G.neighborFinset (a i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin r, G.maxDegree := Finset.sum_le_sum (fun i _ => by
        simpa only [G.card_neighborFinset_eq_degree] using G.degree_le_maxDegree (a i))
      _ = r * G.maxDegree := by simp
  have he : 2 * G.edgeFinset.card ≤ r * G.maxDegree ^ 2 := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ v ∈ T, G.degree v := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro v _ hv
        exact hz v hv
      _ ≤ ∑ _v ∈ T, G.maxDegree :=
        Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
      _ = T.card * G.maxDegree := by simp
      _ ≤ (r * G.maxDegree) * G.maxDegree := Nat.mul_le_mul_right _ hT
      _ = r * G.maxDegree ^ 2 := by ring
  have hr : r + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = Fintype.card V := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at h
    exact h
  have hrreal : (r : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
      (Fintype.card V : ℝ) := by
    exact_mod_cast hr
  have hrsub : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) = (r : ℝ) := by
    linarith
  change (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
    ((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ)) *
      (G.maxDegree : ℝ) ^ 2
  rw [hrsub]
  exact_mod_cast he

theorem model_92bb8eaf5887bd185218 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((G.edgeFinset.card : ℝ) / ((G.maxDegree : ℝ) ^ 2))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  have hD : (0 : ℝ) < (G.maxDegree : ℝ) := by
    linarith only [h_guard.1]
  have hD2 : (0 : ℝ) < (G.maxDegree : ℝ) ^ 2 := by
    positivity
  let k : ℤ := Int.floor
    (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2)
        (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / 2)
  have hk : (k : ℝ) =
      ((Fintype.card V : ℝ) -
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / 2 := by
    exact model_8507aba979de2b196665 G
  have hedge := model_c0b68b8f55a47e0a3735 G
  have hratio : (G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2 ≤
      (k : ℝ) := by
    apply (div_le_iff₀ hD2).2
    rw [hk]
    nlinarith only [hedge]
  have hceil : Int.ceil
      ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2) ≤ k :=
    Int.ceil_le.mpr hratio
  have hceilR :
      (Int.ceil ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2) : ℝ) ≤
        (k : ℝ) := by
    exact_mod_cast hceil
  linarith only [hk, hceilR]
theorem model_61856b7405177b7972cd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) ≥ ((4 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · have he : G.edgeFinset.card = 0 := by
      simpa [hn] using G.card_edgeFinset_le_card_choose_two
    simp [hn, he]
  · rw [if_neg hn]
    let A : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
    have hA : A.IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := A.toEuclideanLin
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) := hA.eigenvectorBasis
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
    let q : ℝ := sSup (Set.range hA.eigenvalues)
    have hTsym : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    have hTb (i : V) : T (b i) = hA.eigenvalues i • b i := by
      apply PiLp.ext
      intro v
      change (Matrix.mulVec A ⇑(hA.eigenvectorBasis i)) v =
        hA.eigenvalues i * (hA.eigenvectorBasis i) v
      exact congrFun (hA.mulVec_eigenvectorBasis i) v
    have hEig (i : V) : hA.eigenvalues i ≤ q := by
      exact le_csSup (Set.finite_range hA.eigenvalues).bddAbove ⟨i, rfl⟩
    have hxx : inner ℝ x x = (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ _v : V, (1 : ℝ) * 1) = (Fintype.card V : ℝ)
      simp
    have hmass : (∑ i : V, (inner ℝ (b i) x) ^ 2) =
        (Fintype.card V : ℝ) := by
      rw [b.sum_sq_inner_right x, ← real_inner_self_eq_norm_sq x, hxx]
    have hquad : inner ℝ x (T x) =
        ∑ i : V, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner x (T x)]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hTsym (b i) x, hTb i, real_inner_smul_left]
      simp only [real_inner_comm (b i) x]
      ring
    have hTx (v : V) : (T x) v = (2 : ℝ) * (G.degree v : ℝ) := by
      change (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ)
        (fun _ : V => (1 : ℝ))) v = _
      rw [Matrix.add_mulVec, Pi.add_apply, G.degMatrix_mulVec_apply,
        G.adjMatrix_mulVec_apply]
      simp [two_mul]
    have hdeg : (∑ v : V, (G.degree v : ℝ)) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hvalue : inner ℝ x (T x) =
        (4 : ℝ) * (G.edgeFinset.card : ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change (∑ v : V, (T x) v * (1 : ℝ)) = _
      simp only [mul_one, hTx]
      rw [← Finset.mul_sum, hdeg]
      ring
    have hbound : (4 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        q * (Fintype.card V : ℝ) := by
      calc
        (4 : ℝ) * (G.edgeFinset.card : ℝ) = inner ℝ x (T x) := hvalue.symm
        _ = ∑ i : V, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2 := hquad
        _ ≤ ∑ i : V, q * (inner ℝ (b i) x) ^ 2 :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_right (hEig i) (sq_nonneg _))
        _ = q * (Fintype.card V : ℝ) := by
          rw [← Finset.mul_sum, hmass]
    change (Fintype.card V : ℝ) * q ≥ (4 : ℝ) * (G.edgeFinset.card : ℝ)
    simpa only [mul_comm] using hbound
