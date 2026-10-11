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

theorem parity_code_unique_neighbor_distance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 ≤ (cw.min' hcw : ℝ)
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hle : sw.min' hsw ≤ cw.min' hcw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [sw])
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
      have hxcode := (Finset.mem_filter.mp hx).2.2
      let S : Finset V := Finset.univ.filter (fun w => x w ≠ 0)
      have hSnonempty : S.Nonempty := by
        apply Finset.card_pos.mp
        change 0 < hammingNorm x
        exact hammingNorm_pos_iff.mpr hxne
      have hSstop : S ∈ stops := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hSnonempty, ?_⟩
        rintro ⟨v, w, hw, hvw, hu⟩
        have hxw : x w ≠ 0 := (Finset.mem_filter.mp hw).2
        have heq : ∑ a ∈ G.neighborFinset v, x a = x w := by
          apply Finset.sum_eq_single w
          · intro a ha hne
            by_contra hxa
            have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxa⟩
            exact hne (hu a haS ((G.mem_neighborFinset v a).mp ha))
          · intro hnot
            exact (hnot ((G.mem_neighborFinset v w).mpr hvw)).elim
        have hzero : ∑ a ∈ G.neighborFinset v, x a = 0 := by
          simpa [Matrix.mulVecLin_apply] using congrFun hxcode v
        exact hxw (heq.symm.trans hzero)
      apply Finset.min'_le
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨S, hSstop, rfl⟩))
  have hn : sw.min' hsw - 1 + 1 ≤ cw.min' hcw := by omega
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

theorem composed_98f6a5db9b7b63f3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  exact le_trans (parity_code_unique_neighbor_distance G) (hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e G)
theorem model_9507736b3513f2c06029 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) = ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) := by
  classical
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ A.mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change (cw.min' hcw : ℝ) = ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hcode : ∀ S ∈ stops, ∃ x : V → ZMod 2, x ≠ 0 ∧ A.mulVecLin x = 0 ∧ hammingNorm x ≤ S.card := by
    intro S hS
    have hs := (Finset.mem_filter.mp hS).2
    obtain ⟨t, ht⟩ := hs.1
    let c : G.Coloring (Fin 2) := h_guard.1.coloringTwo
    have sameColor : ∀ {v w u : V}, G.Adj v w → G.Adj v u → c w = c u := by
      intro v w u hvw hvu
      apply Fin.ext
      have hvw' : (c v).val ≠ (c w).val := fun h => c.valid hvw (Fin.ext h)
      have hvu' : (c v).val ≠ (c u).val := fun h => c.valid hvu (Fin.ext h)
      have hvlt := (c v).isLt
      have hwlt := (c w).isLt
      have hult := (c u).isLt
      omega
    let T : Finset V := S.filter (fun w => c w = c t)
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨ht, rfl⟩
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hTstop : ¬ (∃ v w, w ∈ T ∧ G.Adj v w ∧ ∀ u ∈ T, G.Adj v u → u = w) := by
      rintro ⟨v, w, hw, hvw, huniq⟩
      apply hs.2
      refine ⟨v, w, (Finset.mem_filter.mp hw).1, hvw, ?_⟩
      intro u hu hvu
      exact huniq u (Finset.mem_filter.mpr ⟨hu, (sameColor hvu hvw).trans (Finset.mem_filter.mp hw).2⟩) hvu
    let N : Finset V := Finset.univ.filter (fun v => ∃ w ∈ T, G.Adj v w)
    have hTN : Disjoint T N := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvN
      obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hvN).2
      exact c.valid hvw ((Finset.mem_filter.mp hvT).2.trans (Finset.mem_filter.mp hw).2.symm)
    let U : Finset V := T ∪ N
    let H : SimpleGraph ↥U := (G.between (T : Set V) (N : Set V)).induce (U : Set V)
    have hHacyc : H.IsAcyclic :=
      (SimpleGraph.IsAcyclic.anti
        (SimpleGraph.between_le (G := G) (s := (T : Set V)) (t := (N : Set V)))
        h_guard.1).induce (U : Set V)
    letI : Nonempty ↥U := ⟨⟨t, Finset.mem_union.mpr (Or.inl htT)⟩⟩
    obtain ⟨F, hHF, hFtop, hFT⟩ :=
      (SimpleGraph.connected_top (V := ↥U)).exists_isTree_le_of_le_of_isAcyclic
        (show H ≤ (⊤ : SimpleGraph ↥U) from le_top) hHacyc
    have hEF : H.edgeFinset.card ≤ F.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hHF)
    have hFTcard : F.edgeFinset.card + 1 = U.card := by
      simpa only [Fintype.card_coe] using hFT.card_edgeFinset
    have hHcard : H.edgeFinset.card < U.card := by omega
    let Tp : Finset ↥U := Finset.univ.filter (fun v => (v : V) ∈ T)
    let Np : Finset ↥U := Finset.univ.filter (fun v => (v : V) ∈ N)
    have hNpcard : Np.card = N.card := by
      refine Finset.card_bij (fun v _ => (v : V)) ?_ ?_ ?_
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
      · intro v hv w hw heq
        exact Subtype.ext heq
      · intro v hv
        refine ⟨⟨v, Finset.mem_union.mpr (Or.inr hv)⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    have hparts : H.IsBipartiteWith (Tp : Set ↥U) (Np : Set ↥U) := by
      refine ⟨?_, ?_⟩
      · apply Set.disjoint_left.mpr
        intro v hv hw
        exact Finset.disjoint_left.mp hTN (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
      · intro v w hvw
        change G.Adj (v : V) (w : V) ∧ (((v : V) ∈ T ∧ (w : V) ∈ N) ∨ ((v : V) ∈ N ∧ (w : V) ∈ T)) at hvw
        rcases hvw.2 with ⟨hvT, hwN⟩ | ⟨hvN, hwT⟩
        · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwN⟩⟩
        · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwT⟩⟩
    have hdegree : ∀ v ∈ Np, 2 ≤ H.degree v := by
      intro v hv
      have hvN : (v : V) ∈ N := (Finset.mem_filter.mp hv).2
      obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hvN).2
      have hsecond : ∃ u ∈ T, G.Adj (v : V) u ∧ u ≠ w := by
        by_contra hno
        apply hTstop
        refine ⟨(v : V), w, hw, hvw, ?_⟩
        intro u hu hvu
        by_contra hne
        exact hno ⟨u, hu, hvu, hne⟩
      obtain ⟨u, hu, hvu, hune⟩ := hsecond
      let ww : ↥U := ⟨w, Finset.mem_union.mpr (Or.inl hw)⟩
      let uu : ↥U := ⟨u, Finset.mem_union.mpr (Or.inl hu)⟩
      have hneq : ww ≠ uu := by
        intro heq
        exact hune (congrArg (fun z : ↥U => (z : V)) heq).symm
      have hww : ww ∈ H.neighborFinset v := by
        apply (H.mem_neighborFinset v ww).mpr
        exact ⟨hvw, Or.inr ⟨hvN, hw⟩⟩
      have huu : uu ∈ H.neighborFinset v := by
        apply (H.mem_neighborFinset v uu).mpr
        exact ⟨hvu, Or.inr ⟨hvN, hu⟩⟩
      have hpair : ({ww, uu} : Finset ↥U) ⊆ H.neighborFinset v := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hww
        · exact huu
      have hcard := Finset.card_le_card hpair
      simpa only [Finset.card_pair hneq, SimpleGraph.card_neighborFinset_eq_degree] using hcard
    have hsumEdges : 2 * Np.card ≤ H.edgeFinset.card := by
      rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hparts]
      calc
        2 * Np.card = ∑ v ∈ Np, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ Np, H.degree v := Finset.sum_le_sum hdegree
    have hUcard : U.card = T.card + N.card := Finset.card_union_of_disjoint hTN
    have hNT : N.card < T.card := by omega
    let M : Matrix ↥N ↥T (ZMod 2) := fun v w => A (v : V) (w : V)
    have hnoninj : ¬ Function.Injective M.mulVecLin := by
      intro hinj
      have hdim : T.card ≤ N.card := by
        simpa only [Module.finrank_pi, Fintype.card_coe] using
          (LinearMap.finrank_le_finrank_of_injective (f := M.mulVecLin) hinj)
      omega
    have hyexists : ∃ y : ↥T → ZMod 2, y ≠ 0 ∧ M.mulVecLin y = 0 := by
      by_contra hy
      apply hnoninj
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro y hyzero
      by_contra hyne
      exact hy ⟨y, hyne, hyzero⟩
    obtain ⟨y, hyne, hyker⟩ := hyexists
    let x : V → ZMod 2 := fun v => if hv : v ∈ T then y ⟨v, hv⟩ else 0
    have hxne : x ≠ 0 := by
      intro hx
      apply hyne
      funext w
      have hz := congrFun hx (w : V)
      simpa [x, w.property] using hz
    have hsumVector (v : V) : (A.mulVecLin x) v = ∑ w : ↥T, A v w * y w := by
      rw [Matrix.mulVecLin_apply]
      change (∑ w : V, A v w * x w) = ∑ w : ↥T, A v w * y w
      calc
        (∑ w : V, A v w * x w) = ∑ w ∈ T, A v w * x w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ T)
          intro w hw hwn
          simp [x, hwn]
        _ = ∑ w : ↥T, A v w * x w := (Finset.sum_coe_sort T (fun w => A v w * x w)).symm
        _ = ∑ w : ↥T, A v w * y w := by
          apply Finset.sum_congr rfl
          intro w hw
          simp [x, w.property]
    have hxker : A.mulVecLin x = 0 := by
      funext v
      rw [hsumVector v]
      by_cases hv : v ∈ N
      · have hz := congrFun hyker ⟨v, hv⟩
        change (∑ w : ↥T, A v w * y w) = 0 at hz
        exact hz
      · apply Finset.sum_eq_zero
        intro w hw
        have hnAdj : ¬ G.Adj v (w : V) := by
          intro hvw
          exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(w : V), w.property, hvw⟩⟩)
        simp [A, hnAdj]
    have hxwt : hammingNorm x ≤ T.card := by
      change (Finset.univ.filter (fun v => x v ≠ 0)).card ≤ T.card
      apply Finset.card_le_card
      intro v hv
      have hnv : x v ≠ 0 := (Finset.mem_filter.mp hv).2
      by_contra hvT
      exact hnv (by simp [x, hvT])
    exact ⟨x, hxne, hxker, hxwt.trans (Finset.card_le_card hTS)⟩
  have hle : cw.min' hcw ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [cw])
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨x, hxne, hxker, hxwt⟩ := hcode S hS
      have hmem : hammingNorm x ∈ cw :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩, rfl⟩))
      exact (Finset.min'_le cw _ hmem).trans hxwt
  have hupper : (cw.min' hcw : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 := by
    have hn : cw.min' hcw ≤ sw.min' hsw - 1 + 1 := by omega
    exact_mod_cast hn
  have hlower : ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 ≤ (cw.min' hcw : ℝ) :=
    parity_code_unique_neighbor_distance G
  exact le_antisymm hupper hlower
