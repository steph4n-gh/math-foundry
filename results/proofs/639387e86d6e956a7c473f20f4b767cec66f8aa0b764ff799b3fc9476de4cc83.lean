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

theorem hull3d_parity_code_distance_ge_1_0_unique_neighbor_radius_min_degree_1_is_regular_42ada867cd60 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) := by
  have h := parity_code_unique_neighbor_distance G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem model_ae22b995b67aeeffd271 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) = ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) := by
  classical
  have hdeg : G.maxDegree ≤ 2 := by
    have hlt : (G.maxDegree : ℝ) < (3 : ℝ) :=
      lt_of_le_of_lt h_guard.1 (by norm_num)
    have hn : G.maxDegree < 3 := by exact_mod_cast hlt
    omega
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hreverse : cw.min' hcw ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [cw])
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      have hS' := (Finset.mem_filter.mp hS).2
      let x : V → ZMod 2 := fun w => if w ∈ S then 1 else 0
      have hweight : hammingNorm x = S.card := by
        unfold hammingNorm
        apply congrArg Finset.card
        ext w
        by_cases hw : w ∈ S <;> simp [x, hw]
      have hxne : x ≠ 0 := by
        apply hammingNorm_pos_iff.mp
        rw [hweight]
        exact hS'.1.card_pos
      have hxker : (G.adjMatrix (ZMod 2)).mulVecLin x = 0 := by
        funext v
        let T : Finset V := (G.neighborFinset v).filter (fun w => w ∈ S)
        have hTle : T.card ≤ 2 := calc
          T.card ≤ (G.neighborFinset v).card := Finset.card_filter_le _ _
          _ = G.degree v := G.card_neighborFinset_eq_degree v
          _ ≤ G.maxDegree := G.degree_le_maxDegree v
          _ ≤ 2 := hdeg
        have hTne : T.card ≠ 1 := by
          intro hT
          obtain ⟨w, hw, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hT
          have hwN : w ∈ G.neighborFinset v := (Finset.mem_filter.mp hw).1
          have hwS : w ∈ S := (Finset.mem_filter.mp hw).2
          apply hS'.2
          refine ⟨v, w, hwS, (G.mem_neighborFinset v w).mp hwN, ?_⟩
          intro u hu hvu
          exact huniq u (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v u).mpr hvu, hu⟩)
        have hTcases : T.card = 0 ∨ T.card = 2 := by omega
        rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
        change (∑ u ∈ G.neighborFinset v, if u ∈ S then (1 : ZMod 2) else 0) = 0
        rw [Finset.sum_boole]
        change (T.card : ZMod 2) = 0
        rcases hTcases with hT | hT
        · simp only [hT, Nat.cast_zero]
        · simpa only [hT] using (ZMod.natCast_self 2)
      have hmem : hammingNorm x ∈ cw := by
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨x, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩
      have hmin := Finset.min'_le cw (hammingNorm x) hmem
      simpa only [hweight] using hmin
  change (cw.min' hcw : ℝ) = ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  apply le_antisymm
  · have hn : cw.min' hcw ≤ sw.min' hsw - 1 + 1 := by omega
    exact_mod_cast hn
  · exact parity_code_unique_neighbor_distance G

theorem model_0619a96c0eebea1f3be2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ (|(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) + (((1 : ℝ) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * ((G.minDegree : ℝ) - (2 : ℝ)))) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  let dist : ℕ := cw.min' hcw
  let s : ℕ := sw.min' hsw
  let d : ℕ := G.minDegree
  let r : ℝ := ((s - 1 : ℕ) : ℝ) + 1
  change (dist : ℝ) ≥ r + (1 - ((d : ℝ) - 2 * (Int.floor ((d : ℝ) / 2) : ℝ))) * ((d : ℝ) - 2)
  have hbase : r ≤ (dist : ℝ) := parity_code_unique_neighbor_distance G
  have hpos : 1 ≤ s := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have haeq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hr : r = (s : ℝ) := by
    change ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ)
    have hn : s - 1 + 1 = s := by omega
    exact_mod_cast hn
  have hd : 2 ≤ d := by
    have hreal : (1 : ℝ) < (d : ℝ) :=
      lt_of_lt_of_le (by norm_num) h_guard.2.2.1
    have hn : 1 < d := by exact_mod_cast hreal
    omega
  rcases Nat.even_or_odd d with he | ho
  · have hcast : (d : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr he
    obtain ⟨k, hk⟩ := he
    have hkreal : (d : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hdiv : (d : ℝ) / 2 = (k : ℝ) := by linarith only [hkreal]
    have hf : Int.floor ((d : ℝ) / 2) = (k : ℤ) := by
      rw [hdiv, Int.floor_natCast]
    have hcoef : (d : ℝ) - 2 * (Int.floor ((d : ℝ) / 2) : ℝ) = 0 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    have hdim : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) = 2 := by
      have habs := abs_le.mp h_guard.2.2.2
      have hlo : (1 : ℝ) < (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) := by
        linarith only [habs.1]
      have hhi : (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) < 3 := by
        linarith only [habs.2]
      have hlo' : 1 < Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) := by
        exact_mod_cast hlo
      have hhi' : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) < 3 := by
        exact_mod_cast hhi
      omega
    have hV : Nonempty V := by
      by_contra h
      letI : IsEmpty V := not_nonempty_iff.mp h
      have hz : d = 0 := by simp [d]
      omega
    obtain ⟨v₀⟩ := hV
    letI : Nonempty V := ⟨v₀⟩
    obtain ⟨q, hq⟩ := h_guard.2.1
    have hreg : G.IsRegularOfDegree d := by
      have heq : d = q := hq.minDegree_eq
      rw [heq]
      exact hq
    have hdegree : ∀ v : V, 0 < G.degree v := by
      intro v
      rw [hreg.degree_eq v]
      omega
    let C : G.Coloring (Fin 2) := Classical.choice h_guard.1
    have sameColor : ∀ {v w u : V}, G.Adj v w → G.Adj v u → C w = C u := by
      intro v w u hvw hvu
      apply Fin.ext
      have hvw' : (C v).val ≠ (C w).val := fun h => C.valid hvw (Fin.ext h)
      have hvu' : (C v).val ≠ (C u).val := fun h => C.valid hvu (Fin.ext h)
      have hvlt := (C v).isLt
      have hwlt := (C w).isLt
      have hult := (C u).isLt
      omega
    obtain ⟨v₁, h01⟩ := (G.degree_pos_iff_exists_adj v₀).mp (hdegree v₀)
    have hcsurj : Function.Surjective C := by
      intro i
      by_cases hi : i = C v₀
      · exact ⟨v₀, hi.symm⟩
      · refine ⟨v₁, ?_⟩
        apply Fin.ext
        have h01' : (C v₀).val ≠ (C v₁).val := fun h => C.valid h01 (Fin.ext h)
        have hi' : i.val ≠ (C v₀).val := fun h => hi (Fin.ext h)
        have hiLt := i.isLt
        have h0Lt := (C v₀).isLt
        have h1Lt := (C v₁).isLt
        omega
    have hker : ∀ z : Fin 2 → ZMod 2, (G.adjMatrix (ZMod 2)).mulVecLin (fun v => z (C v)) = 0 := by
      intro z
      funext v
      rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
      obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (hdegree v)
      calc
        (∑ u ∈ G.neighborFinset v, z (C u)) = ∑ u ∈ G.neighborFinset v, z (C w) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact congrArg z (sameColor ((G.mem_neighborFinset v u).mp hu) hvw)
        _ = (d : ZMod 2) * z (C w) := by
          rw [Finset.sum_const, G.card_neighborFinset_eq_degree v, hreg.degree_eq v, nsmul_eq_mul]
        _ = 0 := by rw [hcast, zero_mul]
    let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    let f : (Fin 2 → ZMod 2) → K := fun z =>
      ⟨fun v => z (C v), LinearMap.mem_ker.mpr (hker z)⟩
    have hfinj : Function.Injective f := by
      intro z z' h
      funext i
      obtain ⟨v, hv⟩ := hcsurj i
      have hval := congrFun (congrArg (fun y : K => (y : V → ZMod 2)) h) v
      change z (C v) = z' (C v) at hval
      simpa only [hv] using hval
    have hKcard : Fintype.card K = 4 := by
      calc
        Fintype.card K = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) K :=
          Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
        _ = 4 := by
          rw [ZMod.card, show Module.finrank (ZMod 2) K = 2 from hdim]
          norm_num
    have hfcard : Fintype.card (Fin 2 → ZMod 2) = Fintype.card K := by
      rw [hKcard]
      norm_num [Fintype.card_fun, ZMod.card]
    have hfsurj : Function.Surjective f :=
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hfcard⟩).2
    have hclass : ∀ i : Fin 2, s + d ≤ ((Finset.univ : Finset V).filter (fun v => C v = i)).card + 2 := by
      intro i
      let T : Finset V := Finset.univ.filter (fun v => C v = i)
      change s + d ≤ T.card + 2
      obtain ⟨w, hw⟩ := hcsurj i
      obtain ⟨v, hwv⟩ := (G.degree_pos_iff_exists_adj w).mp (hdegree w)
      have hvw : G.Adj v w := hwv.symm
      have hnT : G.neighborFinset v ⊆ T := by
        intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (sameColor ((G.mem_neighborFinset v u).mp hu) hvw).trans hw⟩
      have hdT : d ≤ T.card := by
        calc
          d = G.degree v := (hreg.degree_eq v).symm
          _ = (G.neighborFinset v).card := (G.card_neighborFinset_eq_degree v).symm
          _ ≤ T.card := Finset.card_le_card hnT
      obtain ⟨D, hDT, hDcard⟩ := Finset.exists_subset_card_eq (show d - 2 ≤ T.card by omega)
      let S : Finset V := T \ D
      have hScard : S.card = T.card - (d - 2) := by
        change (T \ D).card = T.card - (d - 2)
        rw [Finset.card_sdiff_of_subset hDT, hDcard]
      have hSnonempty : S.Nonempty := by
        apply Finset.card_pos.mp
        omega
      have hSstop : S ∈ stops := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hSnonempty, ?_⟩
        rintro ⟨v', w', hwS, hvw', huniq⟩
        have hwT : w' ∈ T := (Finset.mem_sdiff.mp hwS).1
        have hwD : w' ∉ D := (Finset.mem_sdiff.mp hwS).2
        have hwi : C w' = i := (Finset.mem_filter.mp hwT).2
        have hsub : G.neighborFinset v' ⊆ insert w' D := by
          intro u hu
          by_cases huD : u ∈ D
          · exact Finset.mem_insert.mpr (Or.inr huD)
          · have hvu : G.Adj v' u := (G.mem_neighborFinset v' u).mp hu
            have huT : u ∈ T := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (sameColor hvu hvw').trans hwi⟩
            have huS : u ∈ S := Finset.mem_sdiff.mpr ⟨huT, huD⟩
            exact Finset.mem_insert.mpr (Or.inl (huniq u huS hvu))
        have hbound := Finset.card_le_card hsub
        rw [G.card_neighborFinset_eq_degree v', hreg.degree_eq v',
          Finset.card_insert_of_notMem hwD, hDcard] at hbound
        omega
      have hsle : s ≤ S.card :=
        Finset.min'_le sw _ (Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨S, hSstop, rfl⟩)))
      omega
    have hstrong : s + d ≤ dist + 2 := by
      have hmem : dist ∈ cw := Finset.min'_mem cw hcw
      rcases Finset.mem_union.mp hmem with h | h
      · have hdist : dist = Fintype.card V + 1 := Finset.mem_singleton.mp h
        have hc := hclass (0 : Fin 2)
        have hcard : ((Finset.univ : Finset V).filter (fun v => C v = (0 : Fin 2))).card ≤ Fintype.card V := by
          simpa only [Finset.card_univ] using
            Finset.card_filter_le (Finset.univ : Finset V) (fun v => C v = (0 : Fin 2))
        omega
      · obtain ⟨x, hx, hxweight⟩ := Finset.mem_image.mp h
        have hxne : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
        have hxker : (G.adjMatrix (ZMod 2)).mulVecLin x = 0 := (Finset.mem_filter.mp hx).2.2
        obtain ⟨z, hz⟩ := hfsurj (⟨x, LinearMap.mem_ker.mpr hxker⟩ : K)
        have hxeq : ∀ v : V, x v = z (C v) := by
          intro v
          exact (congrFun (congrArg (fun y : K => (y : V → ZMod 2)) hz) v).symm
        obtain ⟨v, hv⟩ : ∃ v : V, x v ≠ 0 := by
          by_contra hno
          apply hxne
          funext v
          exact not_not.mp (not_exists.mp hno v)
        have hzv : z (C v) ≠ 0 := by
          rw [← hxeq v]
          exact hv
        have hsub : ((Finset.univ : Finset V).filter (fun u => C u = C v)) ⊆
            Finset.univ.filter (fun u => x u ≠ 0) := by
          intro u hu
          have hcu : C u = C v := (Finset.mem_filter.mp hu).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hxeq u, hcu]
          exact hzv
        have hweight : ((Finset.univ : Finset V).filter (fun u => C u = C v)).card ≤ hammingNorm x :=
          Finset.card_le_card hsub
        have hc := hclass (C v)
        omega
    have hstrongR : (s : ℝ) + (d : ℝ) ≤ (dist : ℝ) + 2 := by
      exact_mod_cast hstrong
    rw [hcoef]
    simp only [sub_zero, one_mul]
    rw [hr]
    linarith only [hstrongR]
  · obtain ⟨k, hk⟩ := ho
    have hkreal : (d : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have hf : Int.floor ((d : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hkreal]
    have hcoef : (d : ℝ) - 2 * (Int.floor ((d : ℝ) / 2) : ℝ) = 1 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    rw [hcoef]
    simpa only [sub_self, zero_mul, add_zero] using hbase

theorem model_09e1e211ed16a9f315c7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) + (((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))) * (((2 : ℝ) * ((Int.ceil (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) / (2 : ℝ))) : ℝ)) - ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ))))) := by
  classical
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  let c : ℕ := cw.min' hcw
  let r : ℝ := ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  change (c : ℝ) ≥ r + ((G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ)) * (2 * (Int.ceil (r / 2) : ℝ) - r)
  have hbase : r ≤ (c : ℝ) := parity_code_unique_neighbor_distance G
  rcases Nat.even_or_odd G.minDegree with he | ho
  · obtain ⟨k, hk⟩ := he
    have hkreal : (G.minDegree : ℝ) = (k : ℝ) + (k : ℝ) := by exact_mod_cast hk
    have hdiv : (G.minDegree : ℝ) / 2 = (k : ℝ) := by linarith only [hkreal]
    have hf : Int.floor ((G.minDegree : ℝ) / 2) = (k : ℤ) := by
      rw [hdiv, Int.floor_natCast]
    have hcoef : (G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) = 0 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    rw [hcoef]
    simpa only [zero_mul, add_zero] using hbase
  · have hoddcast : (G.minDegree : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr ho
    obtain ⟨k, hk⟩ := ho
    have hkreal : (G.minDegree : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have hf : Int.floor ((G.minDegree : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hkreal]
    have hcoef : (G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) = 1 := by
      rw [hf]
      push_cast
      linarith only [hkreal]
    have hnull : 0 < Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) := by
      by_contra hn
      have hz : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) = 0 := by omega
      have h := h_guard.2.2
      rw [hz] at h
      norm_num at h
    letI : Nontrivial (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) := Module.nontrivial_of_finrank_pos (R := ZMod 2) hnull
    obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
    have hxne : (x : V → ZMod 2) ≠ 0 := by
      intro h
      apply hx
      exact Subtype.ext h
    have hxword : (x : V → ZMod 2) ∈ words := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hxne, LinearMap.mem_ker.mp x.property⟩
    have hxmem : hammingNorm (x : V → ZMod 2) ∈ cw := by
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(x : V → ZMod 2), hxword, rfl⟩))
    have hc_card : c ≤ Fintype.card V := by
      exact (Finset.min'_le cw _ hxmem).trans hammingNorm_le_card_fintype
    obtain ⟨y, hy, hyc⟩ : ∃ y ∈ words, hammingNorm y = c := by
      rcases Finset.mem_union.mp (show c ∈ cw from Finset.min'_mem cw hcw) with h | h
      · have hs : c = Fintype.card V + 1 := Finset.mem_singleton.mp h
        omega
      · exact Finset.mem_image.mp h
    obtain ⟨v, hv⟩ : ∃ v, (x : V → ZMod 2) v ≠ 0 := by
      by_contra h
      apply hxne
      funext v
      exact not_not.mp (not_exists.mp h v)
    letI : Nonempty V := ⟨v⟩
    have hregular : G.IsRegularOfDegree G.minDegree := by
      obtain ⟨d, hd⟩ := h_guard.1
      have hmd : G.minDegree = d := hd.minDegree_eq
      rw [hmd]
      exact hd
    have hone : Matrix.mulVec (G.adjMatrix (ZMod 2)) (1 : V → ZMod 2) = 1 := by
      funext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2)) (Function.const V (1 : ZMod 2))) v = 1
      rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hregular, hoddcast, one_mul]
    have hyzero : Matrix.mulVec (G.adjMatrix (ZMod 2)) y = 0 := by
      simpa only [Matrix.mulVecLin_apply] using (Finset.mem_filter.mp hy).2.2
    have hsumzero : (∑ v, y v) = (0 : ZMod 2) := by
      have hs := (G.isSymm_adjMatrix (α := ZMod 2)).dotProduct_mulVec_comm (x := (1 : V → ZMod 2)) (y := y)
      rw [hyzero, hone] at hs
      simpa [dotProduct] using hs.symm
    have hweight : (hammingNorm y : ZMod 2) = ∑ v, y v := by
      calc
        (hammingNorm y : ZMod 2) = ∑ v ∈ Finset.univ.filter (fun v => y v ≠ 0), (1 : ZMod 2) := by
          simp [hammingNorm]
        _ = ∑ v ∈ Finset.univ.filter (fun v => y v ≠ 0), y v := by
          apply Finset.sum_congr rfl
          intro v hv
          have hne : y v ≠ 0 := (Finset.mem_filter.mp hv).2
          have hval : (y v).val = 1 := by
            have hp : 0 < (y v).val := ZMod.val_pos.mpr hne
            have hlt := ZMod.val_lt (y v)
            omega
          exact ((ZMod.val_eq_one (by decide) (y v)).mp hval).symm
        _ = ∑ v, y v := Finset.sum_filter_ne_zero (Finset.univ : Finset V)
    have hc_even : Even c := by
      rw [← hyc]
      exact ZMod.natCast_eq_zero_iff_even.mp (hweight.trans hsumzero)
    obtain ⟨m, hm⟩ := hc_even
    have hcreal : (c : ℝ) = (m : ℝ) + (m : ℝ) := by exact_mod_cast hm
    have hceil : Int.ceil (r / 2) ≤ (m : ℤ) := by
      apply Int.ceil_le.mpr
      push_cast
      linarith only [hbase, hcreal]
    have hceilreal : (Int.ceil (r / 2) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hceil
    rw [hcoef]
    simp only [one_mul]
    linarith only [hceilreal, hcreal]
theorem model_7f5a8625a28664c18ff7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) = (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) := by
  exact (model_9507736b3513f2c06029 G h_guard).symm
