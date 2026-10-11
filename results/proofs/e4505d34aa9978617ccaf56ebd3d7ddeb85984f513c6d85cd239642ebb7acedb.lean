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

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h

theorem hull3d_size_ge_1_0_max_degree_normalized_laplacian_spectral_gap_0_is_connected_9b83028c151a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ (G.maxDegree : ℝ) := by
  classical
  have hn : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le G.edgeFinset.card
      (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast hn

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

theorem model_80d52b930d57ba66abee {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≤ (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) + (((Fintype.card V : ℝ) - ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ))) * (min (1 : ℝ) (max (0 : ℝ) ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)))))) := by
  classical
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ A.mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  let r : ℝ := ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  change (cw.min' hcw : ℝ) ≤ r + ((Fintype.card V : ℝ) - r) * min (1 : ℝ) (max (0 : ℝ) ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)))
  have horder : (cw.min' hcw : ℝ) ≤ (Fintype.card V : ℝ) :=
    nonzero_parity_code_distance_le_order G h_guard.2
  by_cases hm : Fintype.card V + 1 ≤ G.edgeFinset.card
  · have hmreal : (Fintype.card V : ℝ) + 1 ≤ (G.edgeFinset.card : ℝ) := by exact_mod_cast hm
    have hcoef : min (1 : ℝ) (max (0 : ℝ) ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ))) = 1 := by
      apply min_eq_left
      apply le_max_of_le_right
      linarith only [hmreal]
    rw [hcoef]
    calc
      (cw.min' hcw : ℝ) ≤ (Fintype.card V : ℝ) := horder
      _ = r + ((Fintype.card V : ℝ) - r) * 1 := by ring
  · have hmn : G.edgeFinset.card ≤ Fintype.card V := by omega
    have hmreal : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hmn
    have hcoef : min (1 : ℝ) (max (0 : ℝ) ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ))) = 0 := by
      rw [max_eq_left (sub_nonpos.mpr hmreal)]
      norm_num
    rw [hcoef, mul_zero, add_zero]
    have hmap (J : SimpleGraph V) [DecidableRel J.Adj] (R : Finset V) :
        (J.induce (R : Set V)).edgeFinset.card = (J.edgeFinset ∩ R.sym2).card := by
      simpa only [SimpleGraph.filter_edgeFinset_toFinset_subset] using
        (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := J) R).symm
    obtain ⟨F, hFG, hFT⟩ := h_guard.1.exists_isTree_le
    have hFGfin : F.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hFG
    have hFcard : F.edgeFinset.card + 1 = Fintype.card V := hFT.card_edgeFinset
    have hdiffEq := Finset.card_sdiff_of_subset hFGfin
    have hdiff : (G.edgeFinset \ F.edgeFinset).card ≤ 1 := by omega
    have hsparse (R : Finset V) : (G.induce (R : Set V)).edgeFinset.card ≤ R.card := by
      by_cases hR : R.Nonempty
      · obtain ⟨t, ht⟩ := hR
        letI : Nonempty ↥R := ⟨⟨t, ht⟩⟩
        obtain ⟨J, hHJ, hJtop, hJT⟩ :=
          (SimpleGraph.connected_top (V := ↥R)).exists_isTree_le_of_le_of_isAcyclic
            (show F.induce (R : Set V) ≤ (⊤ : SimpleGraph ↥R) from le_top)
            (hFT.isAcyclic.induce (R : Set V))
        have hJcard : J.edgeFinset.card + 1 = R.card := by
          simpa only [Fintype.card_coe] using hJT.card_edgeFinset
        have hFH : (F.edgeFinset ∩ R.sym2).card + 1 ≤ R.card := by
          have hh := Finset.card_le_card (SimpleGraph.edgeFinset_mono hHJ)
          rw [hmap F R] at hh
          omega
        have hdsub : (G.edgeFinset ∩ R.sym2) \ (F.edgeFinset ∩ R.sym2) ⊆ G.edgeFinset \ F.edgeFinset := by
          intro e he
          simp only [Finset.mem_sdiff, Finset.mem_inter] at he ⊢
          exact ⟨he.1.1, fun heF => he.2 ⟨heF, he.1.2⟩⟩
        have hdcard := Finset.card_le_card hdsub
        have hg := Finset.card_le_card_sdiff_add_card (s := G.edgeFinset ∩ R.sym2) (t := F.edgeFinset ∩ R.sym2)
        rw [hmap G R]
        omega
      · have hr : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
        rw [hmap G R, hr]
        simp
    let Q (R : Finset V) : Finset (V × V) := Finset.univ.filter (fun p => p.1 ∈ R ∧ p.2 ∈ R ∧ G.Adj p.1 p.2)
    have hQ (R : Finset V) : (Q R).card ≤ 2 * R.card := by
      have hb : (Finset.univ.filter (fun p : ↥R × ↥R => (G.induce (R : Set V)).Adj p.1 p.2)).card = (Q R).card := by
        refine Finset.card_bij (fun p _ => ((p.1 : V), (p.2 : V))) ?_ ?_ ?_
        · intro p hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.1.property, p.2.property, (Finset.mem_filter.mp hp).2⟩
        · intro p hp q hq heq
          apply Prod.ext
          · exact Subtype.ext (congrArg Prod.fst heq)
          · exact Subtype.ext (congrArg Prod.snd heq)
        · intro p hp
          have hh := (Finset.mem_filter.mp hp).2
          refine ⟨(⟨p.1, hh.1⟩, ⟨p.2, hh.2.1⟩), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.2.2⟩
      have ht := (G.induce (R : Set V)).two_mul_card_edgeFinset
      have heq : (Q R).card = 2 * (G.induce (R : Set V)).edgeFinset.card := hb.symm.trans ht.symm
      rw [heq]
      exact Nat.mul_le_mul_left 2 (hsparse R)
    have hcode : ∀ S ∈ stops, ∃ x : V → ZMod 2, x ≠ 0 ∧ A.mulVecLin x = 0 ∧ hammingNorm x ≤ S.card := by
      intro S hS
      have hs := (Finset.mem_filter.mp hS).2
      let N : Finset V := Finset.univ.filter (fun v => ∃ w ∈ S, G.Adj v w)
      let k (v : V) : Finset V := (G.neighborFinset v).filter (fun w => w ∈ S)
      let D : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2 ∧ p.2 ∈ S)
      let E : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2 ∧ p.1 ∈ S)
      have hDN : ∀ p ∈ D, p.1 ∈ N := by
        intro p hp
        have hh := (Finset.mem_filter.mp hp).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.2, hh.2, hh.1⟩⟩
      have hDE : D.card = E.card := by
        refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
        · intro p hp
          simpa [D, E, SimpleGraph.adj_comm] using hp
        · intro p hp
          simpa [D, E, SimpleGraph.adj_comm] using hp
        · intro p hp
          simp
        · intro p hp
          simp
      have hU : D ∪ E ⊆ Q (S ∪ N) := by
        intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · have hh := (Finset.mem_filter.mp hp).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union.mpr (Or.inr (hDN p hp)), Finset.mem_union.mpr (Or.inl hh.2), hh.1⟩
        · have hh := (Finset.mem_filter.mp hp).2
          have hn : p.2 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.1, hh.2, hh.1.symm⟩⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union.mpr (Or.inl hh.2), Finset.mem_union.mpr (Or.inr hn), hh.1⟩
      have hI : D ∩ E ⊆ Q (S ∩ N) := by
        intro p hp
        have hpD := (Finset.mem_inter.mp hp).1
        have hpE := (Finset.mem_inter.mp hp).2
        have hhD := (Finset.mem_filter.mp hpD).2
        have hhE := (Finset.mem_filter.mp hpE).2
        have hn : p.2 ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p.1, hhE.2, hhD.1.symm⟩⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_inter.mpr ⟨hhE.2, hDN p hpD⟩, Finset.mem_inter.mpr ⟨hhD.2, hn⟩, hhD.1⟩
      have hDupper : D.card ≤ S.card + N.card := by
        have hu := Finset.card_le_card hU
        have hi := Finset.card_le_card hI
        have hqu := hQ (S ∪ N)
        have hqi := hQ (S ∩ N)
        have hde := Finset.card_union_add_card_inter D E
        have hsn := Finset.card_union_add_card_inter S N
        omega
      have hDsum : D.card = ∑ v ∈ N, (k v).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun p : V × V => p.1) (s := D) (t := N) hDN]
        apply Finset.sum_congr rfl
        intro v hv
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp
          have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hpv : p.1 = v := (Finset.mem_filter.mp hp).2
          apply Finset.mem_filter.mpr
          refine ⟨(G.mem_neighborFinset v p.2).mpr ?_, hh.2⟩
          simpa only [hpv] using hh.1
        · intro p hp q hq heq
          exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) heq
        · intro w hw
          have hh := Finset.mem_filter.mp hw
          refine ⟨(v, w), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (G.mem_neighborFinset v w).mp hh.1, hh.2⟩, rfl⟩
      have hk : ∀ v ∈ N, 2 ≤ (k v).card := by
        intro v hv
        obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hv).2
        have hkp : 0 < (k v).card := Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v w).mpr hvw, hw⟩⟩
        have hkne : (k v).card ≠ 1 := by
          intro hh
          obtain ⟨u, hu, huniq⟩ := Finset.card_eq_one_iff_existsUnique.mp hh
          have hu' := Finset.mem_filter.mp hu
          apply hs.2
          refine ⟨v, u, hu'.2, (G.mem_neighborFinset v u).mp hu'.1, ?_⟩
          intro z hz hvz
          exact huniq z (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v z).mpr hvz, hz⟩)
        omega
      have hDlower : 2 * N.card ≤ D.card := by
        rw [hDsum]
        calc
          2 * N.card = ∑ v ∈ N, (2 : ℕ) := by simp [Nat.mul_comm]
          _ ≤ ∑ v ∈ N, (k v).card := Finset.sum_le_sum hk
      have hNle : N.card ≤ S.card := by omega
      let M : Matrix ↥N ↥S (ZMod 2) := fun v w => A (v : V) (w : V)
      have hyexists : ∃ y : ↥S → ZMod 2, y ≠ 0 ∧ M.mulVecLin y = 0 := by
        by_cases hlt : N.card < S.card
        · have hnoninj : ¬ Function.Injective M.mulVecLin := by
            intro hinj
            have hdim : S.card ≤ N.card := by
              simpa only [Module.finrank_pi, Fintype.card_coe] using
                (LinearMap.finrank_le_finrank_of_injective (f := M.mulVecLin) hinj)
            omega
          by_contra hy
          apply hnoninj
          apply LinearMap.ker_eq_bot.mp
          apply LinearMap.ker_eq_bot'.mpr
          intro y hyzero
          by_contra hyne
          exact hy ⟨y, hyne, hyzero⟩
        · have hNE : N.card = S.card := by omega
          have hsum : (∑ v ∈ N, (2 : ℕ)) = ∑ v ∈ N, (k v).card := by
            have hc : D.card = 2 * N.card := by omega
            rw [← hDsum]
            simpa [Nat.mul_comm] using hc.symm
          have hktwo : ∀ v ∈ N, (k v).card = 2 := by
            have hh := (Finset.sum_eq_sum_iff_of_le hk).mp hsum
            intro v hv
            exact (hh v hv).symm
          refine ⟨(fun _ : ↥S => (1 : ZMod 2)), ?_, ?_⟩
          · intro hz
            obtain ⟨t, ht⟩ := hs.1
            have hh := congrFun hz ⟨t, ht⟩
            norm_num at hh
          · funext v
            rw [Matrix.mulVecLin_apply]
            change (∑ w : ↥S, M v w * (1 : ZMod 2)) = 0
            simp only [mul_one]
            change (∑ w : ↥S, if G.Adj (v : V) (w : V) then (1 : ZMod 2) else 0) = 0
            rw [Finset.sum_boole]
            have hc : (Finset.univ.filter (fun w : ↥S => G.Adj (v : V) (w : V))).card = (k (v : V)).card := by
              refine Finset.card_bij (fun w _ => (w : V)) ?_ ?_ ?_
              · intro w hw
                exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset (v : V) (w : V)).mpr (Finset.mem_filter.mp hw).2, w.property⟩
              · intro w hw u hu heq
                exact Subtype.ext heq
              · intro w hw
                have hh := Finset.mem_filter.mp hw
                refine ⟨⟨w, hh.2⟩, ?_, rfl⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (G.mem_neighborFinset (v : V) w).mp hh.1⟩
            rw [hc, hktwo (v : V) v.property]
            exact ZMod.natCast_self 2
      obtain ⟨y, hyne, hyker⟩ := hyexists
      let x : V → ZMod 2 := fun v => if hv : v ∈ S then y ⟨v, hv⟩ else 0
      have hxne : x ≠ 0 := by
        intro hx
        apply hyne
        funext w
        have hz := congrFun hx (w : V)
        simpa [x, w.property] using hz
      have hsumVector (v : V) : (A.mulVecLin x) v = ∑ w : ↥S, A v w * y w := by
        rw [Matrix.mulVecLin_apply]
        change (∑ w : V, A v w * x w) = ∑ w : ↥S, A v w * y w
        calc
          (∑ w : V, A v w * x w) = ∑ w ∈ S, A v w * x w := by
            symm
            apply Finset.sum_subset (Finset.subset_univ S)
            intro w hw hwn
            simp [x, hwn]
          _ = ∑ w : ↥S, A v w * x w := (Finset.sum_coe_sort S (fun w => A v w * x w)).symm
          _ = ∑ w : ↥S, A v w * y w := by
            apply Finset.sum_congr rfl
            intro w hw
            simp [x, w.property]
      have hxker : A.mulVecLin x = 0 := by
        funext v
        rw [hsumVector v]
        by_cases hv : v ∈ N
        · have hz := congrFun hyker ⟨v, hv⟩
          change (∑ w : ↥S, A v w * y w) = 0 at hz
          exact hz
        · apply Finset.sum_eq_zero
          intro w hw
          have hnAdj : ¬ G.Adj v (w : V) := by
            intro hvw
            exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(w : V), w.property, hvw⟩⟩)
          simp [A, hnAdj]
      have hxwt : hammingNorm x ≤ S.card := by
        change (Finset.univ.filter (fun v => x v ≠ 0)).card ≤ S.card
        apply Finset.card_le_card
        intro v hv
        have hnv : x v ≠ 0 := (Finset.mem_filter.mp hv).2
        by_contra hvS
        exact hnv (by simp [x, hvS])
      exact ⟨x, hxne, hxker, hxwt⟩
    have hreverse : cw.min' hcw ≤ sw.min' hsw := by
      apply Finset.le_min'
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have hh : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
        subst a
        exact Finset.min'_le _ _ (by simp [cw])
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨x, hxne, hxker, hxwt⟩ := hcode S hS
        have hmem : hammingNorm x ∈ cw :=
          Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
            ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩, rfl⟩))
        exact (Finset.min'_le cw _ hmem).trans hxwt
    have hpos : 1 ≤ sw.min' hsw := by
      apply Finset.le_min'
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have hh : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
        omega
      · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_filter.mp hS).2.1.card_pos
    have hn : cw.min' hcw ≤ sw.min' hsw - 1 + 1 := by omega
    change (cw.min' hcw : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
    exact_mod_cast hn
theorem model_3e6fe089e7f561723b1e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≤ (30000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((G.maxDegree : ℝ) * ((Fintype.card V : ℝ) - (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)))) ≥ ((2 : ℝ) * ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ))) := by
  classical
  have hmax : G.maxDegree ≤ 3 := by
    have hr : (G.maxDegree : ℝ) < 4 := by
      linarith only [h_guard.2.2.1]
    have hn : G.maxDegree < 4 := by exact_mod_cast hr
    omega
  let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hKpos : 0 < Module.finrank (ZMod 2) K := by
    have hr : (0 : ℝ) < (Module.finrank (ZMod 2) K : ℝ) := by
      dsimp [K]
      linarith only [h_guard.2.2.2]
    exact_mod_cast hr
  obtain ⟨z, hzne⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := K)).mp hKpos
  let x : V → ZMod 2 := z
  have hxne : x ≠ 0 := by
    intro heq
    apply hzne
    exact Subtype.ext heq
  have hxker : (G.adjMatrix (ZMod 2)).mulVecLin x = 0 := z.property
  have hbinary (a : ZMod 2) :
      (if a ≠ 0 then (1 : ZMod 2) else 0) = a := by
    fin_cases a
    · change (if (0 : ZMod 2) ≠ 0 then (1 : ZMod 2) else 0) = 0
      simp
    · change (if (1 : ZMod 2) ≠ 0 then (1 : ZMod 2) else 0) = 1
      simp
  let S : Finset V := Finset.univ.filter (fun w => x w ≠ 0)
  let T : Finset V := Finset.univ.filter (fun w => x w = 0)
  let k (v : V) : Finset V :=
    (G.neighborFinset v).filter (fun w => x w ≠ 0)
  let q (v : V) : Finset V :=
    (G.neighborFinset v).filter (fun w => x w = 0)
  have hparity (v : V) : ((k v).card : ZMod 2) = 0 := by
    calc
      ((k v).card : ZMod 2) =
          ∑ w ∈ G.neighborFinset v, if x w ≠ 0 then (1 : ZMod 2) else 0 := by
        simp only [k, Finset.sum_boole]
      _ = ∑ w ∈ G.neighborFinset v, x w :=
        Finset.sum_congr rfl (fun w _ => hbinary (x w))
      _ = 0 := by
        have hh := congrFun hxker v
        simpa only [Matrix.mulVecLin_apply,
          SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using hh
  have hkle (v : V) : (k v).card ≤ 2 := by
    have hc : (k v).card ≤ G.degree v :=
      Finset.card_filter_le (G.neighborFinset v) (fun w => x w ≠ 0)
    have h3 : (k v).card ≤ 3 :=
      hc.trans ((G.degree_le_maxDegree v).trans hmax)
    have hne3 : (k v).card ≠ 3 := by
      intro heq
      have hh := hparity v
      rw [heq] at hh
      exact (by decide : (3 : ZMod 2) ≠ 0) hh
    omega
  have hsplit (v : V) : (k v).card + (q v).card = G.degree v := by
    simpa [k, q] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset v) (fun w => x w ≠ 0))
  have hsumq : (∑ v, (q v).card) = ∑ w ∈ T, G.degree w := by
    calc
      (∑ v, (q v).card) =
          ∑ v, ∑ w, if x w = 0 then
            (if G.Adj v w then (1 : ℕ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        change ((G.neighborFinset v).filter (fun w => x w = 0)).card = _
        rw [G.neighborFinset_eq_filter, Finset.filter_filter, Finset.card_filter]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases ha : G.Adj v w <;> by_cases hz : x w = 0 <;> simp [ha, hz]
      _ = ∑ w, ∑ v, if x w = 0 then
            (if G.Adj v w then (1 : ℕ) else 0) else 0 :=
        Finset.sum_comm
      _ = ∑ w, if x w = 0 then G.degree w else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hz : x w = 0
        · simp only [if_pos hz]
          rw [← G.card_neighborFinset_eq_degree w,
            G.neighborFinset_eq_filter, Finset.card_filter]
          apply Finset.sum_congr rfl
          intro v hv
          simp only [G.adj_comm v w]
        · simp [hz]
      _ = ∑ w ∈ T, G.degree w := by
        simp only [T, Finset.sum_filter]
  have hqbound : (∑ v, (q v).card) ≤ G.maxDegree * T.card := by
    rw [hsumq]
    calc
      (∑ w ∈ T, G.degree w) ≤ ∑ _w ∈ T, G.maxDegree :=
        Finset.sum_le_sum (fun w _ => G.degree_le_maxDegree w)
      _ = G.maxDegree * T.card := by simp [Nat.mul_comm]
  have hbound : 2 * G.edgeFinset.card ≤
      2 * Fintype.card V + G.maxDegree * T.card := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v :=
        G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ v, (2 + (q v).card) := by
        apply Finset.sum_le_sum
        intro v hv
        rw [← hsplit v]
        exact Nat.add_le_add_right (hkle v) _
      _ = 2 * Fintype.card V + ∑ v, (q v).card := by
        simp [Finset.sum_add_distrib, Nat.mul_comm]
      _ ≤ 2 * Fintype.card V + G.maxDegree * T.card :=
        Nat.add_le_add_left hqbound _
  have hcard : S.card + T.card = Fintype.card V := by
    simpa [S, T] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun w => x w ≠ 0))
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun y => y ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin y = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  have hxmem : hammingNorm x ∈ weights :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩, rfl⟩))
  have hdist : weights.min' hw ≤ S.card := by
    change weights.min' hw ≤ hammingNorm x
    exact Finset.min'_le weights _ hxmem
  have hbound_real : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
      2 * (Fintype.card V : ℝ) + (G.maxDegree : ℝ) * (T.card : ℝ) := by
    exact_mod_cast hbound
  have hcard_real : (S.card : ℝ) + (T.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcard
  have hdist_real : (weights.min' hw : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hdist
  have ht : (T.card : ℝ) ≤
      (Fintype.card V : ℝ) - (weights.min' hw : ℝ) := by
    linarith only [hcard_real, hdist_real]
  change (G.maxDegree : ℝ) *
      ((Fintype.card V : ℝ) - (weights.min' hw : ℝ)) ≥
    (2 : ℝ) * ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ))
  calc
    (2 : ℝ) * ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) ≤
        (G.maxDegree : ℝ) * (T.card : ℝ) := by
      linarith only [hbound_real]
    _ ≤ (G.maxDegree : ℝ) *
        ((Fintype.card V : ℝ) - (weights.min' hw : ℝ)) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
