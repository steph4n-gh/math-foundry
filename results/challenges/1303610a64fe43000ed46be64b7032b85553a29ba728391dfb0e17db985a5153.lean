import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem clique_edges_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hdv : ∀ v ∈ s, (G.cliqueNum : ℝ) - 1 ≤ (G.degree v : ℝ) := by
    intro v hv
    have hsubset : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [G.mem_neighborFinset]
      exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
    have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
    have hn : G.cliqueNum ≤ G.degree v + 1 := by omega
    have hr : (G.cliqueNum : ℝ) ≤ (G.degree v : ℝ) + 1 := by exact_mod_cast hn
    linarith
  calc
    (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) = ∑ v ∈ s, ((G.cliqueNum : ℝ) - 1) := by
      simp [hs.card_eq]
      ring
    _ ≤ ∑ v ∈ s, (G.degree v : ℝ) := Finset.sum_le_sum hdv
    _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ s) (fun v _ _ => Nat.cast_nonneg _)
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem clique_le_max_degree_plus_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hn : G.cliqueNum ≤ G.maxDegree + 1 := by
    by_cases he : s.Nonempty
    · obtain ⟨v, hv⟩ := he
      have hsubset : s.erase v ⊆ G.neighborFinset v := by
        intro w hw
        rw [G.mem_neighborFinset]
        exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
      have hmax := G.degree_le_maxDegree v
      have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
      omega
    · have : G.cliqueNum = 0 := by
        rw [← hs.card_eq]
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
      omega
  exact_mod_cast hn

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

theorem composed_b214f1e86200a2e1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have checked_0 := clique_le_max_degree_plus_one G; have checked_1 := composed_2cd2dd810fbb9720 G; have checked_2 := degree_sum_density_bound G; have checked_3 := archetype_chi_ge_omega G; have checked_4 := chromatic_le_order G; have checked_5 := clique_edges_density_bound G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem model_e679ce9c7fa60e2c7bfd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) * ((G.chromaticNumber.toNat : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
    let n := G.chromaticNumber.toNat
    obtain ⟨c⟩ := G.colorable_chromaticNumber_of_fintype
    let H : SimpleGraph (Fin n) := G.map c
    have hn : (n : ℕ∞) ≤ H.chromaticNumber :=
      (ENat.natCast_toNat_le_self G.chromaticNumber).trans
        (SimpleGraph.chromaticNumber_mono_of_hom c.homMap)
    have hH : H = ⊤ := by
      apply SimpleGraph.eq_top_of_chromaticNumber_eq_card
      apply le_antisymm H.chromaticNumber_le_card
      simpa only [Fintype.card_fin] using hn
    have hsurj : Function.Surjective c.homMap.mapDart := by
      intro d
      obtain ⟨_, u, v, huv, hu, hv⟩ :=
        (SimpleGraph.map_adj' c G d.fst d.snd).mp d.adj
      refine ⟨⟨(u, v), huv⟩, ?_⟩
      apply SimpleGraph.Dart.ext
      exact Prod.ext hu hv
    have hcard : Fintype.card H.Dart ≤ Fintype.card G.Dart :=
      Fintype.card_le_of_surjective c.homMap.mapDart hsurj
    rw [H.dart_card_eq_twice_card_edges,
      G.dart_card_eq_twice_card_edges] at hcard
    have hreal : (2 : ℝ) * (H.edgeFinset.card : ℝ) ≤
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hcard
    have hclique : H.cliqueNum = n := by
      rw [hH, SimpleGraph.cliqueNum_top, Nat.card_fin]
    have hbound := clique_edges_density_bound H
    rw [hclique] at hbound
    exact hbound.trans hreal

theorem composed_ef727e745e60525c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) * ((G.chromaticNumber.toNat : ℝ) - (1 : ℝ))) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  exact (model_e679ce9c7fa60e2c7bfd G).trans (degree_sum_density_bound G)

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem model_8b660ccec0c7e356f6cf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) + ((G.cliqueFinset 3).card : ℝ)) := by
  classical
  have hnat : G.maxDegree ≤ Gᶜ.cliqueNum + (G.cliqueFinset 3).card := by
    apply G.maxDegree_le_of_forall_degree_le
    intro v
    let A : Finset (Finset V) :=
      (G.neighborFinset v).powerset.filter (fun s => Gᶜ.IsClique (s : Set V))
    have hA : A.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [A]
    obtain ⟨s, hsA, hsmax⟩ :=
      Finset.exists_max_image A (fun s : Finset V => s.card) hA
    have hsN : s ⊆ G.neighborFinset v :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hsA).1
    have hsC : Gᶜ.IsClique (s : Set V) :=
      (Finset.mem_filter.mp hsA).2
    let t : Finset V := G.neighborFinset v \ s
    have ht : ∀ w : ↥t, ∃ u : V, u ∈ s ∧ G.Adj (w : V) u := by
      intro w
      have hwN : (w : V) ∈ G.neighborFinset v :=
        (Finset.mem_sdiff.mp w.property).1
      have hws : (w : V) ∉ s :=
        (Finset.mem_sdiff.mp w.property).2
      by_contra hw
      have hc : Gᶜ.IsClique ((insert (w : V) s : Finset V) : Set V) := by
        rw [Finset.coe_insert]
        apply hsC.insert
        intro u hu hne
        exact (SimpleGraph.compl_adj G _ _).mpr
          ⟨hne, fun hadj => hw ⟨u, hu, hadj⟩⟩
      have hin : insert (w : V) s ∈ A :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.insert_subset_iff.mpr ⟨hwN, hsN⟩), hc⟩
      have hle := hsmax (insert (w : V) s) hin
      rw [Finset.card_insert_of_notMem hws] at hle
      omega
    choose f hfS hfAdj using ht
    let F : ↥t → ↥(G.cliqueFinset 3) := fun w =>
      ⟨{v, (w : V), f w},
        SimpleGraph.mem_cliqueFinset_iff.mpr
          (SimpleGraph.is3Clique_triple_iff.mpr
            ⟨(G.mem_neighborFinset v (w : V)).mp
                (Finset.mem_sdiff.mp w.property).1,
              (G.mem_neighborFinset v (f w)).mp (hsN (hfS w)),
              hfAdj w⟩)⟩
    have hFinj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      have hsets : ({v, (x : V), f x} : Finset V) = {v, (y : V), f y} :=
        congrArg Subtype.val hxy
      have hxmem : (x : V) ∈ ({v, (y : V), f y} : Finset V) := by
        rw [← hsets]
        simp
      have hxne : (x : V) ≠ v :=
        ((G.mem_neighborFinset v (x : V)).mp
          (Finset.mem_sdiff.mp x.property).1).ne'
      have hxnot : (x : V) ∉ s :=
        (Finset.mem_sdiff.mp x.property).2
      have hxf : (x : V) ≠ f y := by
        intro h
        apply hxnot
        rw [h]
        exact hfS y
      simpa [hxne, hxf] using hxmem
    have htcard : t.card ≤ (G.cliqueFinset 3).card :=
      Finset.card_le_card_of_injective hFinj
    have hscard : s.card ≤ Gᶜ.cliqueNum := hsC.card_le_cliqueNum
    have hsum : t.card + s.card = G.degree v := by
      simpa only [t, G.card_neighborFinset_eq_degree] using
        Finset.card_sdiff_add_card_eq_card hsN
    calc
      G.degree v = t.card + s.card := hsum.symm
      _ ≤ (G.cliqueFinset 3).card + Gᶜ.cliqueNum := Nat.add_le_add htcard hscard
      _ = Gᶜ.cliqueNum + (G.cliqueFinset 3).card := Nat.add_comm _ _
  exact_mod_cast hnat
theorem model_c36bd6bfd40d117b3da2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (((G.maxDegree : ℝ) + (1 : ℝ)) * (Gᶜ.cliqueNum : ℝ)) ≤ ((G.maxDegree : ℝ) * (Fintype.card V : ℝ)) := by
  sorry
