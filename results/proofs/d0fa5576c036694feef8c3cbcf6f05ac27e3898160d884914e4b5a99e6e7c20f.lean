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
theorem model_067a59b774064887e40b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.cliqueNum : ℝ) ≤ (30000001 / 10000000 : ℝ)))) :
    ((6 : ℝ) * ((G.cliqueFinset 3).card : ℝ)) ≤ ((G.edgeFinset.card : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  have hclique : G.cliqueNum ≤ 3 := by
    by_contra h
    have hn : 4 ≤ G.cliqueNum := by omega
    have hr : (4 : ℝ) ≤ (G.cliqueNum : ℝ) := by exact_mod_cast hn
    linarith only [hr, h_guard.2.2]
  have hfour : G.CliqueFree 4 := by
    intro s hs
    have hc : s.card ≤ G.cliqueNum := hs.isClique.card_le_cliqueNum
    rw [hs.card_eq] at hc
    omega
  let C : V → Finset (Finset V) := fun v =>
    (G.cliqueFinset 3).filter (fun s => v ∈ s)
  have hlocal : ∀ v : V, 4 * ((C v).card : ℝ) ≤ (G.degree v : ℝ) ^ 2 := by
    intro v
    let H : SimpleGraph (G.neighborSet v) := G.induce (G.neighborSet v)
    have hH : H.CliqueFree 3 := by
      have hN : G.CliqueFreeOn (Set.univ ∩ G.neighborSet v) 3 :=
        SimpleGraph.CliqueFreeOn.of_succ G
          (hfour.cliqueFreeOn (s := Set.univ)) (Set.mem_univ v)
      apply (SimpleGraph.cliqueFree_induce_iff (G := G) (G.neighborSet v) 3).mpr
      simpa only [Set.univ_inter] using hN
    have htzero : (H.cliqueFinset 3).card = 0 := by
      simp only [hH.cliqueFinset, Finset.card_empty]
    have hD : (H.maxDegree : ℝ) ≤ (Hᶜ.cliqueNum : ℝ) := by
      simpa only [htzero, Nat.cast_zero, add_zero] using model_8b660ccec0c7e356f6cf H
    have hE := model_8ce30216566f34c2605a H
    rw [G.card_neighborSet_eq_degree v] at hE
    have hAnat : Hᶜ.cliqueNum ≤ G.degree v := by
      simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree v] using
        (Hᶜ).cliqueNum_le_natCard
    have hA : (Hᶜ.cliqueNum : ℝ) ≤ (G.degree v : ℝ) := by
      exact_mod_cast hAnat
    have hmult :
        ((G.degree v : ℝ) - (Hᶜ.cliqueNum : ℝ)) * (H.maxDegree : ℝ) ≤
        ((G.degree v : ℝ) - (Hᶜ.cliqueNum : ℝ)) * (Hᶜ.cliqueNum : ℝ) :=
      mul_le_mul_of_nonneg_left hD (sub_nonneg.mpr hA)
    have hmantel : 4 * (H.edgeFinset.card : ℝ) ≤ (G.degree v : ℝ) ^ 2 := by
      nlinarith only [hE, hmult,
        sq_nonneg ((G.degree v : ℝ) - 2 * (Hᶜ.cliqueNum : ℝ))]
    let U : Finset (Sym2 V) :=
      G.edgeFinset.filter (fun e => e.toFinset ⊆ G.neighborFinset v)
    have hex : ∀ s : ↥(C v), ∃ e : Sym2 V,
        e ∈ U ∧ e.toFinset = (s : Finset V).erase v := by
      intro s
      have hs : (s : Finset V) ∈ G.cliqueFinset 3 ∧ v ∈ (s : Finset V) := by
        simpa only [C, Finset.mem_filter] using s.property
      have htri : G.IsNClique 3 (s : Finset V) :=
        SimpleGraph.mem_cliqueFinset_iff.mp hs.1
      have hcard : ((s : Finset V).erase v).card = 2 := by
        rw [Finset.card_erase_of_mem hs.2, htri.card_eq]
      obtain ⟨a, b, hab, hpair⟩ := Finset.card_eq_two.mp hcard
      have ha : a ∈ (s : Finset V).erase v := by rw [hpair]; simp
      have hb : b ∈ (s : Finset V).erase v := by rw [hpair]; simp
      have hadj : G.Adj a b :=
        htri.isClique (Finset.mem_erase.mp ha).2 (Finset.mem_erase.mp hb).2 hab
      refine ⟨s(a, b), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
        · rw [Sym2.toFinset_mk_eq, ← hpair]
          intro w hw
          have hw' := Finset.mem_erase.mp hw
          exact (G.mem_neighborFinset v w).mpr
            (htri.isClique hs.2 hw'.2 hw'.1.symm)
      · simpa only [Sym2.toFinset_mk_eq] using hpair.symm
    choose f hfU hfE using hex
    let F : ↥(C v) → ↥U := fun s => ⟨f s, hfU s⟩
    have hFinj : Function.Injective F := by
      intro s t h
      apply Subtype.ext
      have he : f s = f t := congrArg Subtype.val h
      have herase : (s : Finset V).erase v = (t : Finset V).erase v :=
        (hfE s).symm.trans ((congrArg Sym2.toFinset he).trans (hfE t))
      have hs : v ∈ (s : Finset V) := (Finset.mem_filter.mp s.property).2
      have ht : v ∈ (t : Finset V) := (Finset.mem_filter.mp t.property).2
      calc
        (s : Finset V) = insert v ((s : Finset V).erase v) :=
          (Finset.insert_erase hs).symm
        _ = insert v ((t : Finset V).erase v) :=
          congrArg (fun u : Finset V => insert v u) herase
        _ = (t : Finset V) := Finset.insert_erase ht
    have hcount : (C v).card ≤ U.card := Finset.card_le_card_of_injective hFinj
    have hUcard : U.card = H.edgeFinset.card := by
      let e : (G.induce (↑(G.neighborFinset v) : Set V)) ≃g H :=
        { toEquiv := Set.equivOfEq (G.coe_neighborFinset v)
          map_rel_iff' := by intro a b; rfl }
      exact (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G)
        (G.neighborFinset v)).trans e.card_edgeFinset_eq
    rw [hUcard] at hcount
    have hc : ((C v).card : ℝ) ≤ (H.edgeFinset.card : ℝ) := by
      exact_mod_cast hcount
    nlinarith only [hc, hmantel]
  have hsum : (∑ v : V, (C v).card) = 3 * (G.cliqueFinset 3).card := by
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := G.cliqueFinset 3)
      (fun (v : V) (s : Finset V) => v ∈ s)
    calc
      (∑ v : V, (C v).card) = ∑ s ∈ G.cliqueFinset 3, s.card := by
        simpa only [C, Finset.bipartiteAbove, Finset.bipartiteBelow,
          Finset.filter_mem_eq_inter, Finset.univ_inter] using hdc
      _ = ∑ _s ∈ G.cliqueFinset 3, 3 :=
        Finset.sum_congr rfl (fun s hs =>
          (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq)
      _ = 3 * (G.cliqueFinset 3).card := by simp [Nat.mul_comm]
  have hbound :
      (∑ v : V, 4 * ((C v).card : ℝ)) ≤
      ∑ v : V, (G.maxDegree : ℝ) * (G.degree v : ℝ) := by
    apply Finset.sum_le_sum
    intro v hv
    have hd : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast G.degree_le_maxDegree v
    calc
      4 * ((C v).card : ℝ) ≤ (G.degree v : ℝ) ^ 2 := hlocal v
      _ ≤ (G.maxDegree : ℝ) * (G.degree v : ℝ) := by
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (G.degree v))
  have hsumR : (∑ v : V, ((C v).card : ℝ)) =
      3 * ((G.cliqueFinset 3).card : ℝ) := by
    exact_mod_cast hsum
  have hdegreeR : (∑ v : V, (G.degree v : ℝ)) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simp only [← Finset.mul_sum, hsumR, hdegreeR] at hbound
  nlinarith only [hbound]
