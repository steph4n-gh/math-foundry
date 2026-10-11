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

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)

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

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn
theorem model_3307c010f6ed4887361d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (((Gᶜ.cliqueNum : ℝ) * ((Gᶜ.cliqueNum : ℝ) - (1 : ℝ))) + ((2 : ℝ) * (G.edgeFinset.card : ℝ))) ≤ ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - (1 : ℝ))) := by
  classical
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  let e : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
  have hecard : e.card = 2 * G.edgeFinset.card :=
    G.two_mul_card_edgeFinset.symm
  have hd : Disjoint s.offDiag e := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    obtain ⟨hv, hw, hne⟩ := Finset.mem_offDiag.mp hp
    have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp he).2
    exact ((SimpleGraph.compl_adj G p.1 p.2).mp
      (hs.isClique hv hw hne)).2 hadj
  have hsub : s.offDiag ∪ e ⊆ (Finset.univ : Finset V).offDiag := by
    intro p hp
    apply Finset.mem_offDiag.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_offDiag.mp hp).2.2
    · have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
      exact hadj.ne
  have hcount := Finset.card_le_card hsub
  simp only [Finset.card_union_of_disjoint hd, hecard, Finset.offDiag_card,
    Finset.card_univ, hs.card_eq] at hcount
  have hcast (n : ℕ) :
      ((n * n - n : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
    ring
  have hreal :
      ((Gᶜ.cliqueNum * Gᶜ.cliqueNum - Gᶜ.cliqueNum : ℕ) : ℝ) +
        2 * (G.edgeFinset.card : ℝ) ≤
      ((Fintype.card V * Fintype.card V - Fintype.card V : ℕ) : ℝ) := by
    exact_mod_cast hcount
  simpa only [hcast] using hreal
