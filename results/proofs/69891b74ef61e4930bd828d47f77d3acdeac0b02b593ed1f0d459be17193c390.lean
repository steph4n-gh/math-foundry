import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem pilot_bipartite_two_colors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.chromaticNumber.toNat : ℝ) ≤ (2 : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast h_guard.chromaticNumber_le)

theorem generative_chromatic_degree_pilot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  have hpartial : ∀ s : Finset V,
      ∃ c : V → Fin (G.maxDegree + 1),
        ∀ v ∈ s, ∀ w ∈ s, G.Adj v w → c v ≠ c w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩, ?_⟩
        intro v hv
        simp at hv
    | @insert a s ha ih =>
        obtain ⟨c, hc⟩ := ih
        have hcard : ((G.neighborFinset a).image c).card <
            (Finset.univ : Finset (Fin (G.maxDegree + 1))).card := by
          calc
            ((G.neighborFinset a).image c).card ≤
                (G.neighborFinset a).card := Finset.card_image_le
            _ = G.degree a := rfl
            _ ≤ G.maxDegree := G.degree_le_maxDegree a
            _ < (Finset.univ : Finset (Fin (G.maxDegree + 1))).card := by simp
        obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hdc : ∀ w, G.Adj a w → d ≠ c w := by
          intro w haw heq
          apply hd
          exact Finset.mem_image.mpr
            ⟨w, (G.mem_neighborFinset a w).mpr haw, heq.symm⟩
        refine ⟨fun v => if v = a then d else c v, ?_⟩
        intro v hv w hw hvw
        by_cases hva : v = a
        · subst v
          have hwa : w ≠ a := hvw.ne'
          simpa [hwa] using hdc w hvw
        · by_cases hwa : w = a
          · subst w
            simpa [hva] using (hdc v hvw.symm).symm
          · have hvs : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hva
            have hws : w ∈ s := (Finset.mem_insert.mp hw).resolve_left hwa
            simpa [hva, hwa] using hc v hvs w hws hvw
  obtain ⟨c, hc⟩ := hpartial Finset.univ
  have hcolor : G.Colorable (G.maxDegree + 1) :=
    ⟨SimpleGraph.Coloring.mk c (fun {v w} h =>
      hc v (Finset.mem_univ v) w (Finset.mem_univ w) h)⟩
  have hn : G.chromaticNumber.toNat ≤ G.maxDegree + 1 :=
    ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  exact_mod_cast hn

theorem archetype_brooks_standard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  have h := generative_chromatic_degree_pilot G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]
theorem model_e0b140f9bf3d5870fe9f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.chromaticNumber.toNat : ℝ) = (G.cliqueNum : ℝ) := by
  classical
  cases isEmpty_or_nonempty V
  · simp
  · by_cases hG : G = ⊥
    · simp [hG, SimpleGraph.chromaticNumber_bot]
    · obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
      have hc : G.IsClique (↑({u, v} : Finset V) : Set V) := by
        rw [Finset.coe_pair, SimpleGraph.isClique_pair]
        exact fun _ => huv
      have hw : 2 ≤ G.cliqueNum := by
        simpa [huv.ne] using hc.card_le_cliqueNum
      have hwR : (2 : ℝ) ≤ (G.cliqueNum : ℝ) := by
        exact_mod_cast hw
      exact le_antisymm
        ((pilot_bipartite_two_colors G h_guard).trans hwR)
        (archetype_chi_ge_omega G)
