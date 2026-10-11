import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

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

theorem hull_chromatic_number_le_1_size_1_658db08f8c3d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  have hmax : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  have hmaxR : (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hmax
  have h := generative_chromatic_degree_pilot G
  linarith
theorem composed_1f689b2150941b00 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((G.edgeFinset.card : ℝ) + (1 : ℝ)) := by
  exact le_trans (archetype_chi_ge_omega G) (hull_chromatic_number_le_1_size_1_658db08f8c3d G)
