import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic




open scoped BigOperators
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

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

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

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

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
theorem model_92debe23dc15135cb8a8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Gᶜ.cliqueNum : ℝ) * (((2 : ℝ) * (G.edgeFinset.card : ℝ)) + (Fintype.card V : ℝ))) ≥ ((Fintype.card V : ℝ) ^ 2) := by
  sorry
