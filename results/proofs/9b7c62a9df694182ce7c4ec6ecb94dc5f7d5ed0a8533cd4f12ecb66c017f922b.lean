import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith
theorem model_24f5a5ae83b29af4e2eb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (G.minDegree : ℝ)) ≤ (((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ) + (1 : ℝ)) := by
  classical
  have hd : 2 ≤ G.minDegree := by
    by_contra h
    have hle : G.minDegree ≤ 1 := by omega
    have hr : (G.minDegree : ℝ) ≤ 1 := by exact_mod_cast hle
    have ht : (1 : ℝ) < 19999999 / 10000000 := by norm_num
    linarith [h_guard.2.1]
  obtain ⟨C⟩ := h_guard.1
  have hV : Nonempty V := by
    rcases isEmpty_or_nonempty V with he | hn
    · letI : IsEmpty V := he
      have hz : G.minDegree = 0 := by simp
      exfalso
      omega
    · exact hn
  obtain ⟨v₀⟩ := hV
  have hp : 0 < G.degree v₀ := by
    have h := G.minDegree_le_degree v₀
    omega
  obtain ⟨w₀, hvw₀⟩ := (G.degree_pos_iff_exists_adj v₀).mp hp
  have htwo : ∀ a b c : Fin 2, a ≠ c → b ≠ c → a = b := by decide
  have hn (v : V) (c : Fin 2) (hvc : C v ≠ c) :
      G.neighborFinset v ⊆ (Finset.univ : Finset V).filter (fun u => C u = c) := by
    intro u hu
    have hvu : G.Adj v u := by
      simpa only [SimpleGraph.mem_neighborFinset] using hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,
      htwo (C u) c (C v) (Ne.symm (C.valid hvu)) (Ne.symm hvc)⟩
  have hclasses (c : Fin 2) :
      G.minDegree ≤ ((Finset.univ : Finset V).filter (fun u => C u = c)).card := by
    have hex : ∃ x : V, C x ≠ c := by
      by_cases hv : C v₀ = c
      · refine ⟨w₀, ?_⟩
        intro hw
        exact C.valid hvw₀ (hv.trans hw.symm)
      · exact ⟨v₀, hv⟩
    obtain ⟨x, hx⟩ := hex
    have hc : G.degree x ≤
        ((Finset.univ : Finset V).filter (fun u => C u = c)).card := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        Finset.card_le_card (hn x c hx)
    exact (G.minDegree_le_degree x).trans hc
  let A : Finset V := Finset.univ.filter (fun v => C v = (0 : Fin 2))
  let B : Finset V := Finset.univ.filter (fun v => C v = (1 : Fin 2))
  have hfin : ∀ i : Fin 2, (i ≠ 0) ↔ i = 1 := by decide
  have hsum : A.card + B.card = Fintype.card V := by
    simpa only [A, B, hfin, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (fun v : V => C v = (0 : Fin 2)))
  have hsmall : ∃ c : Fin 2,
      2 * ((Finset.univ : Finset V).filter (fun v => C v = c)).card ≤
        Fintype.card V := by
    by_cases hAB : A.card ≤ B.card
    · refine ⟨0, ?_⟩
      change 2 * A.card ≤ Fintype.card V
      omega
    · refine ⟨1, ?_⟩
      change 2 * B.card ≤ Fintype.card V
      omega
  obtain ⟨c, hsmall⟩ := hsmall
  let T : Finset V := Finset.univ.filter (fun v => C v = c)
  have hTc : G.minDegree ≤ T.card := hclasses c
  have hTsmall : 2 * T.card ≤ Fintype.card V := hsmall
  obtain ⟨R, hRT, hRcard⟩ := Finset.exists_subset_card_eq
    (show G.minDegree - 2 ≤ T.card by omega)
  let S : Finset V := T \ R
  have hScard : S.card + R.card = T.card :=
    Finset.card_sdiff_add_card_eq_card hRT
  have hSpos : 0 < S.card := by omega
  have hS : S.Nonempty := Finset.card_pos.mp hSpos
  have hstop : ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
      ∀ u ∈ S, G.Adj v u → u = w) := by
    rintro ⟨v, w, hw, hvw, hunique⟩
    have hwT : w ∈ T := (Finset.mem_sdiff.mp hw).1
    have hwc : C w = c := (Finset.mem_filter.mp hwT).2
    have hvc : C v ≠ c := by
      simpa only [hwc] using C.valid hvw
    have hnT : G.neighborFinset v ⊆ T := hn v c hvc
    have hnR : G.neighborFinset v ⊆ insert w R := by
      intro u hu
      by_cases huR : u ∈ R
      · exact Finset.mem_insert_of_mem huR
      · have huS : u ∈ S := Finset.mem_sdiff.mpr ⟨hnT hu, huR⟩
        have hvu : G.Adj v u := by
          simpa only [SimpleGraph.mem_neighborFinset] using hu
        exact Finset.mem_insert.mpr (Or.inl (hunique u huS hvu))
    have hdegree : G.degree v ≤ R.card + 1 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        (Finset.card_le_card hnR).trans (Finset.card_insert_le w R)
    have hm := G.minDegree_le_degree v
    omega
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S =>
      S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
        ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hwne : weights.Nonempty := by simp [weights]
  have hmember : S.card ∈ weights := by
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS, hstop⟩, rfl⟩
  have hmin : weights.min' hwne ≤ S.card :=
    Finset.min'_le weights S.card hmember
  have hradius : (weights.min' hwne - 1) + G.minDegree ≤ T.card + 1 := by
    omega
  have hradius_real :
      ((weights.min' hwne - 1 : ℕ) : ℝ) + (G.minDegree : ℝ) ≤
        (T.card : ℝ) + 1 := by
    exact_mod_cast hradius
  have hhalf : (T.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by
    have hreal : (2 : ℝ) * (T.card : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hTsmall
    linarith
  have hfloor : (T.card : ℤ) ≤ Int.floor ((Fintype.card V : ℝ) / 2) := by
    apply Int.le_floor.mpr
    simpa only [Int.cast_natCast] using hhalf
  have hfloor_real :
      (T.card : ℝ) ≤ (Int.floor ((Fintype.card V : ℝ) / 2) : ℝ) := by
    exact_mod_cast hfloor
  change ((weights.min' hwne - 1 : ℕ) : ℝ) + (G.minDegree : ℝ) ≤
    (Int.floor ((Fintype.card V : ℝ) / 2) : ℝ) + 1
  linarith only [hradius_real, hfloor_real]
