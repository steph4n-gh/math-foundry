import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

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

theorem model_a4e25367cbc12335da94 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (G.minDegree : ℝ)) + (G.maxDegree : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  change ((weights.min' hw - 1 : ℕ) : ℝ) + (G.minDegree : ℝ) + (G.maxDegree : ℝ) ≤ (Fintype.card V : ℝ) + 1
  have hδ : 2 ≤ G.minDegree := by
    by_contra h
    have hn : G.minDegree ≤ 1 := by omega
    have hr : (G.minDegree : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith [h_guard.2.1]
  have hV : Nonempty V := by
    rcases isEmpty_or_nonempty V with he | hn
    · letI : IsEmpty V := he
      have hz : G.minDegree = 0 := G.minDegree_of_subsingleton
      omega
    · exact hn
  letI : Nonempty V := hV
  obtain ⟨C⟩ : Nonempty (G.Coloring (Fin 2)) := h_guard.1
  obtain ⟨p, hp⟩ := G.exists_maximal_degree_vertex
  have hsame {v w u : V} (hvw : G.Adj v w) (hvu : G.Adj v u) : C w = C u := by
    have hwne : (C v).val ≠ (C w).val := by
      intro h
      exact C.valid hvw (Fin.ext h)
    have hune : (C v).val ≠ (C u).val := by
      intro h
      exact C.valid hvu (Fin.ext h)
    have hvlt := (C v).isLt
    have hwlt := (C w).isLt
    have hult := (C u).isLt
    apply Fin.ext
    omega
  let A : Finset V := Finset.univ.filter (fun v => C v = C p)
  let B : Finset V := Finset.univ \ A
  have hpdeg : 0 < G.degree p := by
    have h := G.minDegree_le_degree p
    omega
  obtain ⟨q, hpq⟩ := (G.degree_pos_iff_exists_adj p).mp hpdeg
  have hqA : G.neighborFinset q ⊆ A := by
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (hsame hpq.symm ((G.mem_neighborFinset q u).mp hu)).symm
  have hδA : G.minDegree ≤ A.card := by
    calc
      G.minDegree ≤ G.degree q := G.minDegree_le_degree q
      _ = (G.neighborFinset q).card := rfl
      _ ≤ A.card := Finset.card_le_card hqA
  have hpB : G.neighborFinset p ⊆ B := by
    intro u hu
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro huA
    have hc : C u = C p := (Finset.mem_filter.mp huA).2
    exact C.valid ((G.mem_neighborFinset p u).mp hu) hc.symm
  have hmax : G.maxDegree ≤ B.card := by
    rw [hp]
    exact Finset.card_le_card hpB
  have hpart : B.card + A.card = Fintype.card V := by
    simpa only [B, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hremove : G.minDegree - 2 ≤ A.card := by omega
  obtain ⟨D, hDA, hDcard⟩ := Finset.exists_subset_card_eq hremove
  let S : Finset V := A \ D
  have hScard : S.card + D.card = A.card := by
    simpa only [S] using Finset.card_sdiff_add_card_eq_card hDA
  have hSadd : S.card + G.minDegree = A.card + 2 := by omega
  have hSnonempty : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hSstop : S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w) := by
    refine ⟨hSnonempty, ?_⟩
    rintro ⟨v, w, hwS, hvw, huniq⟩
    have hwA : w ∈ A := (Finset.mem_sdiff.mp hwS).1
    have hwcol : C w = C p := (Finset.mem_filter.mp hwA).2
    have hsub : G.neighborFinset v ⊆ insert w D := by
      intro u hu
      have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu
      have huA : u ∈ A := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact (hsame hvw hvu).symm.trans hwcol
      by_cases huD : u ∈ D
      · exact Finset.mem_insert.mpr (Or.inr huD)
      · have huS : u ∈ S := Finset.mem_sdiff.mpr ⟨huA, huD⟩
        exact Finset.mem_insert.mpr (Or.inl (huniq u huS hvu))
    have hdeg : G.degree v ≤ D.card + 1 := by
      calc
        G.degree v = (G.neighborFinset v).card := rfl
        _ ≤ (insert w D).card := Finset.card_le_card hsub
        _ ≤ D.card + 1 := Finset.card_insert_le w D
    have hlow := G.minDegree_le_degree v
    omega
  have hminS : weights.min' hw ≤ S.card := by
    apply Finset.min'_le
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSstop⟩, rfl⟩))
  have hnat : weights.min' hw - 1 + G.minDegree + G.maxDegree ≤ Fintype.card V + 1 := by
    omega
  exact_mod_cast hnat

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

theorem composed_98f6a5db9b7b63f3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  exact le_trans (parity_code_unique_neighbor_distance G) (hull3d_parity_code_distance_le_0_1_unique_neighbor_radius_order_1_709dc59dd02e G)

theorem model_a659fd0df8bac9fe2f61 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) + (Gᶜ.cliqueNum : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    let t : Finset V := Finset.univ \ s
    have hcolor : G.Coloring (Option ↥t) := by
      refine SimpleGraph.Coloring.mk
        (fun v => if hv : v ∈ s then none else some ⟨v, by simp [t, hv]⟩) ?_
      intro v w hadj
      by_cases hv : v ∈ s
      · by_cases hw : w ∈ s
        · exact False.elim
            (((SimpleGraph.compl_adj G v w).mp
              (hs.isClique hv hw hadj.ne)).2 hadj)
        · simp [hv, hw]
      · by_cases hw : w ∈ s
        · simp [hv, hw]
        · simpa only [dif_neg hv, dif_neg hw, ne_eq,
            Option.some.injEq, Subtype.mk.injEq] using hadj.ne
    have hn : G.chromaticNumber.toNat ≤ t.card + 1 := by
      simpa only [Fintype.card_option, Fintype.card_coe] using
        (ENat.toNat_le_of_le_natCast hcolor.colorable.chromaticNumber_le)
    have hcard : t.card + Gᶜ.cliqueNum = Fintype.card V := by
      simpa only [t, hs.card_eq, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hnat : G.chromaticNumber.toNat + Gᶜ.cliqueNum ≤ Fintype.card V + 1 := by
      omega
    exact_mod_cast hnat

theorem model_f62f129648dab0844b7e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  classical
  let K : Submodule (ZMod 2) (V → ZMod 2) :=
    LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (Module.finrank (ZMod 2) K : ℝ) + (d : ℝ) ≤
    (Fintype.card V : ℝ) + 1
  have hdpos : 1 ≤ d := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have heq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact hammingNorm_pos_iff.mpr (Finset.mem_filter.mp hx).2.1
  have hdle : d ≤ Fintype.card V + 1 :=
    Finset.min'_le _ _ (by simp [weights])
  have hsub : d - 1 ≤ (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hsub
  let t : Finset V := Finset.univ \ s
  let f : K →ₗ[ZMod 2] (↥t → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) v
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    change (x : V → ZMod 2) = 0
    by_contra hxne
    have hmem : hammingNorm (x : V → ZMod 2) ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨(x : V → ZMod 2), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hxne, ?_⟩
      exact LinearMap.mem_ker.mp x.property
    have hmin : d ≤ hammingNorm (x : V → ZMod 2) :=
      Finset.min'_le _ _ hmem
    have hsupp :
        (Finset.univ.filter (fun v => (x : V → ZMod 2) v ≠ 0)) ⊆ s := by
      intro v hv
      by_contra hvs
      have hvt : v ∈ t := by simp [t, hvs]
      have hzero : (x : V → ZMod 2) v = 0 := by
        exact congrFun hx ⟨v, hvt⟩
      exact (Finset.mem_filter.mp hv).2 hzero
    have hweight : hammingNorm (x : V → ZMod 2) ≤ s.card :=
      Finset.card_le_card hsupp
    omega
  have hk : Module.finrank (ZMod 2) K ≤ t.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      (LinearMap.finrank_le_finrank_of_injective (f := f) hf)
  have hcards : t.card + s.card = Fintype.card V := by
    simpa only [t, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card hs
  have hn : Module.finrank (ZMod 2) K + d ≤ Fintype.card V + 1 := by
    omega
  exact_mod_cast hn
theorem model_6609825288e9b0c185f3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (G.minDegree : ℝ)) ≤ ((Fintype.card V : ℝ) + (1 : ℝ)) := by
  sorry
