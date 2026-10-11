import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic





open scoped BigOperators
theorem model_cd7c90572aced445fec8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.chromaticNumber.toNat : ℝ) ≥ (39999999 / 10000000 : ℝ)))) :
    (((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) + (1 : ℝ)) ≥ ((((G.chromaticNumber.toNat : ℝ) - (1 : ℝ)) * ((G.chromaticNumber.toNat : ℝ) - (2 : ℝ))) / (2 : ℝ)) := by
  classical
  let k : ℕ := G.chromaticNumber.toNat
  have hk : 4 ≤ k := by
    by_contra h
    have h3 : k ≤ 3 := by omega
    have h3R : (k : ℝ) ≤ 3 := by exact_mod_cast h3
    have hg : (39999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2
    linarith only [h3R, hg]
  have hr : 0 < k - 1 := by omega
  have hnot : ¬G.Colorable (k - 1) := by
    intro hc
    have hle : k ≤ k - 1 := ENat.toNat_le_of_le_natCast hc.chromaticNumber_le
    omega
  have hbad : ¬(G.induce (↑(Finset.univ : Finset V) : Set V)).Colorable (k - 1) := by
    rintro ⟨c⟩
    apply hnot
    refine ⟨SimpleGraph.Coloring.mk (fun v : V => c ⟨v, Finset.mem_univ v⟩) ?_⟩
    intro v w h
    exact c.valid h
  have hex : ∃ n : ℕ, ∃ s : Finset V, s.card = n ∧
      ¬(G.induce (↑s : Set V)).Colorable (k - 1) :=
    ⟨_, Finset.univ, rfl, hbad⟩
  obtain ⟨s, hs, hnc⟩ := Nat.find_spec hex
  have hmin (t : Finset V) (ht : t.card < s.card) :
      (G.induce (↑t : Set V)).Colorable (k - 1) := by
    by_contra hnt
    have hle : Nat.find hex ≤ t.card := Nat.find_min' hex ⟨t, rfl, hnt⟩
    omega
  let H : SimpleGraph (↑s : Set V) := G.induce (↑s : Set V)
  have hscard : Fintype.card (↑s : Set V) = s.card := Fintype.card_coe s
  have hn : k ≤ Fintype.card (↑s : Set V) := by
    by_contra h
    have hle : Fintype.card (↑s : Set V) ≤ k - 1 := by omega
    exact hnc (SimpleGraph.Colorable.mono hle H.colorable_of_fintype)
  have hncard : k ≤ s.card := by rwa [hscard] at hn
  letI : Nonempty (↑s : Set V) := Fintype.card_pos_iff.mp (by
    rw [hscard]
    omega)
  have hdeg (v : (↑s : Set V)) : k - 1 ≤ H.degree v := by
    by_contra hv
    have hvlt : H.degree v < k - 1 := by omega
    have herase : (s.erase v.val).card < s.card :=
      Finset.card_erase_lt_of_mem v.property
    obtain ⟨c⟩ := hmin (s.erase v.val) herase
    let f : (↑s : Set V) → Fin (k - 1) := fun w =>
      if h : w.val = v.val then ⟨0, hr⟩
      else c ⟨w.val, Finset.mem_erase.mpr ⟨h, w.property⟩⟩
    have himage : ((H.neighborFinset v).image f).card <
        (Finset.univ : Finset (Fin (k - 1))).card := by
      calc
        ((H.neighborFinset v).image f).card ≤ H.degree v := Finset.card_image_le
        _ < k - 1 := hvlt
        _ = (Finset.univ : Finset (Fin (k - 1))).card := by simp
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card himage
    apply hnc
    refine ⟨SimpleGraph.Coloring.mk (G := H)
      (fun w => if w = v then a else f w) ?_⟩
    intro x y hxy
    by_cases hx : x = v
    · subst x
      have hy : y ≠ v := hxy.ne.symm
      have hym : y ∈ H.neighborFinset v := by
        simpa only [SimpleGraph.mem_neighborFinset] using hxy
      have hya : f y ≠ a := by
        intro h
        exact ha (Finset.mem_image.mpr ⟨y, hym, h⟩)
      simpa only [if_pos rfl, if_neg hy, ite_true] using hya.symm
    · by_cases hy : y = v
      · subst y
        have hxm : x ∈ H.neighborFinset v := by
          simpa only [SimpleGraph.mem_neighborFinset] using hxy.symm
        have hxa : f x ≠ a := by
          intro h
          exact ha (Finset.mem_image.mpr ⟨x, hxm, h⟩)
        simpa only [if_neg hx, if_pos rfl, ite_true] using hxa
      · have hxval : x.val ≠ v.val := fun h => hx (Subtype.ext h)
        have hyval : y.val ≠ v.val := fun h => hy (Subtype.ext h)
        have hcxy :
            c ⟨x.val, Finset.mem_erase.mpr ⟨hxval, x.property⟩⟩ ≠
            c ⟨y.val, Finset.mem_erase.mpr ⟨hyval, y.property⟩⟩ := c.valid hxy
        simpa only [if_neg hx, if_neg hy, f, dif_neg hxval, dif_neg hyval] using hcxy
  have hsum : s.card * (k - 1) ≤ 2 * H.edgeFinset.card := by
    calc
      s.card * (k - 1) = ∑ v : (↑s : Set V), (k - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, hscard,
          Nat.nsmul_eq_mul]
      _ ≤ ∑ v : (↑s : Set V), H.degree v :=
        Finset.sum_le_sum (fun v _ => hdeg v)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  obtain ⟨T, hTG, hT⟩ := h_guard.1.exists_isTree_le
  have hcore : (G.edgeFinset ∩ s.sym2).card = H.edgeFinset.card := by
    simpa only [SimpleGraph.filter_edgeFinset_toFinset_subset, H] using
      (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := G) s)
  have hTcore : (T.edgeFinset ∩ s.sym2).card =
      (T.induce (↑s : Set V)).edgeFinset.card := by
    simpa only [SimpleGraph.filter_edgeFinset_toFinset_subset] using
      (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := T) s)
  obtain ⟨U, hTU, _, hU⟩ :=
    (SimpleGraph.connected_top (V := (↑s : Set V))).exists_isTree_le_of_le_of_isAcyclic
      (H := T.induce (↑s : Set V)) le_top (hT.isAcyclic.induce (↑s : Set V))
  have htin : (T.edgeFinset ∩ s.sym2).card + 1 ≤ s.card := by
    have hle : (T.induce (↑s : Set V)).edgeFinset.card ≤ U.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hTU)
    have hu : U.edgeFinset.card + 1 = s.card := by
      simpa only [hscard] using hU.card_edgeFinset
    omega
  have hsub : T.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hTG
  have hsd := Finset.card_sdiff_add_card_eq_card hsub
  have htcard := hT.card_edgeFinset
  have hcsub :
      (G.edgeFinset ∩ s.sym2) \ (T.edgeFinset ∩ s.sym2) ⊆
        G.edgeFinset \ T.edgeFinset := by
    intro e he
    obtain ⟨heg, het⟩ := Finset.mem_sdiff.mp he
    obtain ⟨heg, hes⟩ := Finset.mem_inter.mp heg
    refine Finset.mem_sdiff.mpr ⟨heg, ?_⟩
    intro het'
    exact het (Finset.mem_inter.mpr ⟨het', hes⟩)
  have hcle := Finset.card_le_card hcsub
  have hcover := Finset.card_le_card_sdiff_add_card
    (s := G.edgeFinset ∩ s.sym2) (t := T.edgeFinset ∩ s.sym2)
  have hboundN : H.edgeFinset.card + Fintype.card V ≤ G.edgeFinset.card + s.card := by
    omega
  have hk1 : 1 ≤ k := by omega
  have hsumR : (s.card : ℝ) * ((k : ℝ) - 1) ≤ 2 * (H.edgeFinset.card : ℝ) := by
    have h : (s.card : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ 2 * (H.edgeFinset.card : ℝ) := by
      exact_mod_cast hsum
    simpa only [Nat.cast_sub hk1, Nat.cast_one] using h
  have hboundR : (H.edgeFinset.card : ℝ) + (Fintype.card V : ℝ) ≤
      (G.edgeFinset.card : ℝ) + (s.card : ℝ) := by exact_mod_cast hboundN
  have hnR : (k : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hncard
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hprod : (0 : ℝ) ≤ ((s.card : ℝ) - (k : ℝ)) * ((k : ℝ) - 3) :=
    mul_nonneg (sub_nonneg.mpr hnR) (by linarith only [hkR])
  change ((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) + 1 ≥
    (((k : ℝ) - 1) * ((k : ℝ) - 2)) / 2
  nlinarith only [hsumR, hboundR, hprod]
