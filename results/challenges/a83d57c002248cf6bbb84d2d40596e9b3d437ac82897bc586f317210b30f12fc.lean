import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic







open scoped BigOperators

theorem model_b2848857e600ffe393f5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  by_cases hc : G.Connected
  · simp only [if_pos hc]
    by_cases hn : 2 ≤ Fintype.card V
    · simp only [dif_pos hn]
      letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let hL := G.isHermitian_lapMatrix ℝ
      let ev := hL.eigenvalues₀
      let e : Fin (Fintype.card V) ≃ V :=
        Fintype.equivOfCardEq (Fintype.card_fin _)
      have heval (i : Fin (Fintype.card V)) :
          hL.eigenvalues (e i) = ev i := by
        simp only [Matrix.IsHermitian.eigenvalues, e, ev, Equiv.symm_apply_apply]
      have hnonneg (i : Fin (Fintype.card V)) : 0 ≤ ev i := by
        rw [← heval i, hL.eigenvalues_eq]
        simpa only [RCLike.re_to_real] using
          (SimpleGraph.posSemidef_lapMatrix ℝ G).dotProduct_mulVec_nonneg
            (⇑(hL.eigenvectorBasis (e i)))
      have hzero : ∃ i : Fin (Fintype.card V), ev i = 0 := by
        have hz : (0 : ℝ) ∈ spectrum ℝ (G.lapMatrix ℝ) :=
          G.zero_mem_spectrum_lapMatrix ℝ
        rw [hL.spectrum_real_eq_range_eigenvalues] at hz
        obtain ⟨v, hv⟩ := hz
        refine ⟨e.symm v, ?_⟩
        simpa only [ev, Matrix.IsHermitian.eigenvalues, e] using hv
      let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
      let second : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
      have hlast : ev last = 0 := by
        obtain ⟨i, hi⟩ := hzero
        have hilast : i ≤ last := by
          change i.val ≤ Fintype.card V - 1
          have hi_lt := i.isLt
          omega
        have hle : ev last ≤ ev i := hL.eigenvalues₀_antitone hilast
        rw [hi] at hle
        exact le_antisymm hle (hnonneg last)
      have hpoint (i : Fin (Fintype.card V))
          (hi : i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last) :
          ev second ≤ ev i := by
        have hne : i.val ≠ Fintype.card V - 1 := by
          intro hv
          exact (Finset.mem_erase.mp hi).1 (Fin.ext hv)
        have hisecond : i ≤ second := by
          change i.val ≤ Fintype.card V - 2
          have hi_lt := i.isLt
          omega
        exact hL.eigenvalues₀_antitone hisecond
      have htrace : (∑ i : Fin (Fintype.card V), ev i) =
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        calc
          (∑ i : Fin (Fintype.card V), ev i) =
              ∑ v : V, hL.eigenvalues v := by
            simpa only [heval] using e.sum_comp hL.eigenvalues
          _ = (G.lapMatrix ℝ).trace := hL.trace_eq_sum_eigenvalues.symm
          _ = ∑ v : V, (G.degree v : ℝ) := by
            simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.trace_sub]
          _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
            exact_mod_cast G.sum_degrees_eq_twice_card_edges
      calc
        ((Fintype.card V : ℝ) - 1) * ev second =
            ∑ _i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last,
              ev second := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_univ last), Finset.card_univ,
            Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
            Nat.cast_one]
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last,
            ev i := Finset.sum_le_sum hpoint
        _ = ∑ i : Fin (Fintype.card V), ev i :=
          Finset.sum_erase (Finset.univ : Finset (Fin (Fintype.card V))) hlast
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := htrace
    · simp only [dif_neg hn, mul_zero]
      exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  · simp only [if_neg hc, mul_zero]
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem model_4a232a5cfb6290dedc16 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (((2 : ℝ) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let K : Submodule (ZMod 2) (V → ZMod 2) :=
    LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hdim : 1 < Module.finrank (ZMod 2) K := by
    have hr : (1 : ℝ) < (Module.finrank (ZMod 2) K : ℝ) := by
      dsimp [K]
      linarith only [h_guard.2.2]
    exact_mod_cast hr
  obtain ⟨x, hxK, hx0, hx1⟩ :
      ∃ x : V → ZMod 2, x ∈ K ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have hle : K ≤ Submodule.span (ZMod 2) ({(1 : V → ZMod 2)} : Set (V → ZMod 2)) := by
      intro y hy
      by_cases hy0 : y = 0
      · rw [hy0]
        exact Submodule.zero_mem _
      · have hy1 : y = 1 := by
          by_contra hy1
          exact h ⟨y, hy, hy0, hy1⟩
        rw [hy1]
        exact Submodule.subset_span (by simp)
    have hs : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({(1 : V → ZMod 2)} : Set (V → ZMod 2))) ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod 2)
        ({(1 : V → ZMod 2)} : Set (V → ZMod 2)))
    have hf := Submodule.finrank_mono hle
    omega
  have hxker : (G.adjMatrix (ZMod 2)).mulVecLin x = 0 := hxK
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun y => y ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin y = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  have hmin (y : V → ZMod 2) (hy0 : y ≠ 0)
      (hyk : (G.adjMatrix (ZMod 2)).mulVecLin y = 0) :
      weights.min' hw ≤ hammingNorm y := by
    have hm : hammingNorm y ∈ weights := by
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hy0, hyk⟩⟩, rfl⟩)
    exact Finset.min'_le weights _ hm
  change (2 - ((G.minDegree : ℝ) -
    2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ))) *
    (weights.min' hw : ℝ) ≤ (Fintype.card V : ℝ)
  let q : ℕ := G.minDegree / 2
  have hd : G.minDegree = 2 * q + G.minDegree % 2 := by
    dsimp [q]
    omega
  have hdr : (G.minDegree : ℝ) = 2 * (q : ℝ) + ((G.minDegree % 2 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((G.minDegree % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrlt : ((G.minDegree % 2 : ℕ) : ℝ) < 2 := by
    exact_mod_cast (Nat.mod_lt G.minDegree (by decide : 0 < (2 : ℕ)))
  have hfloor : Int.floor ((G.minDegree : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith only [hdr, hr0, hrlt]
  have hfac : (2 : ℝ) - ((G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ)) =
      2 - ((G.minDegree % 2 : ℕ) : ℝ) := by
    rw [hfloor]
    push_cast
    linarith only [hdr]
  rw [hfac]
  rcases Nat.mod_two_eq_zero_or_one G.minDegree with he | ho
  · simp only [he, Nat.cast_zero, sub_zero]
    have hV : Nonempty V := by
      by_contra h
      letI : IsEmpty V := not_nonempty_iff.mp h
      apply hx0
      funext v
      exact isEmptyElim v
    letI : Nonempty V := hV
    obtain ⟨d, hreg⟩ := h_guard.1
    have hdeg : ∀ v, G.degree v = G.minDegree :=
      fun v => (hreg v).trans hreg.minDegree_eq.symm
    have hz : (G.minDegree : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr he)
    have hone : (G.adjMatrix (ZMod 2)).mulVecLin (1 : V → ZMod 2) = 0 := by
      ext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2))
        (Function.const V (1 : ZMod 2))) v = 0
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hdeg v, hz, mul_one]
    have hy0 : (1 : V → ZMod 2) - x ≠ 0 := by
      intro hy
      apply hx1
      exact (sub_eq_zero.mp hy).symm
    have hyker : (G.adjMatrix (ZMod 2)).mulVecLin ((1 : V → ZMod 2) - x) = 0 := by
      rw [map_sub, hone, hxker, sub_self]
    have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
      intro a
      have hv : a.val = 0 ∨ a.val = 1 := by
        have ht := ZMod.val_lt a
        omega
      rcases hv with ha | ha
      · exact Or.inl ((ZMod.val_eq_zero a).mp ha)
      · right
        simpa only [ha, Nat.cast_one] using (ZMod.natCast_zmod_val a).symm
    have hcompl (v : V) :
        (((1 : V → ZMod 2) - x) v ≠ 0) ↔ ¬ (x v ≠ 0) := by
      rcases hbits (x v) with hv | hv <;> simp [Pi.sub_apply, hv]
    have hsum : hammingNorm x + hammingNorm ((1 : V → ZMod 2) - x) = Fintype.card V := by
      simp only [hammingNorm]
      simp_rw [hcompl]
      simpa only [Finset.card_univ] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
          (fun v => x v ≠ 0))
    have hb : 2 * weights.min' hw ≤ Fintype.card V := by
      have hfirst := hmin x hx0 hxker
      have hsecond := hmin ((1 : V → ZMod 2) - x) hy0 hyker
      omega
    exact_mod_cast hb
  · have hb : weights.min' hw ≤ Fintype.card V :=
      (hmin x hx0 hxker).trans (hammingNorm_le_card_fintype (x := x))
    have hfac1 : (2 : ℝ) - ((G.minDegree % 2 : ℕ) : ℝ) = 1 := by
      rw [ho]
      norm_num
    rw [hfac1, one_mul]
    exact_mod_cast hb

theorem model_6c69a9fac94e8d24072f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ))) + (max (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) (((2 : ℝ) * (G.minDegree : ℝ)) - (2 : ℝ)))) ≤ (Fintype.card V : ℝ) := by
  let d := G.minDegree
  have hd : 2 ≤ d := by
    by_contra h
    have hn : G.minDegree ≤ 1 := by
      change d ≤ 1
      omega
    have hr : (G.minDegree : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith [h_guard.2.2.1]
  haveI : Nonempty V := by
    rcases isEmpty_or_nonempty V with h | h
    · letI : IsEmpty V := h
      have hz : d = 0 := by
        change G.minDegree = 0
        simp
      omega
    · exact h
  obtain ⟨C⟩ := h_guard.1
  have htwo : ∀ c : Fin 2, c = 0 ∨ c = 1 := by
    intro c
    fin_cases c <;> simp
  have hcolor : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b = c := by
    intro a b c hab hac
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    apply Fin.ext
    omega
  have hsame : ∀ {v w u : V}, G.Adj v w → G.Adj v u → C w = C u := by
    intro v w u hvw hvu
    exact hcolor _ _ _ (C.valid hvw) (C.valid hvu)
  let Stop : Finset V → Prop := fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter Stop).image Finset.card
  have hW : weights.Nonempty := by simp [weights]
  let s := weights.min' hW
  let k := s - 1
  have hs : 1 ≤ s := by
    change 1 ≤ weights.min' hW
    refine Finset.le_min' weights hW 1 ?_
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have he : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      have hStop : Stop S := (Finset.mem_filter.mp hS).2
      exact Finset.card_pos.mpr hStop.1
  have hk : k + 1 = s := by
    change s - 1 + 1 = s
    omega
  have hstop : ∀ S : Finset V, Stop S → s ≤ S.card := by
    intro S hS
    change weights.min' hW ≤ S.card
    apply Finset.min'_le
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩)
  have hsmall : ∀ S : Finset V, S.Nonempty → S.card ≤ k → ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    intro S hne hcard
    by_contra h
    have hh := hstop S ⟨hne, h⟩
    omega
  let A : Fin 2 → Finset V := fun c => Finset.univ.filter (fun v => C v = c)
  have hmem : ∀ (c : Fin 2) (v : V), v ∈ A c ↔ C v = c := by
    intro c v
    simp [A]
  have hdisj : Disjoint (A 0) (A 1) := by
    refine Finset.disjoint_left.mpr ?_
    intro v h0 h1
    have he : (0 : Fin 2) = 1 := ((hmem 0 v).mp h0).symm.trans ((hmem 1 v).mp h1)
    exact (by decide : (0 : Fin 2) ≠ 1) he
  have hcover : A 0 ∪ A 1 = Finset.univ := by
    ext v
    simp only [Finset.mem_union, hmem, Finset.mem_univ, iff_true]
    exact htwo (C v)
  have hpart : (A 0).card + (A 1).card = Fintype.card V := by
    calc
      (A 0).card + (A 1).card = (A 0 ∪ A 1).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = Fintype.card V := by rw [hcover, Finset.card_univ]
  have hbig : ∀ c : Fin 2, d ≤ (A c).card := by
    intro c
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : 0 < G.degree v := by
      have hh := G.minDegree_le_degree v
      change d ≤ G.degree v at hh
      omega
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
    have hex : ∃ z : V, C z ≠ c := by
      by_cases hc : C v = c
      · refine ⟨w, ?_⟩
        intro h
        exact C.valid hw (hc.trans h.symm)
      · exact ⟨v, hc⟩
    obtain ⟨z, hz⟩ := hex
    calc
      d ≤ G.degree z := G.minDegree_le_degree z
      _ = (G.neighborFinset z).card := (G.card_neighborFinset_eq_degree z).symm
      _ ≤ (A c).card := Finset.card_le_card (by
        intro u hu
        exact (hmem c u).mpr (hcolor _ _ _ (C.valid ((G.mem_neighborFinset z u).mp hu)) hz))
  have hbound : ∀ c : Fin 2, k + (d - 1) ≤ (A c).card := by
    intro c
    obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq (show d - 2 ≤ (A c).card by
      have hh := hbig c
      omega)
    let S : Finset V := A c \ D
    have hSc : S.card = (A c).card - (d - 2) := by
      change (A c \ D).card = (A c).card - (d - 2)
      rw [Finset.card_sdiff_of_subset hD, hDc]
    have hSne : S.Nonempty := Finset.card_pos.mp (by
      have hh := hbig c
      omega)
    have hStop : Stop S := by
      refine ⟨hSne, ?_⟩
      rintro ⟨v, w, hw, hvw, huniq⟩
      have hwc : C w = c := (hmem c w).mp (Finset.mem_sdiff.mp hw).1
      have hsub : G.neighborFinset v ⊆ insert w D := by
        intro u hu
        have hvu := (G.mem_neighborFinset v u).mp hu
        have huc : C u = c := (hsame hvw hvu).symm.trans hwc
        by_cases huD : u ∈ D
        · exact Finset.mem_insert_of_mem huD
        · have huS : u ∈ S := Finset.mem_sdiff.mpr ⟨(hmem c u).mpr huc, huD⟩
          have hue : u = w := huniq u huS hvu
          simp [hue]
      have hcard : G.degree v ≤ D.card + 1 := by
        rw [← G.card_neighborFinset_eq_degree v]
        exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have hh := G.minDegree_le_degree v
      change d ≤ G.degree v at hh
      omega
    have hle := hstop S hStop
    have hh := hbig c
    omega
  have hdegreeNat : 2 * k + 2 * (d - 1) ≤ Fintype.card V := by
    have h0 := hbound 0
    have h1 := hbound 1
    omega
  have hdegree : (2 : ℝ) * (k : ℝ) + (2 * (d : ℝ) - 2) ≤ (Fintype.card V : ℝ) := by
    have hr : (2 : ℝ) * (k : ℝ) + 2 * ((d - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hdegreeNat
    rw [Nat.cast_sub (by omega : 1 ≤ d)] at hr
    norm_num at hr
    linarith
  obtain ⟨T0, hT0, hT0c⟩ := Finset.exists_subset_card_eq (show k ≤ (A 0).card by
    have hh := hbound 0
    omega)
  obtain ⟨T1, hT1, hT1c⟩ := Finset.exists_subset_card_eq (show k ≤ (A 1).card by
    have hh := hbound 1
    omega)
  let T := T0 ∪ T1
  have hTdisj : Disjoint T0 T1 := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv0 hv1
    exact (Finset.disjoint_left.mp hdisj) (hT0 hv0) (hT1 hv1)
  have hTc : T.card = 2 * k := by
    change (T0 ∪ T1).card = 2 * k
    rw [Finset.card_union_of_disjoint hTdisj, hT0c, hT1c]
    omega
  have hTcolor0 : ∀ v : V, v ∈ T0 → C v = 0 := fun v hv => (hmem 0 v).mp (hT0 hv)
  have hTcolor1 : ∀ v : V, v ∈ T1 → C v = 1 := fun v hv => (hmem 1 v).mp (hT1 hv)
  have hcap : ∀ c : Fin 2, (T.filter (fun v => C v = c)).card ≤ k := by
    intro c
    rcases htwo c with rfl | rfl
    · have hsub : T.filter (fun v => C v = 0) ⊆ T0 := by
        intro v hv
        obtain ⟨hvT, hc⟩ := Finset.mem_filter.mp hv
        rcases Finset.mem_union.mp hvT with h | h
        · exact h
        · have he : (0 : Fin 2) = 1 := hc.symm.trans (hTcolor1 v h)
          exact ((by decide : (0 : Fin 2) ≠ 1) he).elim
      exact (Finset.card_le_card hsub).trans_eq hT0c
    · have hsub : T.filter (fun v => C v = 1) ⊆ T1 := by
        intro v hv
        obtain ⟨hvT, hc⟩ := Finset.mem_filter.mp hv
        rcases Finset.mem_union.mp hvT with h | h
        · have he : (1 : Fin 2) = 0 := hc.symm.trans (hTcolor0 v h)
          exact ((by decide : (1 : Fin 2) ≠ 0) he).elim
        · exact h
      exact (Finset.card_le_card hsub).trans_eq hT1c
  let L := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker L
  have hzero : ∀ x : K, (∀ v : V, v ∉ T → x.1 v = 0) → x.1 = 0 := by
    intro x hx
    by_contra hneq
    have hex : ∃ w : V, x.1 w ≠ 0 := by
      by_contra h
      apply hneq
      funext w
      have hh : ¬ x.1 w ≠ 0 := fun hw => h ⟨w, hw⟩
      exact not_not.mp hh
    obtain ⟨w, hw⟩ := hex
    let S : Finset V := Finset.univ.filter (fun u => x.1 u ≠ 0 ∧ C u = C w)
    have hSne : S.Nonempty := ⟨w, by simp [S, hw]⟩
    have hScard : S.card ≤ k := by
      calc
        S.card ≤ (T.filter (fun u => C u = C w)).card := Finset.card_le_card (by
          intro u hu
          have hup : x.1 u ≠ 0 ∧ C u = C w := (Finset.mem_filter.mp hu).2
          refine Finset.mem_filter.mpr ⟨?_, hup.2⟩
          by_contra hut
          exact hup.1 (hx u hut))
        _ ≤ k := hcap (C w)
    obtain ⟨v, u, hu, hvu, huniq⟩ := hsmall S hSne hScard
    have hxu : x.1 u ≠ 0 := (Finset.mem_filter.mp hu).2.1
    have huc : C u = C w := (Finset.mem_filter.mp hu).2.2
    have heval : L x.1 v = x.1 u := by
      change (∑ t : V, G.adjMatrix (ZMod 2) v t * x.1 t) = x.1 u
      rw [Finset.sum_eq_single u]
      · simp [hvu]
      · intro t ht htu
        by_cases hvt : G.Adj v t
        · have hxt : x.1 t = 0 := by
            by_contra hh
            have htc : C t = C w := (hsame hvu hvt).symm.trans huc
            have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ t, hh, htc⟩
            exact htu (huniq t htS hvt)
          simp [hxt]
        · simp [hvt]
      · intro h
        exact (h (Finset.mem_univ u)).elim
    have hz : L x.1 = 0 := LinearMap.mem_ker.mp x.2
    exact hxu (heval.symm.trans (congrFun hz v))
  let P : K →ₗ[ZMod 2] ({v : V // v ∉ T} → ZMod 2) :=
    { toFun := fun x v => x.1 v.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : Function.Injective P := by
    intro x y hxy
    apply Subtype.ext
    have hz : (x - y).1 = 0 := hzero (x - y) (by
      intro v hv
      have he := congrFun hxy ⟨v, hv⟩
      change x.1 v = y.1 v at he
      change x.1 v - y.1 v = 0
      exact sub_eq_zero.mpr he)
    change x.1 - y.1 = 0 at hz
    exact sub_eq_zero.mp hz
  have hdim : Module.finrank (ZMod 2) K ≤ Fintype.card V - 2 * k := by
    calc
      _ ≤ Module.finrank (ZMod 2) ({v : V // v ∉ T} → ZMod 2) := LinearMap.finrank_le_finrank_of_injective hP
      _ = Fintype.card {v : V // v ∉ T} := Module.finrank_fintype_fun_eq_card (ZMod 2)
      _ = Fintype.card V - 2 * k := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, hTc]
  have hkn : 2 * k ≤ Fintype.card V := by
    rw [← hTc]
    exact Finset.card_le_univ T
  have hnullNat : 2 * k + Module.finrank (ZMod 2) K ≤ Fintype.card V := by omega
  have hnull : (2 : ℝ) * (k : ℝ) + (Module.finrank (ZMod 2) K : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hnullNat
  change (2 : ℝ) * (k : ℝ) + max (Module.finrank (ZMod 2) K : ℝ) (2 * (d : ℝ) - 2) ≤ (Fintype.card V : ℝ)
  rcases le_total (Module.finrank (ZMod 2) K : ℝ) (2 * (d : ℝ) - 2) with h | h
  · rw [max_eq_right h]
    exact hdegree
  · rw [max_eq_left h]
    exact hnull

theorem model_5e76b721dff9cc8391a8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) * ((1 : ℝ) - (Real.exp (((-(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) K
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (4 : ℝ) * (d : ℝ) *
    (1 - Real.exp ((-(k : ℝ) / 2) * Real.log (1 + (1 : ℝ)))) ≤
      (Fintype.card V : ℝ)
  rw [show (1 + (1 : ℝ)) = 2 by norm_num]
  have hkg : (9999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.2
  have hkpos : 0 < k := by
    have hh : (0 : ℝ) < (k : ℝ) := by linarith only [hkg]
    exact_mod_cast hh
  have hkn : k ≤ Fintype.card V := by
    calc
      k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le K
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hn : 0 < Fintype.card V := lt_of_lt_of_le hkpos hkn
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨r, hr⟩ := h_guard.2.1
  have hrpos : 0 < r := by
    have hh : (9999999 / 10000000 : ℝ) ≤ (r : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.2.1
    have hh' : (0 : ℝ) < (r : ℝ) := by linarith only [hh]
    exact_mod_cast hh'
  obtain ⟨c⟩ := h_guard.1
  let s : Finset V := Finset.univ.filter (fun v => c v = 0)
  have hcolors : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ b ≠ 0) := by decide
  have hopp {v w : V} (hvw : G.Adj v w) : v ∈ s ↔ w ∉ s := by
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
      hcolors (c v) (c w) (c.valid hvw)
  have hB : G.IsBipartiteWith (s : Set V) ((sᶜ : Finset V) : Set V) := by
    refine ⟨?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro v hv ht
      exact (Finset.mem_compl.mp ht) hv
    · intro v w hvw
      by_cases hv : v ∈ s
      · exact Or.inl ⟨hv, Finset.mem_compl.mpr ((hopp hvw).mp hv)⟩
      · exact Or.inr ⟨Finset.mem_compl.mpr hv, (hopp hvw.symm).mpr hv⟩
  have heq : s.card * r = (sᶜ).card * r := by
    simpa only [hr.degree_eq, Finset.sum_const, Nat.nsmul_eq_mul] using
      (SimpleGraph.isBipartiteWith_sum_degrees_eq hB)
  have hcard : s.card = (sᶜ).card := mul_right_cancel₀ hrpos.ne' heq
  have htotal : s.card + (sᶜ).card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hside : 2 * s.card = Fintype.card V := by omega
  have hside' : 2 * (sᶜ).card = Fintype.card V := by omega
  have hproj (x : K) :
      A (fun v => if v ∈ s then (x : V → ZMod 2) v else 0) = 0 := by
    apply funext
    intro v
    change ((G.adjMatrix (ZMod 2)).mulVecLin
      (fun w => if w ∈ s then (x : V → ZMod 2) w else 0)) v = 0
    rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
    by_cases hv : v ∈ s
    · apply Finset.sum_eq_zero
      intro w hw'
      have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
      have hw'' : w ∉ s := (hopp hadj).mp hv
      simp only [if_neg hw'']
    · calc
        _ = ∑ w ∈ G.neighborFinset v, (x : V → ZMod 2) w := by
          apply Finset.sum_congr rfl
          intro w hw'
          have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
          have hw'' : w ∈ s := (hopp hadj.symm).mpr hv
          simp only [if_pos hw'']
        _ = 0 := by
          have hx : A (x : V → ZMod 2) = 0 := x.property
          simpa only [A, Matrix.mulVecLin_apply,
            SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using congrFun hx v
  let T : K →ₗ[ZMod 2] K :=
    { toFun := fun x =>
        ⟨(fun v => if v ∈ s then (x : V → ZMod 2) v else 0), hproj x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext v
        change (if v ∈ s then (x : V → ZMod 2) v + (y : V → ZMod 2) v else 0) =
          (if v ∈ s then (x : V → ZMod 2) v else 0) +
            (if v ∈ s then (y : V → ZMod 2) v else 0)
        by_cases hv : v ∈ s <;> simp [hv]
      map_smul' := by
        intro a x
        apply Subtype.ext
        funext v
        change (if v ∈ s then a • ((x : V → ZMod 2) v) else 0) =
          a • (if v ∈ s then (x : V → ZMod 2) v else 0)
        by_cases hv : v ∈ s <;> simp [hv] }
  have hchoice : ∃ (S : Finset V) (D : Submodule (ZMod 2) K),
      2 * S.card = Fintype.card V ∧
      k ≤ 2 * Module.finrank (ZMod 2) D ∧
      ∀ (x : D) (v : V), v ∉ S → (x.val : V → ZMod 2) v = 0 := by
    have hsplit : Module.finrank (ZMod 2) (LinearMap.range T) +
        Module.finrank (ZMod 2) (LinearMap.ker T) = k :=
      LinearMap.finrank_range_add_finrank_ker T
    by_cases hm : Module.finrank (ZMod 2) (LinearMap.range T) ≤
        Module.finrank (ZMod 2) (LinearMap.ker T)
    · refine ⟨sᶜ, LinearMap.ker T, hside', ?_, ?_⟩
      · omega
      · intro x v hv
        have hv' : v ∈ s := by simpa using hv
        have hh : T x.val = 0 := LinearMap.mem_ker.mp x.property
        have hh' := congrArg (fun z : K => (z : V → ZMod 2) v) hh
        change (if v ∈ s then (x.val : V → ZMod 2) v else 0) = 0 at hh'
        simpa only [if_pos hv'] using hh'
    · refine ⟨s, LinearMap.range T, hside, ?_, ?_⟩
      · omega
      · intro x v hv
        obtain ⟨y, hy⟩ := x.property
        have hh := congrArg (fun z : K => (z : V → ZMod 2) v) hy
        change (if v ∈ s then (y : V → ZMod 2) v else 0) =
          (x.val : V → ZMod 2) v at hh
        simpa only [if_neg hv] using hh.symm
  obtain ⟨S, D, hS, hkD, hsupp⟩ := hchoice
  letI : Fintype D := Fintype.ofFinite D
  let e : D →ₗ[ZMod 2] (V → ZMod 2) := K.subtype.comp D.subtype
  have hd (x : D) (hx : x ≠ 0) : d ≤ hammingNorm (e x) := by
    have hxne : e x ≠ 0 := by
      intro heq'
      apply hx
      apply Subtype.ext
      apply Subtype.ext
      exact heq'
    have hxker : A (e x) = 0 := x.val.property
    have hxmem : e x ∈ (Finset.univ : Finset (V → ZMod 2)).filter
        (fun z => z ≠ 0 ∧ A z = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩
    have hmem : hammingNorm (e x) ∈ weights :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e x, hxmem, rfl⟩))
    exact Finset.min'_le weights (hammingNorm (e x)) hmem
  have hbit : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hcoord (v : V) :
      2 * (Finset.univ.filter (fun x : D => e x v ≠ 0)).card ≤ Fintype.card D := by
    let U : Finset D := Finset.univ.filter (fun x => e x v ≠ 0)
    let W : Finset D := Finset.univ.filter (fun x => e x v = 0)
    change 2 * U.card ≤ Fintype.card D
    by_cases hU : U.Nonempty
    · obtain ⟨a, ha⟩ := hU
      have ha1 : e a v = 1 := hbit _ (Finset.mem_filter.mp ha).2
      have hUW : U.card ≤ W.card := by
        apply Finset.card_le_card_of_injOn (fun x : D => x + a)
        · intro x hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hx1 : e x v = 1 := hbit _ (Finset.mem_filter.mp hx).2
          change e (x + a) v = 0
          rw [map_add, Pi.add_apply, hx1, ha1]
          decide
        · intro x hx y hy hxy
          exact add_right_cancel hxy
      have hpartition : U.card + W.card = Fintype.card D := by
        simpa [U, W] using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset D)) (fun x : D => e x v ≠ 0))
      omega
    · have hzero : U.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
      simp [hzero]
  have hsum : (∑ x : D, hammingNorm (e x)) =
      ∑ v : V, (Finset.univ.filter (fun x : D => e x v ≠ 0)).card := by
    simp only [hammingNorm, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hupper : 2 * (∑ x : D, hammingNorm (e x)) ≤
      S.card * Fintype.card D := by
    rw [hsum, Finset.mul_sum]
    calc
      _ ≤ ∑ v : V, if v ∈ S then Fintype.card D else 0 := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvS : v ∈ S
        · simpa only [if_pos hvS] using hcoord v
        · have hzero : Finset.univ.filter (fun x : D => e x v ≠ 0) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro x hx
            exact fun h => h (hsupp x v hvS)
          simp [hvS, hzero]
      _ = S.card * Fintype.card D := by
        rw [Finset.sum_ite]
        simp [Finset.filter_mem_eq_inter, Nat.nsmul_eq_mul]
  have hlower : (Fintype.card D - 1) * d ≤ ∑ x : D, hammingNorm (e x) := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset D).erase 0, d := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ (0 : D)), Finset.card_univ]
      _ ≤ ∑ x ∈ (Finset.univ : Finset D).erase 0, hammingNorm (e x) :=
        Finset.sum_le_sum (fun x hx => hd x ((Finset.mem_erase.mp hx).1))
      _ = ∑ x : D, hammingNorm (e x) :=
        Finset.sum_erase (Finset.univ : Finset D)
          (f := fun x : D => hammingNorm (e x)) (a := (0 : D)) (by simp)
  have hbound : 4 * (Fintype.card D - 1) * d ≤
      Fintype.card V * Fintype.card D := by
    calc
      _ = 2 * (2 * ((Fintype.card D - 1) * d)) := by ring
      _ ≤ 2 * (2 * (∑ x : D, hammingNorm (e x))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hlower)
      _ ≤ 2 * (S.card * Fintype.card D) := Nat.mul_le_mul_left 2 hupper
      _ = Fintype.card V * Fintype.card D := by rw [← mul_assoc, hS]
  have hboundR : (4 : ℝ) * ((Fintype.card D - 1 : ℕ) : ℝ) * (d : ℝ) ≤
      (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := by
    exact_mod_cast hbound
  have hm1 : 1 ≤ Fintype.card D := Fintype.card_pos
  rw [Nat.cast_sub hm1, Nat.cast_one] at hboundR
  have hmpos : (0 : ℝ) < (Fintype.card D : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have hscaled :
      (4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹)) * (Fintype.card D : ℝ) ≤
        (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := by
    calc
      _ = 4 * (d : ℝ) *
          ((1 - (Fintype.card D : ℝ)⁻¹) * (Fintype.card D : ℝ)) := by ring
      _ = 4 * ((Fintype.card D : ℝ) - 1) * (d : ℝ) := by
        rw [sub_mul, one_mul, inv_mul_cancel₀ hmpos.ne']
        ring
      _ ≤ (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := hboundR
  have hsmall : 4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹) ≤
      (Fintype.card V : ℝ) := by
    by_contra! h
    exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_right h hmpos)
  letI : Module.Free (ZMod 2) D := Module.Free.of_divisionRing (ZMod 2) D
  have hm : Fintype.card D = 2 ^ Module.finrank (ZMod 2) D := by
    simpa only [ZMod.card, Fintype.card_fin] using
      (Module.card_fintype (Module.finBasis (ZMod 2) D))
  have hmreal : (Fintype.card D : ℝ) =
      (2 : ℝ) ^ Module.finrank (ZMod 2) D := by
    exact_mod_cast hm
  have hexp : Real.exp (-(Module.finrank (ZMod 2) D : ℝ) * Real.log 2) =
      (Fintype.card D : ℝ)⁻¹ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), ← hmreal]
  have hdimR : (k : ℝ) / 2 ≤ (Module.finrank (ZMod 2) D : ℝ) := by
    have hh : (k : ℝ) ≤ 2 * (Module.finrank (ZMod 2) D : ℝ) := by
      exact_mod_cast hkD
    linarith only [hh]
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexple : Real.exp (-(Module.finrank (ZMod 2) D : ℝ) * Real.log 2) ≤
      Real.exp ((-(k : ℝ) / 2) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    have hh : -(Module.finrank (ZMod 2) D : ℝ) ≤ -(k : ℝ) / 2 := by
      linarith only [hdimR]
    exact mul_le_mul_of_nonneg_right hh hlog
  rw [hexp] at hexple
  calc
    (4 : ℝ) * (d : ℝ) * (1 - Real.exp ((-(k : ℝ) / 2) * Real.log 2)) ≤
        4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hexple 1)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    _ ≤ (Fintype.card V : ℝ) := hsmall

theorem model_ceb714b3b8492a9c6002 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) * ((1 : ℝ) - (((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))) * (Real.exp (((-(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ)))))))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (4 : ℝ) * (d : ℝ) *
    (1 - ((G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ)) *
      Real.exp ((-(k : ℝ) / 2) * Real.log (1 + (1 : ℝ)))) ≤ (n : ℝ)
  let q : ℕ := G.minDegree / 2
  have hd : G.minDegree = 2 * q + G.minDegree % 2 := by
    dsimp [q]
    omega
  have hdr : (G.minDegree : ℝ) =
      2 * (q : ℝ) + ((G.minDegree % 2 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((G.minDegree % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrlt : ((G.minDegree % 2 : ℕ) : ℝ) < 2 := by
    exact_mod_cast (Nat.mod_lt G.minDegree (by decide : 0 < (2 : ℕ)))
  have hfloor : Int.floor ((G.minDegree : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith only [hdr, hr0, hrlt]
  have hrem : (G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) =
      ((G.minDegree % 2 : ℕ) : ℝ) := by
    rw [hfloor]
    push_cast
    linarith only [hdr]
  rw [hrem]
  rcases Nat.mod_two_eq_zero_or_one G.minDegree with he | ho
  · simp only [he, Nat.cast_zero, zero_mul, sub_zero, mul_one]
    have hkreal : (29999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.2
    have hk : 3 ≤ k := by
      by_contra h
      have hle : (k : ℝ) ≤ 2 := by
        exact_mod_cast (show k ≤ 2 by omega)
      linarith only [hkreal, hle]
    have hkn : k ≤ n := by
      calc
        k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
        _ = n := Module.finrank_fintype_fun_eq_card (ZMod 2)
    have hn : 0 < Fintype.card V := by
      change 0 < n
      omega
    letI : Nonempty V := Fintype.card_pos_iff.mp hn
    obtain ⟨r, hr⟩ := h_guard.2.1
    have hrpos : 0 < r := by
      have hg : (19999999 / 10000000 : ℝ) ≤ (r : ℝ) := by
        simpa only [hr.minDegree_eq] using h_guard.2.2.1
      have hg' : (0 : ℝ) < (r : ℝ) := by linarith only [hg]
      exact_mod_cast hg'
    have hdeg : ∀ v, G.degree v = G.minDegree :=
      fun v => (hr v).trans hr.minDegree_eq.symm
    have hz : (G.minDegree : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr he)
    have hone : A (1 : V → ZMod 2) = 0 := by
      ext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2))
        (Function.const V (1 : ZMod 2))) v = 0
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hdeg v, hz, mul_one]
    obtain ⟨c⟩ := h_guard.1
    let s : Finset V := Finset.univ.filter (fun v => c v = 0)
    have hcolors : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ b ≠ 0) := by decide
    have hopp {v w : V} (hvw : G.Adj v w) : v ∈ s ↔ w ∉ s := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
        hcolors (c v) (c w) (c.valid hvw)
    have hB : G.IsBipartiteWith (s : Set V) ((sᶜ : Finset V) : Set V) := by
      refine ⟨?_, ?_⟩
      · apply Set.disjoint_left.mpr
        intro v hv ht
        exact (Finset.mem_compl.mp ht) hv
      · intro v w hvw
        by_cases hv : v ∈ s
        · exact Or.inl ⟨hv, Finset.mem_compl.mpr ((hopp hvw).mp hv)⟩
        · exact Or.inr ⟨Finset.mem_compl.mpr hv, (hopp hvw.symm).mpr hv⟩
    have heq : s.card * r = (sᶜ).card * r := by
      simpa only [hr.degree_eq, Finset.sum_const, Nat.nsmul_eq_mul] using
        (SimpleGraph.isBipartiteWith_sum_degrees_eq hB)
    have hcard : s.card = (sᶜ).card := mul_right_cancel₀ hrpos.ne' heq
    have htotal : s.card + (sᶜ).card = n := Finset.card_add_card_compl s
    have hside : 2 * s.card = n := by omega
    have hside' : 2 * (sᶜ).card = n := by omega
    have hoppc {v w : V} (hvw : G.Adj v w) : v ∈ sᶜ ↔ w ∉ sᶜ := by
      simpa only [Finset.mem_compl, not_not] using (not_congr (hopp hvw))
    have hproj (S : Finset V)
        (hSopp : ∀ {v w : V}, G.Adj v w → (v ∈ S ↔ w ∉ S))
        (z : V → ZMod 2) (hzA : A z = 0) :
        A (fun v => if v ∈ S then z v else 0) = 0 := by
      funext v
      change ((G.adjMatrix (ZMod 2)).mulVecLin
        (fun w => if w ∈ S then z w else 0)) v = 0
      rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
      by_cases hv : v ∈ S
      · apply Finset.sum_eq_zero
        intro w hw'
        have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
        have hw'' : w ∉ S := (hSopp hadj).mp hv
        simp only [if_neg hw'']
      · calc
          _ = ∑ w ∈ G.neighborFinset v, z w := by
            apply Finset.sum_congr rfl
            intro w hw'
            have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
            have hw'' : w ∈ S := (hSopp hadj.symm).mpr hv
            simp only [if_pos hw'']
          _ = 0 := by
            simpa only [A, Matrix.mulVecLin_apply,
              SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using congrFun hzA v
    have hmin (z : V → ZMod 2) (hz0 : z ≠ 0) (hzA : A z = 0) :
        d ≤ hammingNorm z := by
      have hm : hammingNorm z ∈ weights := by
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz0, hzA⟩, rfl⟩))
      exact Finset.min'_le weights (hammingNorm z) hm
    have hbit : ∀ a : ZMod 2,
        (if a ≠ 0 then (1 : ℕ) else 0) +
          (if 1 - a ≠ 0 then 1 else 0) = 1 := by decide
    have hbound (S : Finset V) (hS : 2 * S.card = n)
        (hSopp : ∀ {v w : V}, G.Adj v w → (v ∈ S ↔ w ∉ S))
        (z : V → ZMod 2) (hz0 : z ≠ 0)
        (hz1 : z ≠ (fun v => if v ∈ S then 1 else 0))
        (hzA : A z = 0) (hzsupp : ∀ v, v ∉ S → z v = 0) :
        (4 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by
      let b : V → ZMod 2 := fun v => if v ∈ S then 1 else 0
      have hbA : A b = 0 := by
        simpa only [b, Pi.one_apply] using hproj S hSopp (1 : V → ZMod 2) hone
      have hy0 : b - z ≠ 0 := by
        intro hy
        apply hz1
        exact (sub_eq_zero.mp hy).symm
      have hyA : A (b - z) = 0 := by
        rw [map_sub, hbA, hzA, sub_self]
      have hpoint (v : V) :
          (if z v ≠ 0 then (1 : ℕ) else 0) +
            (if (b - z) v ≠ 0 then 1 else 0) =
            if v ∈ S then 1 else 0 := by
        by_cases hv : v ∈ S
        · simpa only [b, Pi.sub_apply, if_pos hv] using hbit (z v)
        · simp [b, hv, hzsupp v hv]
      have hsum : hammingNorm z + hammingNorm (b - z) = S.card := by
        calc
          _ = ∑ v : V,
              ((if z v ≠ 0 then (1 : ℕ) else 0) +
                (if (b - z) v ≠ 0 then 1 else 0)) := by
            simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
          _ = ∑ v : V, if v ∈ S then (1 : ℕ) else 0 :=
            Finset.sum_congr rfl (fun v _ => hpoint v)
          _ = S.card := by
            rw [← Finset.card_filter]
            simp [Finset.filter_mem_eq_inter]
      have hfirst := hmin z hz0 hzA
      have hsecond := hmin (b - z) hy0 hyA
      have htwo : 2 * d ≤ S.card := by omega
      have hfour : 4 * d ≤ n := by omega
      exact_mod_cast hfour
    let l : V → ZMod 2 := fun v => if v ∈ s then 1 else 0
    let rcode : V → ZMod 2 := fun v => if v ∈ sᶜ then 1 else 0
    let L : Submodule (ZMod 2) (V → ZMod 2) :=
      Submodule.span (ZMod 2) (Set.range ![l, rcode])
    have hLdim : Module.finrank (ZMod 2) L ≤ 2 := by
      simpa only [L, Set.finrank, Fintype.card_fin] using
        (finrank_range_le_card (R := ZMod 2) ![l, rcode])
    have hlL : l ∈ L := Submodule.subset_span ⟨(0 : Fin 2), by simp⟩
    have hrL : rcode ∈ L := Submodule.subset_span ⟨(1 : Fin 2), by simp⟩
    obtain ⟨x, hxC, hxL⟩ : ∃ x : V → ZMod 2, x ∈ C ∧ x ∉ L := by
      by_contra h
      have hCL : C ≤ L := by
        intro x hx
        by_contra hxL
        exact h ⟨x, hx, hxL⟩
      have hdim := Submodule.finrank_mono hCL
      change k ≤ Module.finrank (ZMod 2) L at hdim
      omega
    have hxA : A x = 0 := hxC
    let xL : V → ZMod 2 := fun v => if v ∈ s then x v else 0
    let xR : V → ZMod 2 := fun v => if v ∈ sᶜ then x v else 0
    have hxsum : xL + xR = x := by
      funext v
      by_cases hv : v ∈ s <;> simp [xL, xR, hv]
    have hchoice : (xL ≠ 0 ∧ xL ≠ l) ∨ (xR ≠ 0 ∧ xR ≠ rcode) := by
      by_contra h
      have hxLL : xL ∈ L := by
        by_cases hzero : xL = 0
        · rw [hzero]
          exact L.zero_mem
        · by_cases heql : xL = l
          · rw [heql]
            exact hlL
          · exact False.elim (h (Or.inl ⟨hzero, heql⟩))
      have hxRL : xR ∈ L := by
        by_cases hzero : xR = 0
        · rw [hzero]
          exact L.zero_mem
        · by_cases heqr : xR = rcode
          · rw [heqr]
            exact hrL
          · exact False.elim (h (Or.inr ⟨hzero, heqr⟩))
      apply hxL
      rw [← hxsum]
      exact L.add_mem hxLL hxRL
    rcases hchoice with ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩
    · apply hbound s hside hopp xL hx0 hx1 (hproj s hopp x hxA)
      intro v hv
      simp only [xL, if_neg hv]
    · apply hbound sᶜ hside' hoppc xR hx0 hx1 (hproj sᶜ hoppc x hxA)
      intro v hv
      simp only [xR, if_neg hv]
  · simp only [ho, Nat.cast_one, one_mul]
    exact model_5e76b721dff9cc8391a8 G
      ⟨h_guard.1, h_guard.2.1,
        by linarith only [h_guard.2.2.1],
        by linarith only [h_guard.2.2.2]⟩

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
theorem model_60716014e2e559489a74 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) ≤ ((Fintype.card V : ℝ) * (G.minDegree : ℝ)) := by
  sorry
