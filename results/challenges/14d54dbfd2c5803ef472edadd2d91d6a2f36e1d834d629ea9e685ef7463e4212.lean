import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem model_02ce2b029db2bd60d69c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (((Fintype.card V : ℝ) + (1 : ℝ)) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) := by
  classical
  rcases h_guard with ⟨⟨r, hr⟩, hm_guard, hk_guard⟩
  let n := Fintype.card V
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let C := LinearMap.ker A
  let k := Module.finrank (ZMod 2) C
  let weights : Finset ℕ := {n + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d := weights.min' hw
  change (k : ℝ) ≥ (9999999 / 10000000 : ℝ) at hk_guard
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz] at hk_guard
    norm_num at hk_guard
  have hmpos : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := by omega
    rw [hz] at hm_guard
    norm_num at hm_guard
  have hkle : k ≤ n := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
      _ = n := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hnpos : 0 < Fintype.card V := by
    change 0 < n
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hrmin : G.minDegree = r := hr.minDegree_eq
  have hmin (x : V → ZMod 2) (hx : x ≠ 0) (hAx : A x = 0) :
      d ≤ hammingNorm x := by
    exact Finset.min'_le weights (hammingNorm x) (Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hAx⟩, rfl⟩)))
  have hdpos : 0 < d := by
    have hdmem : d ∈ weights := Finset.min'_mem weights hw
    rcases Finset.mem_union.mp hdmem with hs | hi
    · have he : d = n + 1 := Finset.mem_singleton.mp hs
      omega
    · obtain ⟨x, hxf, hxd⟩ := Finset.mem_image.mp hi
      have hp : 0 < hammingNorm x :=
        hammingNorm_pos_iff.mpr (Finset.mem_filter.mp hxf).2.1
      omega
  have hdle : d ≤ n := by
    obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero
      (R := ZMod 2) (M := C)).mp hkpos
    have hxne : (x : V → ZMod 2) ≠ 0 := by
      intro hz
      apply hx
      exact Subtype.ext hz
    exact (hmin (x : V → ZMod 2) hxne (LinearMap.mem_ker.mp x.property)).trans
      hammingNorm_le_card_fintype
  have hexists (s : Finset V) (hs : n < k + s.card) :
      ∃ x : V → ZMod 2, x ≠ 0 ∧ A x = 0 ∧ ∀ v, v ∉ s → x v = 0 := by
    let f : C →ₗ[ZMod 2] (↥(sᶜ) → ZMod 2) :=
      { toFun := fun x v => (x : V → ZMod 2) (v : V)
        map_add' := by
          intro x y
          funext v
          rfl
        map_smul' := by
          intro c x
          funext v
          rfl }
    have hdim : Module.finrank (ZMod 2) (↥(sᶜ) → ZMod 2) <
        Module.finrank (ZMod 2) C := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      change sᶜ.card < k
      have hc := Finset.card_add_card_compl s
      change s.card + sᶜ.card = n at hc
      omega
    obtain ⟨x, hxf, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
    refine ⟨(x : V → ZMod 2), ?_, LinearMap.mem_ker.mp x.property, ?_⟩
    · intro hz
      apply hx
      exact Subtype.ext hz
    · intro v hv
      have hh := congrFun (LinearMap.mem_ker.mp hxf)
        (⟨v, Finset.mem_compl.mpr hv⟩ : ↥(sᶜ))
      exact hh
  have hweight_le (s : Finset V) (x : V → ZMod 2)
      (hxs : ∀ v, v ∉ s → x v = 0) : hammingNorm x ≤ s.card := by
    change (Finset.univ.filter (fun v => x v ≠ 0)).card ≤ s.card
    apply Finset.card_le_card
    intro v hv
    by_contra hvs
    exact (Finset.mem_filter.mp hv).2 (hxs v hvs)
  have hsingleton : k + d ≤ n + 1 := by
    obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset V)) (n := n - k + 1) (by
        change n - k + 1 ≤ n
        omega)
    obtain ⟨x, hx, hAx, hxs⟩ := hexists s (by omega)
    have hb := (hmin x hx hAx).trans (hweight_le s x hxs)
    omega
  have hbinary (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
    apply (ZMod.val_eq_one (by decide : 1 < 2) a).mp
    have hl := ZMod.val_lt a
    have hn := (ZMod.val_ne_zero a).mpr ha
    omega
  have happly (s : Finset V) (v : V) :
      A (fun w => if w ∈ s then 1 else 0) v =
        ∑ w ∈ s, G.adjMatrix (ZMod 2) v w := by
    change (∑ w : V, G.adjMatrix (ZMod 2) v w * (if w ∈ s then 1 else 0)) = _
    simp only [mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_mem_eq s (fun w => G.adjMatrix (ZMod 2) v w)
  have hfloor : Int.floor ((G.minDegree : ℝ) / 2) =
      ((G.minDegree / 2 : ℕ) : ℤ) := by
    calc
      _ = (G.minDegree : ℤ) / 2 := by
        simpa only [Int.floor_natCast, Nat.cast_ofNat] using
          (Int.floor_div_natCast (G.minDegree : ℝ) 2)
      _ = ((G.minDegree / 2 : ℕ) : ℤ) := (Int.natCast_div G.minDegree 2).symm
  have hrem : (G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) =
      ((G.minDegree % 2 : ℕ) : ℝ) := by
    rw [hfloor]
    simp only [Int.cast_natCast]
    have hc : ((G.minDegree % 2 : ℕ) : ℝ) +
        2 * ((G.minDegree / 2 : ℕ) : ℝ) = (G.minDegree : ℝ) := by
      exact_mod_cast Nat.mod_add_div G.minDegree 2
    linarith
  change (k : ℝ) + (d : ℝ) ≤ (n : ℝ) + 1 -
    ((G.minDegree : ℝ) - 2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ))
  rw [hrem]
  have hcases : G.minDegree % 2 = 0 ∨ G.minDegree % 2 = 1 := by
    have hh := Nat.mod_lt G.minDegree (by decide : 0 < 2)
    omega
  rcases hcases with heven | hodd
  · rw [heven]
    simp only [Nat.cast_zero, sub_zero]
    exact_mod_cast hsingleton
  · have hstrict : k + d ≤ n := by
      by_contra hbad
      have heq : k + d = n + 1 := by omega
      have hchars (s : Finset V) (hs : s.card = d) :
          A (fun v => if v ∈ s then 1 else 0) = 0 := by
        obtain ⟨x, hx, hAx, hxs⟩ := hexists s (by omega)
        have hsub : Finset.univ.filter (fun v => x v ≠ 0) ⊆ s := by
          intro v hv
          by_contra hvs
          exact (Finset.mem_filter.mp hv).2 (hxs v hvs)
        have hfull : Finset.univ.filter (fun v => x v ≠ 0) = s := by
          apply Finset.eq_of_subset_of_card_le hsub
          change s.card ≤ hammingNorm x
          rw [hs]
          exact hmin x hx hAx
        have hxeq : x = fun v => if v ∈ s then 1 else 0 := by
          funext v
          by_cases hv : v ∈ s
          · rw [if_pos hv]
            have hfilt : v ∈ Finset.univ.filter (fun v => x v ≠ 0) := by
              rw [hfull]
              exact hv
            exact hbinary (x v) (Finset.mem_filter.mp hfilt).2
          · rw [if_neg hv]
            exact hxs v hv
        rw [hxeq] at hAx
        exact hAx
      by_cases hdn : d = n
      · have huniv : (Finset.univ : Finset V).card = d := by
          change n = d
          exact hdn.symm
        have hones : A (fun _ : V => (1 : ZMod 2)) = 0 := by
          simpa only [Finset.mem_univ, if_true] using hchars Finset.univ huniv
        obtain ⟨v⟩ := ‹Nonempty V›
        have hcv := congrFun hones v
        change Matrix.mulVec (G.adjMatrix (ZMod 2))
          (Function.const V (1 : ZMod 2)) v = 0 at hcv
        rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hr, mul_one] at hcv
        have hzmod : r % 2 = 0 := Nat.mod_eq_zero_of_dvd
          ((ZMod.natCast_eq_zero_iff r 2).mp hcv)
        rw [← hrmin] at hzmod
        omega
      · have hdlt : d < n := by omega
        obtain ⟨v⟩ := ‹Nonempty V›
        have hvpos : 0 < G.degree v := lt_of_lt_of_le hmpos (G.minDegree_le_degree v)
        obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
        let base : Finset V := ((Finset.univ : Finset V).erase v).erase w
        have hbase : base.card = n - 2 := by
          have hwm : w ∈ (Finset.univ : Finset V).erase v := by
            simp [hvw.ne.symm]
          dsimp only [base]
          rw [Finset.card_erase_of_mem hwm,
            Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
          change n - 1 - 1 = n - 2
          omega
        obtain ⟨t, htu, htcard⟩ := Finset.exists_subset_card_eq
          (s := base) (n := d - 1) (by rw [hbase]; omega)
        have hvnot : v ∉ t := by
          intro hv
          have hh := (Finset.mem_erase.mp (htu hv)).2
          exact (Finset.mem_erase.mp hh).1 rfl
        have hwnot : w ∉ t := by
          intro hw'
          exact (Finset.mem_erase.mp (htu hw')).1 rfl
        have hvcard : (insert v t).card = d := by
          rw [Finset.card_insert_of_notMem hvnot, htcard]
          omega
        have hwcard : (insert w t).card = d := by
          rw [Finset.card_insert_of_notMem hwnot, htcard]
          omega
        have hsum : (∑ u ∈ t, G.adjMatrix (ZMod 2) v u) = 0 := by
          have hh := congrFun (hchars (insert v t) hvcard) v
          rw [happly, Finset.sum_insert hvnot] at hh
          simpa using hh
        have hh := congrFun (hchars (insert w t) hwcard) v
        rw [happly, Finset.sum_insert hwnot, hsum] at hh
        simp [hvw] at hh
    rw [hodd]
    simp only [Nat.cast_one, add_sub_cancel_right]
    exact_mod_cast hstrict

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

theorem model_7f80b6911ecd9dc4c880 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) = ((2 : ℝ) * ((Int.floor (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ))) : ℝ)) := by
  classical
  suffices haux : ∀ (n : ℕ) (W : Type _) [Fintype W],
      Fintype.card W = n → ∀ (M : Matrix W W (ZMod 2)),
      (∀ i j, M i j = M j i) → (∀ i, M i i = 0) →
      ∃ k : ℕ, Fintype.card W =
        Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * k by
    obtain ⟨k, hk⟩ := haux (Fintype.card V) V rfl (G.adjMatrix (ZMod 2))
      (fun i j => (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply j i)
      (G.isAdjMatrix_adjMatrix (ZMod 2)).apply_diag
    have hcast : (Fintype.card V : ℝ) =
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) +
        (2 : ℝ) * (k : ℝ) := by
      exact_mod_cast hk
    have hreal : (Fintype.card V : ℝ) -
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) =
        (2 : ℝ) * (k : ℝ) := by
      linarith
    have hhalf : (2 : ℝ) * (k : ℝ) / 2 = (k : ℝ) := by
      ring
    simp [hreal, hhalf]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ hcard M hsym hdiag
    by_cases hM : M = 0
    · refine ⟨0, ?_⟩
      rw [hM, Matrix.mulVecLin_zero, LinearMap.ker_zero,
        finrank_top, Module.finrank_fintype_fun_eq_card, mul_zero, add_zero]
    obtain ⟨a, b, hne⟩ : ∃ a b, M a b ≠ 0 := by
      by_contra h
      push_neg at h
      apply hM
      ext a b
      exact h a b
    have hab : a ≠ b := by
      intro h
      subst b
      exact hne (hdiag a)
    have hba : b ≠ a := Ne.symm hab
    have hval : (M a b).val = 1 := by
      have hlt := ZMod.val_lt (M a b)
      have hnz := (ZMod.val_ne_zero (M a b)).mpr hne
      omega
    have hc : M a b = 1 := by
      calc
        M a b = ((M a b).val : ZMod 2) :=
          (ZMod.natCast_zmod_val (M a b)).symm
        _ = 1 := by simp only [hval, Nat.cast_one]
    have hc' : M b a = 1 := (hsym b a).trans hc
    let Wa := {v : W // v ≠ a}
    let b' : Wa := ⟨b, hba⟩
    let U := {v : Wa // v ≠ b'}
    have hcarda : Fintype.card Wa + 1 = Fintype.card W := by
      simpa only [Fintype.card_option] using
        Fintype.card_congr (Equiv.optionSubtypeNe a)
    have hcardb : Fintype.card U + 1 = Fintype.card Wa := by
      simpa only [Fintype.card_option] using
        Fintype.card_congr (Equiv.optionSubtypeNe b')
    have hcards : Fintype.card U + 2 = Fintype.card W := by
      omega
    have hsum (f : W → ZMod 2) : (∑ v : W, f v) =
        f a + f b + ∑ t : U, f t.val.val := by
      rw [Fintype.sum_eq_add_sum_subtype_ne f a]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun v : Wa => f v.val) b']
      exact (add_assoc _ _ _).symm
    have hrow (x : W → ZMod 2) (v : W) : M.mulVecLin x v =
        M v a * x a + M v b * x b +
        ∑ t : U, M v t.val.val * x t.val.val := by
      change (∑ w : W, M v w * x w) = _
      exact hsum (fun w => M v w * x w)
    let B : Matrix U U (ZMod 2) := fun i j =>
      M i.val.val j.val.val +
      M i.val.val a * M b j.val.val +
      M i.val.val b * M a j.val.val
    have hsymB : ∀ i j, B i j = B j i := by
      intro i j
      dsimp only [B]
      rw [hsym i.val.val j.val.val, hsym i.val.val a,
        hsym b j.val.val, hsym i.val.val b, hsym a j.val.val]
      ring
    have hdiagB : ∀ i, B i i = 0 := by
      intro i
      change M i.val.val i.val.val +
        M i.val.val a * M b i.val.val +
        M i.val.val b * M a i.val.val = 0
      rw [hdiag i.val.val, hsym b i.val.val, hsym a i.val.val,
        zero_add, mul_comm (M i.val.val b) (M i.val.val a)]
      exact ZModModule.add_self _
    have brow (y : U → ZMod 2) (v : U) : B.mulVecLin y v =
        (∑ t : U, M v.val.val t.val.val * y t) +
        M v.val.val a * (∑ t : U, M b t.val.val * y t) +
        M v.val.val b * (∑ t : U, M a t.val.val * y t) := by
      change (∑ t : U,
        (M v.val.val t.val.val + M v.val.val a * M b t.val.val +
          M v.val.val b * M a t.val.val) * y t) = _
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    have xa (x : LinearMap.ker M.mulVecLin) : x.val a =
        ∑ t : U, M b t.val.val * x.val t.val.val := by
      have hx := congrFun (LinearMap.mem_ker.mp x.property) b
      change M.mulVecLin x.val b = 0 at hx
      rw [hrow] at hx
      simp only [hc', hdiag b, one_mul, zero_mul, add_zero] at hx
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using
        congrArg (fun z : ZMod 2 =>
          z + ∑ t : U, M b t.val.val * x.val t.val.val) hx
    have xb (x : LinearMap.ker M.mulVecLin) : x.val b =
        ∑ t : U, M a t.val.val * x.val t.val.val := by
      have hx := congrFun (LinearMap.mem_ker.mp x.property) a
      change M.mulVecLin x.val a = 0 at hx
      rw [hrow] at hx
      simp only [hdiag a, hc, zero_mul, one_mul, zero_add] at hx
      simpa only [add_assoc, ZModModule.add_self, add_zero, zero_add] using
        congrArg (fun z : ZMod 2 =>
          z + ∑ t : U, M a t.val.val * x.val t.val.val) hx
    have hmem : ∀ x : LinearMap.ker M.mulVecLin,
        (fun t : U => x.val t.val.val) ∈ LinearMap.ker B.mulVecLin := by
      intro x
      rw [LinearMap.mem_ker]
      funext u
      change B.mulVecLin (fun t : U => x.val t.val.val) u = 0
      rw [brow, ← xa x, ← xb x]
      have hx := congrFun (LinearMap.mem_ker.mp x.property) u.val.val
      change M.mulVecLin x.val u.val.val = 0 at hx
      rw [hrow] at hx
      convert hx using 1 <;> ring
    let r0 : (W → ZMod 2) →ₗ[ZMod 2] (U → ZMod 2) :=
      LinearMap.funLeft (ZMod 2) (ZMod 2) (fun t : U => t.val.val)
    let r : LinearMap.ker M.mulVecLin →ₗ[ZMod 2] LinearMap.ker B.mulVecLin :=
      (r0.domRestrict (LinearMap.ker M.mulVecLin)).codRestrict
        (LinearMap.ker B.mulVecLin) hmem
    have hinj : Function.Injective r := by
      intro x y hxy
      have ht (t : U) : x.val t.val.val = y.val t.val.val := by
        have h := congrFun
          (congrArg (fun z : LinearMap.ker B.mulVecLin => z.val) hxy) t
        change x.val t.val.val = y.val t.val.val at h
        exact h
      apply Subtype.ext
      funext v
      by_cases hva : v = a
      · subst v
        rw [xa x, xa y]
        apply Finset.sum_congr rfl
        intro t _
        rw [ht t]
      · by_cases hvb : v = b
        · subst v
          rw [xb x, xb y]
          apply Finset.sum_congr rfl
          intro t _
          rw [ht t]
        · let t : U := ⟨⟨v, hva⟩, by
            intro h
            exact hvb (congrArg Subtype.val h)⟩
          exact ht t
    have hsurj : Function.Surjective r := by
      intro y
      let x : W → ZMod 2 := fun v =>
        if hva : v = a then ∑ t : U, M b t.val.val * y.val t
        else if hvb : v = b then ∑ t : U, M a t.val.val * y.val t
        else y.val ⟨⟨v, hva⟩, by
          intro h
          exact hvb (congrArg Subtype.val h)⟩
      have x_a : x a = ∑ t : U, M b t.val.val * y.val t := by
        simp [x]
      have x_b : x b = ∑ t : U, M a t.val.val * y.val t := by
        simp [x, hba]
      have x_u (t : U) : x t.val.val = y.val t := by
        have hta : t.val.val ≠ a := t.val.property
        have htb : t.val.val ≠ b := by
          intro h
          apply t.property
          exact Subtype.ext h
        simp [x, hta, htb]
      have hx : x ∈ LinearMap.ker M.mulVecLin := by
        rw [LinearMap.mem_ker]
        funext v
        change M.mulVecLin x v = 0
        rw [hrow]
        by_cases hva : v = a
        · subst v
          simp only [hdiag a, hc, zero_mul, one_mul, zero_add]
          rw [x_b]
          simp_rw [x_u]
          exact ZModModule.add_self _
        · by_cases hvb : v = b
          · subst v
            simp only [hc', hdiag b, one_mul, zero_mul, add_zero]
            rw [x_a]
            simp_rw [x_u]
            exact ZModModule.add_self _
          · let t : U := ⟨⟨v, hva⟩, by
              intro h
              exact hvb (congrArg Subtype.val h)⟩
            have hy := congrFun (LinearMap.mem_ker.mp y.property) t
            change B.mulVecLin y.val t = 0 at hy
            rw [brow] at hy
            change (∑ s : U, M v s.val.val * y.val s) +
              M v a * (∑ s : U, M b s.val.val * y.val s) +
              M v b * (∑ s : U, M a s.val.val * y.val s) = 0 at hy
            rw [x_a, x_b]
            simp_rw [x_u]
            convert hy using 1 <;> ring
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      funext t
      change x t.val.val = y.val t
      exact x_u t
    have hdim : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
        Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) :=
      (LinearEquiv.ofBijective r ⟨hinj, hsurj⟩).finrank_eq
    have hlt : Fintype.card U < n := by
      omega
    obtain ⟨k, hk⟩ := ih (Fintype.card U) hlt U rfl B hsymB hdiagB
    refine ⟨k + 1, ?_⟩
    rw [hdim]
    omega

theorem model_86d5f85f179c31163952 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let E : (s → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x v => if hv : v ∈ s then x ⟨v, hv⟩ else 0
      map_add' := by
        intro x y
        funext v
        by_cases hv : v ∈ s <;> simp [hv]
      map_smul' := by
        intro c x
        funext v
        by_cases hv : v ∈ s <;> simp [hv] }
  have hE : Function.Injective E := by
    intro x y hxy
    funext v
    have h := congrFun hxy (v : V)
    simpa [E, v.property] using h
  have hzero (x : s → ZMod 2) (v : V) (hv : v ∈ s) :
      A (E x) v = 0 := by
    change (∑ w : V, G.adjMatrix (ZMod 2) v w * E x w) = 0
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hws : w ∈ s
    · have hnot : ¬ G.Adj v w := by
        intro hadj
        exact ((SimpleGraph.compl_adj G v w).mp
          (hs.isClique hv hws hadj.ne)).2 hadj
      simp [SimpleGraph.adjMatrix_apply, hnot]
    · simp [E, hws]
  let f : (s → ZMod 2) →ₗ[ZMod 2] (↥(sᶜ) → ZMod 2) :=
    { toFun := fun x v => A (E x) (v : V)
      map_add' := by
        intro x y
        funext v
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext v
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hker : ∀ x : LinearMap.ker f,
      E (x : s → ZMod 2) ∈ LinearMap.ker A := by
    intro x
    rw [LinearMap.mem_ker]
    funext v
    change A (E (x : s → ZMod 2)) v = 0
    by_cases hv : v ∈ s
    · exact hzero (x : s → ZMod 2) v hv
    · have hx := congrFun (LinearMap.mem_ker.mp x.property)
        (⟨v, Finset.mem_compl.mpr hv⟩ : ↥(sᶜ))
      exact hx
  let e : LinearMap.ker f →ₗ[ZMod 2] LinearMap.ker A :=
    (E.domRestrict (LinearMap.ker f)).codRestrict (LinearMap.ker A) hker
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply hE
    exact congrArg (fun z : LinearMap.ker A => (z : V → ZMod 2)) hxy
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) ≤ sᶜ.card := by
    calc
      _ ≤ Module.finrank (ZMod 2) (↥(sᶜ) → ZMod 2) := Submodule.finrank_le _
      _ = sᶜ.card := by
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) +
      Module.finrank (ZMod 2) (LinearMap.ker f) = s.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker f
  have hcards : s.card + sᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hsize : s.card = Gᶜ.cliqueNum := hs.card_eq
  have hnat : 2 * Gᶜ.cliqueNum ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) + Fintype.card V := by
    omega
  have hreal : (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) ≤
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) + (Fintype.card V : ℝ) := by
    exact_mod_cast hnat
  change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) ≥
    (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) - (Fintype.card V : ℝ)
  linarith

theorem model_498663d70c6a4882faec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((2 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ)))) := by
  classical
  have hconn : G.Connected := h_guard.1
  letI : Nonempty V := hconn.nonempty
  have hlo : (1 : ℝ) < (G.minDegree : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).1
    linarith
  have hhi : (G.minDegree : ℝ) < (3 : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).2
    linarith
  have hlo' : 1 < G.minDegree := by exact_mod_cast hlo
  have hhi' : G.minDegree < 3 := by exact_mod_cast hhi
  have hmin : G.minDegree = 2 := by omega
  obtain ⟨d, hreg⟩ := h_guard.2.1
  have hd : d = 2 := hreg.minDegree_eq.symm.trans hmin
  have hdeg (u : V) : G.degree u = 2 := (hreg.degree_eq u).trans hd
  have hnotacyc : ¬ G.IsAcyclic := by
    intro hac
    have htree : G.IsTree := ⟨hconn, hac⟩
    have hedges := htree.card_edgeFinset
    have hsum : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
      simpa [hdeg, Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges
    omega
  have hexcycle : ∃ a, ∃ p : G.Walk a a, p.IsCycle := by
    by_contra h
    apply hnotacyc
    intro a p hp
    exact h ⟨a, p, hp⟩
  obtain ⟨a, p, hp⟩ := hexcycle
  have hn : 2 < p.length := by
    have h := hp.three_le_length
    omega
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨a, p, hp, rfl⟩
  have hcycledeg : ∀ i : Fin p.length,
      (SimpleGraph.cycleGraph p.length).degree i = 2 := by
    have hn3 : p.length - 3 + 3 = p.length := by omega
    rw [← hn3]
    exact fun i => SimpleGraph.cycleGraph_degree_three_le
  have hns (i : Fin p.length) : Function.Surjective (f.mapNeighborSet i) := by
    have hbij : Function.Bijective (f.mapNeighborSet i) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(f.mapNeighborSet i).injective, by
          simp only [SimpleGraph.card_neighborSet_eq_degree, hcycledeg, hdeg]⟩
    exact hbij.2
  have hclosed {i : Fin p.length} {w : V} (hw : G.Adj (f i) w) :
      ∃ j : Fin p.length, f j = w := by
    obtain ⟨j, hj⟩ := hns i ⟨w, hw⟩
    exact ⟨j.1, congrArg Subtype.val hj⟩
  have hreach {u w : V} (q : G.Walk u w) :
      (∃ i : Fin p.length, f i = u) → (∃ i : Fin p.length, f i = w) := by
    induction q with
    | nil => exact fun h => h
    | @cons u t w hut q ih =>
      rintro ⟨i, rfl⟩
      exact ih (hclosed hut)
  let i0 : Fin p.length := ⟨0, by omega⟩
  have hfs : Function.Surjective f := by
    intro w
    exact hreach (hconn (f i0) w).some ⟨i0, rfl⟩
  let e : SimpleGraph.cycleGraph p.length ≃g G :=
    { toEquiv := Equiv.ofBijective f ⟨f.injective, hfs⟩
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph p.length).Adj i j
        constructor
        · intro hij
          obtain ⟨k, hk⟩ := hns i ⟨f j, hij⟩
          have hval : f k.1 = f j := congrArg Subtype.val hk
          have hkval : k.1 = j := f.injective hval
          simpa only [SimpleGraph.mem_neighborSet, hkval] using k.property
        · intro hij
          exact f.toHom.map_adj hij }
  have hcard : p.length = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker A
  have hpairs (u : V) : ∃ v w, v ≠ w ∧ G.neighborFinset u = {v, w} := by
    apply Finset.card_eq_two.mp
    exact hdeg u
  have htwo (t : ZMod 2) : t + t = 0 := by
    simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel t
  have hrows (x : K) (u : V) : (∑ w ∈ G.neighborFinset u, x.1 w) = 0 := by
    have hx : A x.1 = 0 := LinearMap.mem_ker.mp x.property
    have h := congrFun hx u
    simpa only [A, Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      Pi.zero_apply] using h
  have hneighbors (x : K) {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) :
      x.1 v = x.1 w := by
    obtain ⟨s, t, hst, hs⟩ := hpairs u
    have hsum : x.1 s + x.1 t = 0 := by
      simpa [hs, hst] using hrows x u
    have heq : x.1 s = x.1 t := by
      have h : x.1 s = -x.1 t := eq_neg_of_add_eq_zero_left hsum
      simpa only [ZMod.neg_eq_self_mod_two] using h
    have hv : v = s ∨ v = t := by
      simpa [hs] using ((G.mem_neighborFinset u v).mpr huv)
    have hw : w = s ∨ w = t := by
      simpa [hs] using ((G.mem_neighborFinset u w).mpr huw)
    rcases hv with rfl | rfl
    · rcases hw with rfl | rfl
      · rfl
      · exact heq
    · rcases hw with rfl | rfl
      · exact heq.symm
      · rfl
  have hprop (x : K) {u w : V} (q : G.Walk u w) :
      ∀ z, G.Adj z u → x.1 z = 0 → x.1 u = 0 → x.1 w = 0 := by
    induction q with
    | nil =>
      intro z hz hz0 hu0
      exact hu0
    | @cons u t w hut q ih =>
      intro z hzu hz0 hu0
      exact ih u hut hu0 ((hneighbors x hzu.symm hut).symm.trans hz0)
  have hzero (x : K) {u v : V} (huv : G.Adj u v)
      (hu : x.1 u = 0) (hv : x.1 v = 0) : x = 0 := by
    apply Subtype.ext
    funext w
    exact hprop x (hconn v w).some u huv hu hv
  obtain ⟨b, b', hbb', hnb⟩ := hpairs a
  have hab : G.Adj a b := by
    apply (G.mem_neighborFinset a b).mp
    simp [hnb]
  let C0 : (ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := LinearMap.const
  have hC0 (t : ZMod 2) : C0 t ∈ K := by
    rw [LinearMap.mem_ker]
    funext u
    change Matrix.mulVec (G.adjMatrix (ZMod 2)) (C0 t) u = 0
    obtain ⟨v, w, hvw, hs⟩ := hpairs u
    rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
    change t + t = 0
    exact htwo t
  let C : (ZMod 2) →ₗ[ZMod 2] K := C0.codRestrict K hC0
  have hCi : Function.Injective C := by
    intro x y hxy
    have h := congrArg (fun z : K => z.1 a) hxy
    change x = y at h
    exact h
  have hge1 : 1 ≤ Module.finrank (ZMod 2) K := by
    simpa only [CommSemiring.finrank_self] using
      LinearMap.finrank_le_finrank_of_injective hCi
  let T : K →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi fun i =>
      if i = 0 then (LinearMap.proj a).domRestrict K
      else (LinearMap.proj b).domRestrict K
  have hTi : Function.Injective T := by
    intro x y hxy
    have h0 : x.1 a = y.1 a := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (0 : Fin 2)
    have h1 : x.1 b = y.1 b := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (1 : Fin 2)
    apply sub_eq_zero.mp
    apply hzero (x - y) hab
    · change x.1 a - y.1 a = 0
      exact sub_eq_zero.mpr h0
    · change x.1 b - y.1 b = 0
      exact sub_eq_zero.mpr h1
  have hle2 : Module.finrank (ZMod 2) K ≤ 2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_injective hTi
  change (Module.finrank (ZMod 2) K : ℝ) = _
  rw [← hcard]
  by_cases hEven : Even p.length
  · have hcolor : G.Colorable 2 :=
      (SimpleGraph.IsBipartite.cycleGraph_of_even hEven).of_hom e.symm.toHom
    obtain ⟨c⟩ := hcolor
    have hcsurj : Function.Surjective c := by
      intro i
      have hne : (c a).val ≠ (c b).val := by
        intro h
        exact c.valid hab (Fin.ext h)
      have ha2 := (c a).isLt
      have hb2 := (c b).isLt
      have hi2 := i.isLt
      have hi : i = c a ∨ i = c b := by
        by_cases hia : i = c a
        · exact Or.inl hia
        · right
          apply Fin.ext
          have hia' : i.val ≠ (c a).val := by
            intro h
            exact hia (Fin.ext h)
          omega
      rcases hi with hi | hi
      · exact ⟨a, hi.symm⟩
      · exact ⟨b, hi.symm⟩
    have hcolors {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : c v = c w := by
      apply Fin.ext
      have hv : (c u).val ≠ (c v).val := by
        intro h
        exact c.valid huv (Fin.ext h)
      have hw : (c u).val ≠ (c w).val := by
        intro h
        exact c.valid huw (Fin.ext h)
      have hu2 := (c u).isLt
      have hv2 := (c v).isLt
      have hw2 := (c w).isLt
      omega
    let D0 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
      LinearMap.pi fun u => LinearMap.proj (c u)
    have hD0 (t : Fin 2 → ZMod 2) : D0 t ∈ K := by
      rw [LinearMap.mem_ker]
      funext u
      change Matrix.mulVec (G.adjMatrix (ZMod 2)) (D0 t) u = 0
      obtain ⟨v, w, hvw, hs⟩ := hpairs u
      have huv : G.Adj u v := by
        apply (G.mem_neighborFinset u v).mp
        simp [hs]
      have huw : G.Adj u w := by
        apply (G.mem_neighborFinset u w).mp
        simp [hs]
      have heq := hcolors huv huw
      rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
      change t (c v) + t (c w) = 0
      rw [heq]
      exact htwo _
    let D : (Fin 2 → ZMod 2) →ₗ[ZMod 2] K := D0.codRestrict K hD0
    have hDi : Function.Injective D := by
      intro x y hxy
      funext i
      obtain ⟨u, hu⟩ := hcsurj i
      have h := congrArg (fun z : K => z.1 u) hxy
      change x (c u) = y (c u) at h
      simpa only [hu] using h
    have hge2 : 2 ≤ Module.finrank (ZMod 2) K := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        LinearMap.finrank_le_finrank_of_injective hDi
    have hdim : Module.finrank (ZMod 2) K = 2 := le_antisymm hle2 hge2
    obtain ⟨k, hk⟩ := hEven
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      rw [hquot, Int.floor_natCast]
    rw [hdim, hfloor, hk]
    push_cast <;> ring
  · have hOdd : Odd p.length := Nat.not_even_iff_odd.mp hEven
    have hnotcolor : ¬ G.Colorable 2 := by
      intro hc
      have hc' := hc.of_hom f.toHom
      have hchrom := SimpleGraph.chromaticNumber_cycleGraph_of_odd p.length
        (by omega) hOdd
      have hle := hc'.chromaticNumber_le
      rw [hchrom] at hle
      norm_num at hle
    have hsame (x : K) : x.1 a = x.1 b := by
      by_contra hx
      let c : G.Coloring (ZMod 2) :=
        SimpleGraph.Coloring.mk x.1 (by
          intro u w huw heq
          have hxconst : x = C (x.1 u) := by
            apply sub_eq_zero.mp
            apply hzero (x - C (x.1 u)) huw
            · change x.1 u - x.1 u = 0
              exact sub_self _
            · change x.1 w - x.1 u = 0
              exact sub_eq_zero.mpr heq.symm
          apply hx
          rw [hxconst]
          rfl)
      exact hnotcolor (by simpa only [ZMod.card] using c.colorable)
    let S : K →ₗ[ZMod 2] (ZMod 2) := (LinearMap.proj a).domRestrict K
    have hSi : Function.Injective S := by
      intro x y hxy
      have h : x.1 a = y.1 a := by
        simpa [S, LinearMap.proj_apply] using hxy
      have hz : (x - y).1 a = 0 := by
        change x.1 a - y.1 a = 0
        exact sub_eq_zero.mpr h
      apply sub_eq_zero.mp
      exact hzero (x - y) hab hz ((hsame (x - y)).symm.trans hz)
    have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
      simpa only [CommSemiring.finrank_self] using
        LinearMap.finrank_le_finrank_of_injective hSi
    have hdim : Module.finrank (ZMod 2) K = 1 := le_antisymm hle1 hge1
    obtain ⟨k, hk⟩ := hOdd
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) + (1 / 2 : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      rw [hquot]
      constructor <;> push_cast <;> linarith
    rw [hdim, hfloor, hk]
    push_cast <;> ring
theorem model_bd745c7d8b877a7a34e8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (29999999 / 10000000 : ℝ)))) :
    ((((Fintype.card V : ℝ) + (1 : ℝ)) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) - (G.minDegree : ℝ)) ≤ (Real.exp (((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) - (1 : ℝ)) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * (Real.log (1 + (1 : ℝ))))) := by
  sorry
