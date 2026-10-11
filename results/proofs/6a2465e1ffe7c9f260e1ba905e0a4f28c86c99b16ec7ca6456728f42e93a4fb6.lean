import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem model_2209847bd37567ccf0ff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (59999999 / 10000000 : ℝ)))) :
    (((((Fintype.card V : ℝ) ^ 3) + ((5 : ℝ) * (Fintype.card V : ℝ))) + (6 : ℝ)) / (6 : ℝ)) ≤ (Real.exp (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  let n : ℕ := Fintype.card V
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S =>
      S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
        ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hwne : weights.Nonempty := by simp [weights]
  have hg : (((weights.min' hwne - 1 : ℕ) : ℝ)) ≥
      (59999999 / 10000000 : ℝ) := h_guard.2
  classical
  have hlarge : 7 ≤ weights.min' hwne := by
    by_contra hh
    have hb : weights.min' hwne - 1 ≤ 5 := by omega
    have hbr : (((weights.min' hwne - 1 : ℕ) : ℝ)) ≤ (5 : ℝ) := by
      exact_mod_cast hb
    linarith only [hg, hbr]
  have hn : 6 ≤ n := by
    have hmem : n + 1 ∈ weights := by simp [weights]
    have hle := Finset.min'_le weights (n + 1) hmem
    omega
  have hsmall (S : Finset V) (hS : S.Nonempty) (hc : S.card ≤ 6) :
      ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    by_contra hh
    have hmem : S.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, ⟨hS, hh⟩⟩, rfl⟩
    have hle := Finset.min'_le weights S.card hmem
    omega
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let chi : Finset V → V → ZMod 2 := fun S v => if v ∈ S then 1 else 0
  let small : Finset (Finset V) := Finset.univ.filter (fun S => S.card ≤ 3)
  let f : small → LinearMap.range A := fun S =>
    ⟨A (chi S.val), ⟨chi S.val, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro S T hST
    have hsame : A (chi S.val) = A (chi T.val) :=
      congrArg (fun z : LinearMap.range A => z.val) hST
    have hScard : S.val.card ≤ 3 := (Finset.mem_filter.mp S.property).2
    have hTcard : T.val.card ≤ 3 := (Finset.mem_filter.mp T.property).2
    apply Subtype.ext
    by_contra hne
    let U : Finset V := (S.val \ T.val) ∪ (T.val \ S.val)
    have hUne : U.Nonempty := by
      change (symmDiff S.val T.val).Nonempty
      exact Finset.symmDiff_nonempty.mpr hne
    have hUcard : U.card ≤ 6 := by
      calc
        U.card ≤ (S.val \ T.val).card + (T.val \ S.val).card :=
          Finset.card_union_le _ _
        _ ≤ S.val.card + T.val.card :=
          Nat.add_le_add
            (Finset.card_le_card Finset.sdiff_subset)
            (Finset.card_le_card Finset.sdiff_subset)
        _ ≤ 6 := by omega
    have hchi : chi U = chi S.val + chi T.val := by
      funext v
      by_cases hs : v ∈ S.val <;> by_cases ht : v ∈ T.val <;>
        simp [chi, U, Finset.mem_union, Finset.mem_sdiff, hs, ht,
          ZModModule.add_self]
    have hz : A (chi U) = 0 := by
      rw [hchi, map_add, hsame]
      exact ZModModule.add_self _
    obtain ⟨v, w, hw, hvw, huniq⟩ := hsmall U hUne hUcard
    have hrow : A (chi U) v = 1 := by
      change (∑ u : V, G.adjMatrix (ZMod 2) v u * chi U u) = 1
      calc
        (∑ u : V, G.adjMatrix (ZMod 2) v u * chi U u) =
            G.adjMatrix (ZMod 2) v w * chi U w := by
          apply Finset.sum_eq_single_of_mem w (Finset.mem_univ w)
          intro u _ huw
          by_cases hu : u ∈ U
          · have hnot : ¬ G.Adj v u := by
              intro hvu
              exact huw (huniq u hu hvu)
            simp [SimpleGraph.adjMatrix_apply, hnot]
          · simp [chi, hu]
        _ = 1 := by simp [chi, hw, hvw, SimpleGraph.adjMatrix_apply]
    have hvzero : A (chi U) v = 0 := congrFun hz v
    rw [hrow] at hvzero
    exact one_ne_zero hvzero
  have hsmall_eq : small = (Finset.range 4).biUnion
      (fun i => (Finset.univ : Finset V).powersetCard i) := by
    ext S
    simp only [small, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
      Finset.subset_univ]
    constructor
    · intro hc
      exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨i, hi, hc⟩
      omega
  have hdisj : (↑(Finset.range 4) : Set ℕ).PairwiseDisjoint
      (fun i => (Finset.univ : Finset V).powersetCard i) :=
    (Finset.pairwise_disjoint_powersetCard (Finset.univ : Finset V)).set_pairwise _
  have hcount : small.card = 1 + n + n.choose 2 + n.choose 3 := by
    rw [hsmall_eq, Finset.card_biUnion hdisj]
    simp [Finset.sum_range_succ, n]
  have hbound : 1 + n + n.choose 2 + n.choose 3 ≤
      2 ^ Module.finrank (ZMod 2) (LinearMap.range A) := by
    calc
      _ = Fintype.card small := by rw [Fintype.card_coe, hcount]
      _ ≤ Fintype.card (LinearMap.range A) := Fintype.card_le_of_injective f hinj
      _ = 2 ^ Module.finrank (ZMod 2) (LinearMap.range A) := by
        simpa only [ZMod.card] using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range A))
  have hchoose2 : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ n
  have hchoose3 : (n.choose 3 : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
    have hdnat : (n - 2) * ((n - 1) * n) = 6 * n.choose 3 := by
      simpa [Nat.descFactorial_succ, Nat.factorial] using
        (Nat.descFactorial_eq_factorial_mul_choose n 3)
    have hdreal : ((n - 2 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ) * (n : ℝ)) =
        (6 : ℝ) * (n.choose 3 : ℝ) := by
      exact_mod_cast hdnat
    have hsub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      norm_num [Nat.cast_sub (show 1 ≤ n from by omega)]
    have hsub2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      norm_num [Nat.cast_sub (show 2 ≤ n from by omega)]
    rw [hsub2, hsub1] at hdreal
    nlinarith only [hdreal]
  have hvolume : ((1 + n + n.choose 2 + n.choose 3 : ℕ) : ℝ) =
      ((n : ℝ) ^ 3 + 5 * (n : ℝ) + 6) / 6 := by
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hchoose2, hchoose3]
    ring
  have hboundreal : ((1 + n + n.choose 2 + n.choose 3 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range A) := by
    exact_mod_cast hbound
  rw [hvolume] at hboundreal
  have hdim : Module.finrank (ZMod 2) (LinearMap.range A) +
      Module.finrank (ZMod 2) (LinearMap.ker A) = n := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hdimcast : (Module.finrank (ZMod 2) (LinearMap.range A) : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (n : ℝ) := by
    exact_mod_cast hdim
  have hdimreal : (n : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) =
      (Module.finrank (ZMod 2) (LinearMap.range A) : ℝ) := by
    linarith only [hdimcast]
  have htwo : (1 : ℝ) + 1 = 2 := by norm_num
  change ((n : ℝ) ^ 3 + 5 * (n : ℝ) + 6) / 6 ≤
    Real.exp (((n : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) *
      Real.log (1 + (1 : ℝ)))
  rw [hdimreal, htwo, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact hboundreal

theorem model_eccaeecd0caf8e058231 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (39999999 / 10000000 : ℝ)))) :
    ((1 : ℝ) + (((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) + (1 : ℝ))) / (2 : ℝ))) ≤ (Real.exp (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S =>
      S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
        ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  have hminreal : (((weights.min' hw - 1 : ℕ) : ℝ)) ≥
      (39999999 / 10000000 : ℝ) := by
    simpa only [weights] using h_guard.2
  have hfour : 4 ≤ weights.min' hw - 1 := by
    by_contra h
    have hn : weights.min' hw - 1 ≤ 3 := by omega
    have hr : (((weights.min' hw - 1 : ℕ) : ℝ)) ≤ 3 := by
      exact_mod_cast hn
    linarith only [hminreal, hr]
  have hfive : 5 ≤ weights.min' hw := by omega
  have hsmall : ∀ S : Finset V, S.Nonempty → S.card ≤ 4 →
      ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    intro S hS hc
    by_contra h
    have hm : S.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS, h⟩, rfl⟩
    have hl : weights.min' hw ≤ S.card := Finset.min'_le weights S.card hm
    omega
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  have hkerSmall : ∀ x : V → ZMod 2, A x = 0 →
      ((Finset.univ : Finset V).filter (fun v => x v ≠ 0)).card ≤ 4 → x = 0 := by
    intro x hx hc
    by_contra hn
    let S : Finset V := Finset.univ.filter (fun v => x v ≠ 0)
    have hS : S.Nonempty := by
      by_contra he
      apply hn
      funext v
      have hv : v ∉ S := by
        intro hv
        exact he ⟨v, hv⟩
      simpa [S] using hv
    obtain ⟨v, w, hwS, hvw, huniq⟩ := hsmall S hS hc
    have hxw : x w ≠ 0 := (Finset.mem_filter.mp hwS).2
    have hv := congrFun hx v
    change (∑ u : V, G.adjMatrix (ZMod 2) v u * x u) = 0 at hv
    have hsum : (∑ u : V, G.adjMatrix (ZMod 2) v u * x u) = x w := by
      calc
        _ = G.adjMatrix (ZMod 2) v w * x w := by
          apply Finset.sum_eq_single w
          · intro u _ hne
            by_cases hu : u ∈ S
            · have hnot : ¬ G.Adj v u := by
                intro hadj
                exact hne (huniq u hu hadj)
              simp [SimpleGraph.adjMatrix_apply, hnot]
            · have hxu : x u = 0 := by simpa [S] using hu
              simp [hxu]
          · simp
        _ = x w := by simp [SimpleGraph.adjMatrix_apply, hvw]
    exact hxw (hsum.symm.trans hv)
  let D : Finset (Finset V) :=
    ((Finset.univ : Finset V).powersetCard 0 ∪
      (Finset.univ : Finset V).powersetCard 1) ∪
      (Finset.univ : Finset V).powersetCard 2
  have hDsmall : ∀ S ∈ D, S.card ≤ 2 := by
    intro S hS
    simp only [D, Finset.mem_union, Finset.mem_powersetCard] at hS
    rcases hS with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ <;> omega
  have hd01 : Disjoint ((Finset.univ : Finset V).powersetCard 0)
      ((Finset.univ : Finset V).powersetCard 1) :=
    Finset.disjoint_powersetCard_of_ne (by decide) _ _
  have hd02 : Disjoint ((Finset.univ : Finset V).powersetCard 0)
      ((Finset.univ : Finset V).powersetCard 2) :=
    Finset.disjoint_powersetCard_of_ne (by decide) _ _
  have hd12 : Disjoint ((Finset.univ : Finset V).powersetCard 1)
      ((Finset.univ : Finset V).powersetCard 2) :=
    Finset.disjoint_powersetCard_of_ne (by decide) _ _
  have hd2 : Disjoint
      ((Finset.univ : Finset V).powersetCard 0 ∪
        (Finset.univ : Finset V).powersetCard 1)
      ((Finset.univ : Finset V).powersetCard 2) :=
    Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩
  have hDcard : D.card = 1 + Fintype.card V + (Fintype.card V).choose 2 := by
    dsimp only [D]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd01]
    simp only [Finset.card_powersetCard, Finset.card_univ,
      Nat.choose_zero_right, Nat.choose_one_right]
  let c : Finset V → (V → ZMod 2) := fun S v => if v ∈ S then 1 else 0
  let f : ↥D → LinearMap.range A := fun S =>
    ⟨A (c S.val), ⟨c S.val, rfl⟩⟩
  have hf : Function.Injective f := by
    intro S T h
    have hA : A (c S.val) = A (c T.val) :=
      congrArg (fun z : LinearMap.range A => (z : V → ZMod 2)) h
    have hz : A (c S.val - c T.val) = 0 := by
      rw [map_sub, hA, sub_self]
    have hc : ((Finset.univ : Finset V).filter
        (fun v => (c S.val - c T.val) v ≠ 0)).card ≤ 4 := by
      calc
        _ ≤ (S.val ∪ T.val).card := by
          apply Finset.card_le_card
          intro v hv
          by_contra hnot
          have hs : v ∉ S.val := fun hs =>
            hnot (Finset.mem_union.mpr (Or.inl hs))
          have ht : v ∉ T.val := fun ht =>
            hnot (Finset.mem_union.mpr (Or.inr ht))
          exact (Finset.mem_filter.mp hv).2 (by simp [c, hs, ht])
        _ ≤ S.val.card + T.val.card := Finset.card_union_le _ _
        _ ≤ 4 := by
          have hs := hDsmall S.val S.property
          have ht := hDsmall T.val T.property
          omega
    have hzero : c S.val - c T.val = 0 := hkerSmall _ hz hc
    have hval : c S.val = c T.val := sub_eq_zero.mp hzero
    apply Subtype.ext
    apply Finset.ext
    intro v
    have hv := congrFun hval v
    by_cases hs : v ∈ S.val <;> by_cases ht : v ∈ T.val <;>
      simp [c, hs, ht] at hv ⊢
  have hrange : Fintype.card (LinearMap.range A) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range A) := by
    simpa only [ZMod.card, Fintype.card_fin] using
      (Module.card_fintype (Module.finBasis (ZMod 2) (LinearMap.range A)))
  have hcount : 1 + Fintype.card V + (Fintype.card V).choose 2 ≤
      2 ^ Module.finrank (ZMod 2) (LinearMap.range A) := by
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_coe, hDcard, hrange] at hc
    exact hc
  have hdim : Module.finrank (ZMod 2) (LinearMap.range A) +
      Module.finrank (ZMod 2) (LinearMap.ker A) = Fintype.card V := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hdiff : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) =
      (Module.finrank (ZMod 2) (LinearMap.range A) : ℝ) := by
    have hcast : (Module.finrank (ZMod 2) (LinearMap.range A) : ℝ) +
        (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) =
        (Fintype.card V : ℝ) := by
      exact_mod_cast hdim
    linarith only [hcast]
  have hchoose : ∀ m : ℕ, (1 : ℝ) + (m : ℝ) + (m.choose 2 : ℝ) =
      1 + (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Nat.choose_succ_succ m 1, Nat.choose_one_right]
      push_cast
      nlinarith only [ih]
  change (1 : ℝ) + (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) + 1) / 2 ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) * Real.log (1 + (1 : ℝ)))
  rw [hdiff, show (1 : ℝ) + 1 = 2 by norm_num,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    ← hchoose (Fintype.card V)]
  exact_mod_cast hcount

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

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
theorem model_7bc785c375fbbdb773ee {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (19999999 / 10000000 : ℝ)))) :
    (((1 : ℝ) + ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * (((Fintype.card V : ℝ) + (1 : ℝ)) + ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))))) ≤ (Real.exp (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let n : ℕ := Fintype.card V
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker A
  let R := LinearMap.range A
  let k : ℕ := Module.finrank (ZMod 2) K
  let r : ℕ := Module.finrank (ZMod 2) R
  let D : ℕ := G.minDegree
  have hkg : (9999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.1
  have hk : 1 ≤ k := by
    have hh : (0 : ℝ) < (k : ℝ) := by linarith only [hkg]
    have hh' : 0 < k := by exact_mod_cast hh
    omega
  have hdim : r + k = n := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hn : 0 < n := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨d0, hd0⟩ := h_guard.1
  have hdeg : ∀ v : V, G.degree v = D :=
    fun v => (hd0 v).trans hd0.minDegree_eq.symm
  have hDg : (9999999 / 10000000 : ℝ) ≤ (D : ℝ) := h_guard.2.1
  have hD : 1 ≤ D := by
    by_contra h
    have hb : D ≤ 0 := by omega
    have hbr : (D : ℝ) ≤ 0 := by exact_mod_cast hb
    linarith only [hDg, hbr]
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S =>
      S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
        ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  have hg : (((weights.min' hw - 1 : ℕ) : ℝ)) ≥
      (19999999 / 10000000 : ℝ) := h_guard.2.2.2
  have hlarge : 3 ≤ weights.min' hw := by
    by_contra h
    have hb : weights.min' hw - 1 ≤ 1 := by omega
    have hbr : (((weights.min' hw - 1 : ℕ) : ℝ)) ≤ 1 := by
      exact_mod_cast hb
    linarith only [hg, hbr]
  have hsmall (S : Finset V) (hS : S.Nonempty) (hc : S.card ≤ 2) :
      ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    by_contra hh
    have hm : S.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr
        ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS, hh⟩, rfl⟩
    have hl := Finset.min'_le weights S.card hm
    omega
  let c : V → R := fun v =>
    ⟨A (Pi.single v 1), ⟨Pi.single v 1, rfl⟩⟩
  have hcol (v u : V) : (c v).val u = G.adjMatrix (ZMod 2) u v := by
    change (G.adjMatrix (ZMod 2)).mulVecLin (Pi.single v 1) u = _
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply]
  have htwins (v w : V) (hh : c v = c w) (u : V) :
      G.Adj u v ↔ G.Adj u w := by
    have he := congrArg (fun z : R => z.val u) hh
    simp only [hcol] at he
    by_cases hv : G.Adj u v <;> by_cases hw' : G.Adj u w <;>
      simp [SimpleGraph.adjMatrix_apply, hv, hw'] at he ⊢
  have hinj : Function.Injective c := by
    intro v w hh
    by_contra hne
    obtain ⟨u, z, hz, huz, huniq⟩ :=
      hsmall ({v, w} : Finset V) (by simp) (by simp [hne])
    have ht := htwins v w hh u
    have hz' : z = v ∨ z = w := by simpa using hz
    have huv : G.Adj u v := by
      rcases hz' with h | h
      · simpa only [h] using huz
      · exact ht.mpr (by simpa only [h] using huz)
    have huw : G.Adj u w := by
      rcases hz' with h | h
      · exact ht.mp (by simpa only [h] using huz)
      · simpa only [h] using huz
    exact hne ((huniq v (by simp) huv).trans (huniq w (by simp) huw).symm)
  have hcne (v : V) : c v ≠ 0 := by
    have hv : 0 < G.degree v := by rw [hdeg]; omega
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
    have hc1 : (c v).val w = 1 := by rw [hcol]; simp [hvw.symm]
    intro hh
    have he := congrArg (fun z : R => z.val w) hh
    change (c v).val w = 0 at he
    rw [hc1] at he
    exact one_ne_zero he
  let C : Finset R := Finset.univ.image c
  have hCcard : C.card = n := by
    simpa only [C, n, Finset.card_univ] using
      Finset.card_image_of_injective (Finset.univ : Finset V) hinj
  have hrange : Fintype.card R = 2 ^ r := by
    simpa only [ZMod.card, Fintype.card_fin] using
      Module.card_fintype (Module.finBasis (ZMod 2) R)
  have hbasic : n + 1 ≤ 2 ^ r := by
    have h0 : (0 : R) ∉ C := by
      intro hh
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hh
      exact hcne v hv
    have hh := Finset.card_le_univ (insert (0 : R) C)
    rw [Finset.card_insert_of_notMem h0, hCcard, hrange] at hh
    exact hh
  have hr2 : 2 ≤ r := by
    by_contra hh
    have hc : r = 0 ∨ r = 1 := by omega
    rcases hc with h | h
    · have hp : (2 : ℕ) ^ r = 1 := by rw [h, pow_zero]
      omega
    · have hp : (2 : ℕ) ^ r = 2 := by rw [h, pow_one]
      omega
  have hbound : (1 + D % 2) * (n + 1 + D % 2) ≤ 2 ^ r := by
    rcases Nat.mod_two_eq_zero_or_one D with he | ho
    · simpa only [he, add_zero, one_mul] using hbasic
    · have hodd : Odd D := Nat.odd_iff.mpr ho
      have hnEven : Even n := by
        simpa [hdeg, hodd, n] using G.even_card_odd_degree_vertices
      let p : R → ZMod 2 := fun x => ∑ v : V, x.val v
      have padd (x y : R) : p (x + y) = p x + p y := by
        change (∑ v : V, (x.val v + y.val v)) =
          (∑ v : V, x.val v) + (∑ v : V, y.val v)
        exact Finset.sum_add_distrib
      have pc (v : V) : p (c v) = 1 := by
        have hs : p (c v) = (G.degree v : ZMod 2) := by
          calc
            p (c v) = ∑ u : V, if G.Adj v u then (1 : ZMod 2) else 0 := by
              apply Finset.sum_congr rfl
              intro u _
              rw [hcol]
              simp only [SimpleGraph.adjMatrix_apply, G.adj_comm]
            _ = (((Finset.univ : Finset V).filter
                (fun u => G.Adj v u)).card : ZMod 2) := Finset.sum_boole _ _
            _ = (G.degree v : ZMod 2) := by
              rw [← G.neighborFinset_eq_filter, G.card_neighborFinset_eq_degree]
        rw [hs, hdeg]
        exact ZMod.natCast_eq_one_iff_odd.mpr hodd
      have hself (x : R) : x + x = 0 := by
        apply Subtype.ext
        funext v
        change x.val v + x.val v = 0
        exact ZModModule.add_self _
      have htranslate (S T : Finset R) (t : R)
          (hm : ∀ x : R, x ∈ S ↔ x + t ∈ T) : S.card = T.card := by
        refine Finset.card_bijective (fun x : R => x + t) ?_ hm
        constructor
        · intro x y hxy
          exact add_right_cancel hxy
        · intro y
          refine ⟨y + t, ?_⟩
          change (y + t) + t = y
          rw [add_assoc, hself t, add_zero]
      have hflip : ∀ z : ZMod 2, z = 1 ↔ z + 1 ≠ 1 := by decide
      let P : Finset R := Finset.univ.filter (fun x => p x = 1)
      let E : Finset R := Finset.univ.filter (fun x => p x ≠ 1)
      obtain ⟨a⟩ := ‹Nonempty V›
      have hPE : P.card = E.card := by
        apply htranslate P E (c a)
        intro x
        simpa only [P, E, Finset.mem_filter, Finset.mem_univ,
          true_and, padd, pc] using hflip (p x)
      have hpartition : P.card + E.card = Fintype.card R := by
        simpa only [P, E, Finset.card_univ] using
          Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset R)) (fun x : R => p x = 1)
      have hhalf : 2 * P.card = Fintype.card R := by omega
      have hCPsub : C ⊆ P := by
        intro x hx
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pc v⟩
      have hnP : n ≤ P.card := by
        rw [← hCcard]
        exact Finset.card_le_card hCPsub
      have hstrict : 2 * n < 2 ^ r := by
        by_contra hh
        have hsat : n = P.card := by omega
        have hCP : C = P :=
          Finset.eq_of_subset_of_card_le hCPsub (by omega)
        have ha : 0 < G.degree a := by rw [hdeg]; omega
        obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj a).mp ha
        let t : R := c a + c b
        have htp : p t = 0 := by
          change p (c a + c b) = 0
          simp only [padd, pc]
          exact ZModModule.add_self _
        have hta : t.val a = 1 := by
          change (c a).val a + (c b).val a = 1
          simp [hcol, hab]
        let Q : Finset R := P.filter (fun x => x.val a = 1)
        let Q' : Finset R := P.filter (fun x => x.val a ≠ 1)
        have hQQ : Q.card = Q'.card := by
          apply htranslate Q Q' t
          intro x
          have hp : p (x + t) = p x := by rw [padd, htp, add_zero]
          have hv : (x + t).val a = x.val a + 1 := by
            change x.val a + t.val a = x.val a + 1
            rw [hta]
          simp only [Q, Q', P, Finset.mem_filter, Finset.mem_univ,
            true_and, hp, hv]
          exact and_congr_right (fun _ => hflip (x.val a))
        have hQpartition : Q.card + Q'.card = P.card := by
          simpa only [Q, Q'] using
            Finset.card_filter_add_card_filter_not
              (s := P) (fun x : R => x.val a = 1)
        have hQhalf : 2 * Q.card = P.card := by omega
        have hQeq : Q = (G.neighborFinset a).image c := by
          ext x
          constructor
          · intro hx
            have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
            have hxC : x ∈ C := by rw [hCP]; exact hxP
            obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hxC
            subst x
            refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
            apply (G.mem_neighborFinset a v).mpr
            have hone : (c v).val a = 1 := (Finset.mem_filter.mp hx).2
            by_contra hnot
            have hz : (c v).val a = 0 := by rw [hcol]; simp [hnot]
            exact zero_ne_one (hz.symm.trans hone)
          · intro hx
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
            refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · exact hCPsub
                (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
            · rw [hcol]
              simp [(G.mem_neighborFinset a v).mp hv]
        have hQcard : Q.card = D := by
          calc
            Q.card = ((G.neighborFinset a).image c).card :=
              congrArg Finset.card hQeq
            _ = (G.neighborFinset a).card :=
              Finset.card_image_of_injective _ hinj
            _ = D := (G.card_neighborFinset_eq_degree a).trans (hdeg a)
        have hDn : 2 * D = n := by omega
        have hpowD : 2 ^ r = 4 * D := by omega
        have hr3 : 3 ≤ r := by
          by_contra hh'
          have hr : r = 2 := by omega
          have hp : (2 : ℕ) ^ r = 4 := by rw [hr]; norm_num
          omega
        have hpow8 : (2 : ℕ) ^ r = 8 * 2 ^ (r - 3) := by
          have hh' : r = (r - 3) + 3 := by omega
          calc
            (2 : ℕ) ^ r = 2 ^ ((r - 3) + 3) :=
              congrArg (fun j : ℕ => (2 : ℕ) ^ j) hh'
            _ = 8 * 2 ^ (r - 3) := by rw [pow_add]; ring
        have hDeven : D = 2 * 2 ^ (r - 3) := by omega
        have hmod : D % 2 = 0 := by rw [hDeven]; omega
        omega
      have hpow4 : (2 : ℕ) ^ r = 4 * 2 ^ (r - 2) := by
        have hh : r = (r - 2) + 2 := by omega
        calc
          (2 : ℕ) ^ r = 2 ^ ((r - 2) + 2) :=
            congrArg (fun j : ℕ => (2 : ℕ) ^ j) hh
          _ = 4 * 2 ^ (r - 2) := by rw [pow_add]; ring
      have hstrong : 2 * (n + 2) ≤ 2 ^ r := by
        obtain ⟨m, hm⟩ := hnEven
        omega
      simpa [ho, Nat.add_assoc] using hstrong
  let q : ℕ := D / 2
  have hd : D = 2 * q + D % 2 := by dsimp [q]; omega
  have hdr : (D : ℝ) = 2 * (q : ℝ) + ((D % 2 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((D % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrlt : ((D % 2 : ℕ) : ℝ) < 2 := by
    exact_mod_cast (Nat.mod_lt D (by decide : 0 < (2 : ℕ)))
  have hfloor : Int.floor ((D : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith only [hdr, hr0, hrlt]
  have hrem : (D : ℝ) - 2 * (Int.floor ((D : ℝ) / 2) : ℝ) =
      ((D % 2 : ℕ) : ℝ) := by
    rw [hfloor]
    push_cast
    linarith only [hdr]
  have hdimR : (r : ℝ) + (k : ℝ) = (n : ℝ) := by exact_mod_cast hdim
  have hdiff : (n : ℝ) - (k : ℝ) = (r : ℝ) := by
    linarith only [hdimR]
  change (1 + ((D : ℝ) - 2 * (Int.floor ((D : ℝ) / 2) : ℝ))) *
    (((n : ℝ) + 1) + ((D : ℝ) - 2 * (Int.floor ((D : ℝ) / 2) : ℝ))) ≤
      Real.exp (((n : ℝ) - (k : ℝ)) * Real.log (1 + (1 : ℝ)))
  simp only [hrem, hdiff, show (1 : ℝ) + 1 = 2 by norm_num,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hbound
