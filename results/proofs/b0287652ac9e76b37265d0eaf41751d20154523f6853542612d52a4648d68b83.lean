import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
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
