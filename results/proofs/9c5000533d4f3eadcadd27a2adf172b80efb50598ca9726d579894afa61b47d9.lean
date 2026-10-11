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
theorem model_b019db4c751eaa507b7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (59999999 / 10000000 : ℝ)))) :
    ((1 : ℝ) + ((((Fintype.card V : ℝ) ^ 3) + ((20 : ℝ) * (Fintype.card V : ℝ))) / (48 : ℝ))) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧
      ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  have hg : (((weights.min' hw - 1 : ℕ) : ℝ)) ≥
      (59999999 / 10000000 : ℝ) := h_guard.2.2
  have hmin : 6 ≤ weights.min' hw - 1 := by
    by_contra h
    have hn : weights.min' hw - 1 ≤ 5 := by omega
    have hr : (((weights.min' hw - 1 : ℕ) : ℝ)) ≤ 5 := by
      exact_mod_cast hn
    linarith only [hg, hr]
  have hsmall (S : Finset V) (hS : S.Nonempty) (hcard : S.card ≤ 6) :
      ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    by_contra h
    have hm : S.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS, h⟩, rfl⟩
    have hl : weights.min' hw ≤ S.card := Finset.min'_le weights S.card hm
    omega
  obtain ⟨c⟩ := h_guard.1
  let s0 : Finset V := Finset.univ.filter (fun v => c v = 0)
  have hi0 : ∀ v ∈ s0, ∀ w ∈ s0, ¬ G.Adj v w := by
    intro v hv w hw' hadj
    have hv0 : c v = 0 := (Finset.mem_filter.mp hv).2
    have hw0 : c w = 0 := (Finset.mem_filter.mp hw').2
    exact c.valid hadj (hv0.trans hw0.symm)
  have hi1 : ∀ v ∉ s0, ∀ w ∉ s0, ¬ G.Adj v w := by
    intro v hv w hw' hadj
    have hv0 : c v ≠ 0 := by simpa [s0] using hv
    have hw0 : c w ≠ 0 := by simpa [s0] using hw'
    have hv1 : (c v).val = 1 := by
      have hlt := (c v).isLt
      have hnz : (c v).val ≠ 0 := by
        intro h
        exact hv0 (Fin.ext h)
      omega
    have hw1 : (c w).val = 1 := by
      have hlt := (c w).isLt
      have hnz : (c w).val ≠ 0 := by
        intro h
        exact hw0 (Fin.ext h)
      omega
    exact c.valid hadj (Fin.ext (hv1.trans hw1.symm))
  obtain ⟨s, hsize, hi, hj⟩ : ∃ s : Finset V,
      Fintype.card V ≤ 2 * s.card ∧
      (∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w) ∧
      (∀ v ∉ s, ∀ w ∉ s, ¬ G.Adj v w) := by
    by_cases h : Fintype.card V ≤ 2 * s0.card
    · exact ⟨s0, h, hi0, hi1⟩
    · refine ⟨s0ᶜ, ?_, ?_, ?_⟩
      · have hc := Finset.card_add_card_compl s0
        omega
      · simpa only [Finset.mem_compl] using hi1
      · simpa only [Finset.mem_compl, not_not] using hi0
  let B := {v : V // v ∉ s}
  let M : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let C : Matrix B s (ZMod 2) := fun i j => M i.val j.val
  let e : (↥s ⊕ B) ≃ V := Equiv.sumCompl (fun v : V => v ∈ s)
  let N : Matrix (↥s ⊕ B) (↥s ⊕ B) (ZMod 2) := M.submatrix e e
  have hN : N = Matrix.fromBlocks (0 : Matrix s s (ZMod 2))
      C.transpose C (0 : Matrix B B (ZMod 2)) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · change M i.val j.val = 0
        simp [M, SimpleGraph.adjMatrix_apply, hi i.val i.property j.val j.property]
      · change M i.val j.val = M j.val i.val
        exact (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply j.val i.val
    · rcases j with j | j
      · rfl
      · change M i.val j.val = 0
        simp [M, SimpleGraph.adjMatrix_apply, hj i.val i.property j.val j.property]
  let E : ((↥s ⊕ B) → ZMod 2) ≃ₗ[ZMod 2]
      ((s → ZMod 2) × (B → ZMod 2)) :=
    LinearEquiv.sumArrowLequivProdArrow s B (ZMod 2) (ZMod 2)
  let E' : ((↥s ⊕ B) → ZMod 2) ≃ₗ[ZMod 2]
      ((B → ZMod 2) × (s → ZMod 2)) :=
    E.trans (LinearEquiv.prodComm (ZMod 2) (s → ZMod 2) (B → ZMod 2))
  let P : ((s → ZMod 2) × (B → ZMod 2)) →ₗ[ZMod 2]
      ((B → ZMod 2) × (s → ZMod 2)) :=
    C.mulVecLin.prodMap C.transpose.mulVecLin
  have hconj : (E'.toLinearMap.comp N.mulVecLin).comp E.symm.toLinearMap = P := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · funext i
      change Matrix.mulVec N (Sum.elim x.1 x.2) (Sum.inr i) =
        Matrix.mulVec C x.1 i
      rw [hN, Matrix.fromBlocks_mulVec]
      simp [Function.comp_def]
    · funext i
      change Matrix.mulVec N (Sum.elim x.1 x.2) (Sum.inl i) =
        Matrix.mulVec C.transpose x.2 i
      rw [hN, Matrix.fromBlocks_mulVec]
      simp [Function.comp_def]
  have hPrange : Module.finrank (ZMod 2) (LinearMap.range P) = N.rank := by
    calc
      _ = Module.finrank (ZMod 2)
          (LinearMap.range (E'.toLinearMap.comp N.mulVecLin)) := by
        rw [← hconj, LinearMap.range_comp_of_range_eq_top _ E.symm.range]
      _ = N.rank := by
        rw [LinearMap.range_comp]
        exact E'.finrank_map_eq (LinearMap.range N.mulVecLin)
  have hPprod : Module.finrank (ZMod 2) (LinearMap.range P) =
      C.rank + C.transpose.rank := by
    calc
      _ = Module.finrank (ZMod 2)
          ((LinearMap.range C.mulVecLin).prod
            (LinearMap.range C.transpose.mulVecLin)) := by
        dsimp only [P]
        rw [LinearMap.range_prodMap]
      _ = Module.finrank (ZMod 2)
          ((LinearMap.range C.mulVecLin) ×
            (LinearMap.range C.transpose.mulVecLin)) :=
        (Submodule.prodEquiv _ _).finrank_eq
      _ = C.rank + C.transpose.rank := by
        simp only [Module.finrank_prod, Matrix.rank]
  have hMrank : M.rank = 2 * C.rank := by
    calc
      M.rank = N.rank := (Matrix.rank_submatrix M e e).symm
      _ = C.rank + C.transpose.rank := hPrange.symm.trans hPprod
      _ = 2 * C.rank := by simp only [Matrix.rank_transpose, two_mul]
  let L : Finset (Finset V) :=
    (Finset.range 4).biUnion (fun k => s.powersetCard k)
  have hL (S : Finset V) (hS : S ∈ L) : S ⊆ s ∧ S.card ≤ 3 := by
    obtain ⟨k, hk, hSk⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hSk
    have hlt := Finset.mem_range.mp hk
    exact ⟨hsub, by omega⟩
  have hdisj : ((Finset.range 4 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => s.powersetCard k) := by
    intro i hi' j hj' hij
    exact Finset.disjoint_powersetCard_of_ne hij s s
  have hLcard : L.card = 1 + s.card + s.card.choose 2 + s.card.choose 3 := by
    dsimp only [L]
    rw [Finset.card_biUnion hdisj]
    simp [Finset.card_powersetCard, Finset.sum_range_succ]
  let x : Finset V → (s → ZMod 2) := fun S u =>
    if u.val ∈ S then 1 else 0
  let q : Finset V → LinearMap.range C.mulVecLin := fun S =>
    ⟨C.mulVecLin (x S), ⟨x S, rfl⟩⟩
  have hq : Set.InjOn q (L : Set (Finset V)) := by
    intro S hS T hT hST
    obtain ⟨hSs, hSc⟩ := hL S hS
    obtain ⟨hTs, hTc⟩ := hL T hT
    by_contra hne
    let D : Finset V := symmDiff S T
    have hDnonempty : D.Nonempty := Finset.symmDiff_nonempty.mpr hne
    have hDcard : D.card ≤ 6 := by
      have hd : D.card ≤ (S ∪ T).card :=
        Finset.card_le_card Finset.symmDiff_subset_union
      have hu := Finset.card_union_le S T
      omega
    have hDsub : D ⊆ s := by
      intro u hu
      rcases Finset.mem_symmDiff.mp hu with h | h
      · exact hSs h.1
      · exact hTs h.1
    obtain ⟨v, w, hwD, hvw, huniq⟩ := hsmall D hDnonempty hDcard
    have hws : w ∈ s := hDsub hwD
    have hvns : v ∉ s := by
      intro hv
      exact hi v hv w hws hvw
    have hxD : x D = x S + x T := by
      funext u
      by_cases huS : u.val ∈ S <;> by_cases huT : u.val ∈ T <;>
        simp [x, D, Finset.mem_symmDiff, huS, huT, ZModModule.add_self]
    have hST' : C.mulVecLin (x S) = C.mulVecLin (x T) :=
      congrArg (fun z : LinearMap.range C.mulVecLin => z.val) hST
    have hzero : C.mulVecLin (x D) = 0 := by
      rw [hxD, map_add, hST']
      funext u
      exact ZModModule.add_self _
    have hvzero := congrFun hzero (⟨v, hvns⟩ : B)
    change (∑ u : s, M v u.val * (if u.val ∈ D then 1 else 0)) = 0 at hvzero
    have hvone : (∑ u : s, M v u.val * (if u.val ∈ D then 1 else 0)) = 1 := by
      calc
        _ = M v w * (if w ∈ D then 1 else 0) := by
          refine Finset.sum_eq_single (⟨w, hws⟩ : s) ?_ ?_
          · intro u hu hune
            by_cases huD : u.val ∈ D
            · have hnadj : ¬ G.Adj v u.val := by
                intro hadj
                apply hune
                exact Subtype.ext (huniq u.val huD hadj)
              simp [M, SimpleGraph.adjMatrix_apply, hnadj]
            · simp [huD]
          · simp
        _ = 1 := by simp [M, SimpleGraph.adjMatrix_apply, hvw, hwD]
    exact one_ne_zero (hvone.symm.trans hvzero)
  have hcount : 1 + s.card + s.card.choose 2 + s.card.choose 3 ≤ 2 ^ C.rank := by
    calc
      _ = L.card := hLcard.symm
      _ = (L.image q).card := (Finset.card_image_of_injOn hq).symm
      _ ≤ Fintype.card (LinearMap.range C.mulVecLin) := Finset.card_le_univ _
      _ = 2 ^ C.rank := by
        simpa only [ZMod.card, Matrix.rank] using
          (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range C.mulVecLin))
  have hchoose3 (a : ℕ) : (6 : ℝ) * (a.choose 3 : ℝ) =
      (a : ℝ) * ((a : ℝ) - 1) * ((a : ℝ) - 2) := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.cast_add, Nat.cast_succ, Nat.cast_choose_two ℝ a]
      nlinarith only [ih]
  have hcountR : (1 : ℝ) + (s.card : ℝ) + (s.card.choose 2 : ℝ) +
      (s.card.choose 3 : ℝ) ≤ (2 : ℝ) ^ C.rank := by
    exact_mod_cast hcount
  have hvolume : (1 : ℝ) + ((s.card : ℝ) ^ 3 + 5 * (s.card : ℝ)) / 6 ≤
      (2 : ℝ) ^ C.rank := by
    rw [Nat.cast_choose_two ℝ s.card] at hcountR
    have hc3 := hchoose3 s.card
    nlinarith only [hc3, hcountR]
  have hsizeR : (Fintype.card V : ℝ) ≤ 2 * (s.card : ℝ) := by
    exact_mod_cast hsize
  have hcube : (Fintype.card V : ℝ) ^ 3 ≤ (2 * (s.card : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hsizeR 3
  have hlarge : (1 : ℝ) + ((Fintype.card V : ℝ) ^ 3 +
      20 * (Fintype.card V : ℝ)) / 48 ≤
      1 + ((s.card : ℝ) ^ 3 + 5 * (s.card : ℝ)) / 6 := by
    nlinarith only [hsizeR, hcube]
  have hdim : M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have htotal : Fintype.card V =
      Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * C.rank := by
    rw [hMrank] at hdim
    omega
  have hreal : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) =
      2 * (C.rank : ℝ) := by
    have hc : (Fintype.card V : ℝ) =
        (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) +
        2 * (C.rank : ℝ) := by
      exact_mod_cast htotal
    linarith only [hc]
  have hhalf : (2 : ℝ) * (C.rank : ℝ) / 2 = (C.rank : ℝ) := by ring
  have hexp : Real.exp ((C.rank : ℝ) * Real.log (1 + (1 : ℝ))) =
      (2 : ℝ) ^ C.rank := by
    simp only [show (1 : ℝ) + 1 = 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change (1 : ℝ) + ((Fintype.card V : ℝ) ^ 3 +
      20 * (Fintype.card V : ℝ)) / 48 ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ)) / 2 *
      Real.log (1 + (1 : ℝ)))
  rw [hreal, hhalf, hexp]
  exact hlarge.trans hvolume
