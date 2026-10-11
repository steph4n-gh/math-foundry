import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

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

theorem model_8507aba979de2b196665 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Int.floor (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ))) : ℝ) = (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) := by
  have h := model_7f80b6911ecd9dc4c880 G
  linarith only [h]

theorem model_839d3b7a6b536e9e20f2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) + ((Int.ceil ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) / (2 : ℝ))) : ℝ)))) ≤ ((Fintype.card V : ℝ) + (4 : ℝ)) := by
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
  change (k : ℝ) + 2 * ((d : ℝ) + (Int.ceil ((d : ℝ) / 2) : ℝ)) ≤ (n : ℝ) + 4
  have hkreal : (29999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2
  have hk : 3 ≤ k := by
    by_contra h
    have hle : (k : ℝ) ≤ 2 := by
      exact_mod_cast (show k ≤ 2 by omega)
    linarith
  have hbit : ∀ a b : ZMod 2,
      (if a ≠ 0 then (1 : ℕ) else 0) +
        (if b ≠ 0 then 1 else 0) +
        (if a + b ≠ 0 then 1 else 0) ≤ 2 := by decide
  have hbit_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hd : ∀ t : V → ZMod 2, t ≠ 0 → A t = 0 → d ≤ hammingNorm t := by
    intro t ht hAt
    have hm : hammingNorm t ∈ weights := by
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht, hAt⟩, rfl⟩))
    exact Finset.min'_le weights (hammingNorm t) hm
  obtain ⟨c⟩ := h_guard.1
  let L := {v : V // c v = 0}
  let R := {v : V // c v ≠ 0}
  let B : Matrix R L (ZMod 2) :=
    Matrix.of fun i j => (G.adjMatrix (ZMod 2)) i.val j.val
  let BT : Matrix L R (ZMod 2) := Matrix.transpose B
  let C0 : Submodule (ZMod 2) (L → ZMod 2) := LinearMap.ker B.mulVecLin
  let C1 : Submodule (ZMod 2) (R → ZMod 2) := LinearMap.ker BT.mulVecLin
  let k0 : ℕ := Module.finrank (ZMod 2) C0
  let k1 : ℕ := Module.finrank (ZMod 2) C1
  let r : ℕ := Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin)
  have hcol : ∀ a b : Fin 2, a ≠ 0 → b ≠ 0 → a = b := by decide
  have hz0 (v w : L) : (G.adjMatrix (ZMod 2)) v.val w.val = 0 := by
    have hn : ¬G.Adj v.val w.val :=
      fun h => c.valid h (v.property.trans w.property.symm)
    simp [SimpleGraph.adjMatrix_apply, hn]
  have hz1 (v w : R) : (G.adjMatrix (ZMod 2)) v.val w.val = 0 := by
    have hn : ¬G.Adj v.val w.val :=
      fun h => c.valid h (hcol (c v.val) (c w.val) v.property w.property)
    simp [SimpleGraph.adjMatrix_apply, hn]
  have hsym (v w : V) :
      (G.adjMatrix (ZMod 2)) v w = (G.adjMatrix (ZMod 2)) w v :=
    (SimpleGraph.isSymm_adjMatrix (α := ZMod 2) G).apply w v
  have hsplit (t : V → ZMod 2) :
      (∑ v : V, t v) = (∑ v : L, t v.val) + (∑ v : R, t v.val) :=
    (Fintype.sum_subtype_add_sum_subtype (fun v : V => c v = 0) t).symm
  have haL (t : V → ZMod 2) (i : L) :
      A t i.val = BT.mulVecLin (fun j : R => t j.val) i := by
    change (∑ v : V, (G.adjMatrix (ZMod 2)) i.val v * t v) =
      ∑ j : R, (G.adjMatrix (ZMod 2)) j.val i.val * t j.val
    have hz : (∑ j : L, (G.adjMatrix (ZMod 2)) i.val j.val * t j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hz0 i j, zero_mul]
    rw [hsplit, hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym i.val j.val]
  have haR (t : V → ZMod 2) (i : R) :
      A t i.val = B.mulVecLin (fun j : L => t j.val) i := by
    change (∑ v : V, (G.adjMatrix (ZMod 2)) i.val v * t v) =
      ∑ j : L, (G.adjMatrix (ZMod 2)) i.val j.val * t j.val
    have hz : (∑ j : R, (G.adjMatrix (ZMod 2)) i.val j.val * t j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hz1 i j, zero_mul]
    rw [hsplit, hz, add_zero]
  let f : C →ₗ[ZMod 2] C0 × C1 :=
    { toFun := fun x =>
        (⟨fun i : L => (x : V → ZMod 2) i.val, by
            change B.mulVecLin (fun i : L => (x : V → ZMod 2) i.val) = 0
            funext i
            exact (haR (x : V → ZMod 2) i).symm.trans (congrFun x.property i.val)⟩,
         ⟨fun i : R => (x : V → ZMod 2) i.val, by
            change BT.mulVecLin (fun i : R => (x : V → ZMod 2) i.val) = 0
            funext i
            exact (haL (x : V → ZMod 2) i).symm.trans (congrFun x.property i.val)⟩)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext v
    by_cases hv : c v = 0
    · exact congrArg (fun z : C0 × C1 => (z.1 : L → ZMod 2) ⟨v, hv⟩) hxy
    · exact congrArg (fun z : C0 × C1 => (z.2 : R → ZMod 2) ⟨v, hv⟩) hxy
  have hkk : k ≤ k0 + k1 := by
    simpa only [k, k0, k1, Module.finrank_prod] using
      (LinearMap.finrank_le_finrank_of_injective hf)
  have htrans : Module.finrank (ZMod 2) (LinearMap.range BT.mulVecLin) = r := by
    let eL := dotProductEquiv (ZMod 2) L
    let eR := dotProductEquiv (ZMod 2) R
    have hdual : eL.toLinearMap.comp BT.mulVecLin =
        B.mulVecLin.dualMap.comp eR.toLinearMap := by
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro x
      change dotProduct (BT.mulVecLin y) x = dotProduct y (B.mulVecLin x)
      simp only [BT, Matrix.mulVecLin_apply, Matrix.mulVec_transpose,
        Matrix.dotProduct_mulVec]
    have heq := congrArg
      (fun g : (R → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (L → ZMod 2) =>
        Module.finrank (ZMod 2) (LinearMap.range g)) hdual
    rw [LinearMap.range_comp,
      eL.finrank_map_eq (LinearMap.range BT.mulVecLin),
      LinearMap.range_comp_of_range_eq_top B.mulVecLin.dualMap eR.range,
      LinearMap.finrank_range_dualMap_eq_finrank_range] at heq
    exact heq
  have hr0 : r + k0 = Fintype.card L := by
    simpa only [r, k0, C0, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_add_finrank_ker B.mulVecLin)
  have hr1 : r + k1 = Fintype.card R := by
    have hh := LinearMap.finrank_range_add_finrank_ker BT.mulVecLin
    change Module.finrank (ZMod 2) (LinearMap.range BT.mulVecLin) + k1 =
      Module.finrank (ZMod 2) (R → ZMod 2) at hh
    rw [htrans, Module.finrank_fintype_fun_eq_card] at hh
    exact hh
  have hcard : Fintype.card L + Fintype.card R = n := by
    simpa only [Fintype.card_sum] using
      (Fintype.card_congr (Equiv.sumCompl (fun v : V => c v = 0)))
  have hknr : k + 2 * r ≤ n := by omega
  have hlarge : 2 ≤ k0 ∨ 2 ≤ k1 := by omega
  let E : (L → ZMod 2) → (R → ZMod 2) → (V → ZMod 2) :=
    fun x y v => if h : c v = 0 then x ⟨v, h⟩ else y ⟨v, h⟩
  have hEL (x : L → ZMod 2) (y : R → ZMod 2) (i : L) :
      E x y i.val = x i := by simp [E, i.property]
  have hER (x : L → ZMod 2) (y : R → ZMod 2) (i : R) :
      E x y i.val = y i := by simp [E, i.property]
  have hEnorm (x : L → ZMod 2) (y : R → ZMod 2) :
      hammingNorm (E x y) = hammingNorm x + hammingNorm y := by
    simp only [hammingNorm, Finset.card_filter]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun v : V => c v = 0)
      (fun v => if E x y v ≠ 0 then (1 : ℕ) else 0)]
    simp only [hEL, hER]
    congr 1 <;> apply Finset.sum_congr (by ext i; simp) <;>
      intro i hi <;> split_ifs <;> rfl
  have heker (x : C0) (y : C1) :
      A (E (x : L → ZMod 2) (y : R → ZMod 2)) = 0 := by
    have h0 : (fun i : L => E (x : L → ZMod 2) (y : R → ZMod 2) i.val) =
        (x : L → ZMod 2) := funext (fun i => hEL _ _ i)
    have h1 : (fun i : R => E (x : L → ZMod 2) (y : R → ZMod 2) i.val) =
        (y : R → ZMod 2) := funext (fun i => hER _ _ i)
    funext v
    by_cases hv : c v = 0
    · rw [haL (E (x : L → ZMod 2) (y : R → ZMod 2)) ⟨v, hv⟩, h1]
      exact congrFun y.property ⟨v, hv⟩
    · rw [haR (E (x : L → ZMod 2) (y : R → ZMod 2)) ⟨v, hv⟩, h0]
      exact congrFun x.property ⟨v, hv⟩
  have hd0 (x : C0) (hx : x ≠ 0) : d ≤ hammingNorm (x : L → ZMod 2) := by
    have hne : E (x : L → ZMod 2) 0 ≠ 0 := by
      intro heq
      apply hx
      apply Subtype.ext
      funext i
      change (x : L → ZMod 2) i = 0
      simpa only [hEL, Pi.zero_apply] using congrFun heq i.val
    have hh := hd (E (x : L → ZMod 2) 0) hne (heker x 0)
    simpa only [hEnorm, hammingNorm_zero, add_zero] using hh
  have hd1 (y : C1) (hy : y ≠ 0) : d ≤ hammingNorm (y : R → ZMod 2) := by
    have hne : E 0 (y : R → ZMod 2) ≠ 0 := by
      intro heq
      apply hy
      apply Subtype.ext
      funext i
      change (y : R → ZMod 2) i = 0
      simpa only [hER, Pi.zero_apply] using congrFun heq i.val
    have hh := hd (E 0 (y : R → ZMod 2)) hne (heker 0 y)
    simpa only [hEnorm, hammingNorm_zero, zero_add] using hh
  have hsmall : ∀ (T : Type _) [Fintype T] [DecidableEq T]
      (D : Submodule (ZMod 2) (T → ZMod 2)) (q : ℕ),
      q + Module.finrank (ZMod 2) D = Fintype.card T →
      2 ≤ Module.finrank (ZMod 2) D →
      (∀ x : D, x ≠ 0 → d ≤ hammingNorm (x : T → ZMod 2)) →
      3 * d ≤ 2 * q + 4 := by
    intro T instT instDecT D q hdim hkD hdist
    let l : ℕ := Module.finrank (ZMod 2) D
    let m : ℕ := Fintype.card T
    change q + l = m at hdim
    change 2 ≤ l at hkD
    have hlm : l ≤ m := by omega
    obtain ⟨s, hsu, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset T)) (n := l - 2)
      (by simpa only [Finset.card_univ] using (Nat.sub_le l 2).trans hlm)
    let p : D →ₗ[ZMod 2] (s → ZMod 2) :=
      { toFun := fun w i => (w : T → ZMod 2) i.val
        map_add' := by intro w z; rfl
        map_smul' := by intro a w; rfl }
    have hpr : Module.finrank (ZMod 2) (LinearMap.range p) ≤ l - 2 := by
      calc
        _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
        _ = s.card := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
        _ = l - 2 := hs
    have hpdim : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker p) := by
      have heq := LinearMap.finrank_range_add_finrank_ker p
      change Module.finrank (ZMod 2) (LinearMap.range p) +
        Module.finrank (ZMod 2) (LinearMap.ker p) = l at heq
      omega
    obtain ⟨z, hz⟩ := exists_linearIndependent_of_le_finrank
      (R := ZMod 2) (M := LinearMap.ker p) hpdim
    let x : T → ZMod 2 := (z 0).val.val
    let y : T → ZMod 2 := (z 1).val.val
    have hxy : x + y ≠ 0 := by
      intro heq
      have hzeq : z 0 = z 1 := by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact hbit_eq (x i) (y i) (congrFun heq i)
      exact (by decide : (0 : Fin 2) ≠ 1) (hz.injective hzeq)
    have hdx : d ≤ hammingNorm x := hdist (z 0).val (by
      intro heq
      apply hz.ne_zero 0
      exact Subtype.ext heq)
    have hdy : d ≤ hammingNorm y := hdist (z 1).val (by
      intro heq
      apply hz.ne_zero 1
      exact Subtype.ext heq)
    have hdxy : d ≤ hammingNorm (x + y) :=
      hdist ((z 0).val + (z 1).val) (by
        intro heq
        apply hxy
        exact congrArg (fun w : D => (w : T → ZMod 2)) heq)
    have hxs : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have heq : p (z 0).val = 0 := LinearMap.mem_ker.mp (z 0).property
      exact congrFun heq ⟨i, hi⟩
    have hys : ∀ i ∈ s, y i = 0 := by
      intro i hi
      have heq : p (z 1).val = 0 := LinearMap.mem_ker.mp (z 1).property
      exact congrFun heq ⟨i, hi⟩
    have hpoint : ∀ i : T,
        (if x i ≠ 0 then (1 : ℕ) else 0) +
          (if y i ≠ 0 then 1 else 0) +
          (if (x + y) i ≠ 0 then 1 else 0) ≤
            if i ∈ s then 0 else 2 := by
      intro i
      by_cases hi : i ∈ s
      · simp [hi, hxs i hi, hys i hi, Pi.add_apply]
      · simpa [hi, Pi.add_apply] using hbit (x i) (y i)
    have hcomp : (Finset.univ : Finset T).filter (fun i => i ∉ s) = sᶜ := by
      ext i
      simp
    have hsum : hammingNorm x + hammingNorm y + hammingNorm (x + y) ≤
        2 * (m - s.card) := by
      calc
        _ = ∑ i : T,
            ((if x i ≠ 0 then (1 : ℕ) else 0) +
              (if y i ≠ 0 then 1 else 0) +
              (if (x + y) i ≠ 0 then 1 else 0)) := by
          simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
        _ ≤ ∑ i : T, if i ∈ s then (0 : ℕ) else 2 :=
          Finset.sum_le_sum (fun i _ => hpoint i)
        _ = 2 * (m - s.card) := by
          rw [Finset.sum_ite]
          simp [hcomp, Finset.card_compl, m, Nat.mul_comm]
    have h3d : 3 * d ≤ 2 * (m - s.card) := by omega
    have hlen : m - s.card = q + 2 := by omega
    omega
  have h3d : 3 * d ≤ 2 * r + 4 := by
    rcases hlarge with hl | hr
    · exact hsmall L C0 r hr0 hl hd0
    · exact hsmall R C1 r hr1 hr hd1
  have h3dR : (3 : ℝ) * (d : ℝ) ≤ 2 * (r : ℝ) + 4 := by
    exact_mod_cast h3d
  have hceil : Int.ceil ((d : ℝ) / 2) ≤ (r : ℤ) + 2 - (d : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hceilR : (Int.ceil ((d : ℝ) / 2) : ℝ) ≤ (r : ℝ) + 2 - (d : ℝ) := by
    exact_mod_cast hceil
  have hknrR : (k : ℝ) + 2 * (r : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hknr
  linarith

theorem model_e2fedcd7edb750c79aa1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) + ((Int.ceil ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) / (2 : ℝ))) : ℝ)))) ≤ ((Fintype.card V : ℝ) + (4 : ℝ)) := by
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
  change (k : ℝ) + 2 * ((d : ℝ) + (Int.ceil ((d : ℝ) / 2) : ℝ)) ≤
    (n : ℝ) + 4
  have hkreal : (19999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2
  have hk : 2 ≤ k := by
    by_contra h
    have hle : (k : ℝ) ≤ 1 := by
      exact_mod_cast (show k ≤ 1 by omega)
    linarith
  by_cases hk3 : 3 ≤ k
  · exact model_839d3b7a6b536e9e20f2 G
      ⟨h_guard.1.colorable_two, by
        change (29999999 / 10000000 : ℝ) ≤ (k : ℝ)
        have hle : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        linarith⟩
  have hk2 : k = 2 := by omega
  have hd : ∀ t : V → ZMod 2, t ≠ 0 → A t = 0 → d ≤ hammingNorm t := by
    intro t ht hAt
    have hm : hammingNorm t ∈ weights := by
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht, hAt⟩, rfl⟩))
    exact Finset.min'_le weights (hammingNorm t) hm
  have hsupport : ∀ t : V → ZMod 2, A t = 0 →
      ∀ u v : V, G.Adj u v → t u = 0 ∨ t v = 0 := by
    intro t hAt u v huv
    by_cases hu : t u = 0
    · exact Or.inl hu
    by_cases hv : t v = 0
    · exact Or.inr hv
    exfalso
    let T := {w : V // t w ≠ 0}
    let H : SimpleGraph T := G.induce {w : V | t w ≠ 0}
    let u0 : T := ⟨u, hu⟩
    let v0 : T := ⟨v, hv⟩
    letI : Nonempty T := ⟨u0⟩
    have hH : H.IsAcyclic := h_guard.1.induce {w : V | t w ≠ 0}
    have huv0 : H.Adj u0 v0 := huv
    obtain ⟨a, b, p, hp, hmax⟩ :=
      SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
    have hlen : 1 ≤ p.length := by
      simpa using hmax u0 v0 huv0.toWalk
        (SimpleGraph.Walk.IsPath.of_adj huv0)
    have hnil : ¬p.Nil := by
      intro h
      have hzero := h.length_eq_zero
      omega
    have huniq (w : T) (haw : H.Adj a w) : w = p.snd := by
      apply hH.eq_snd_of_adj_start hp haw
      by_contra hnot
      have hlong := hmax w b (p.cons haw.symm) (hp.cons hnot)
      simp only [SimpleGraph.Walk.length_cons] at hlong
      omega
    have hpAdj : G.Adj a.val p.snd.val := p.adj_snd hnil
    have hrow : A t a.val = t p.snd.val := by
      change (∑ w : V, (G.adjMatrix (ZMod 2)) a.val w * t w) = t p.snd.val
      rw [Finset.sum_eq_single p.snd.val]
      · simp [SimpleGraph.adjMatrix_apply, hpAdj]
      · intro w _ hne
        by_cases htw : t w = 0
        · simp [htw]
        · have hn : ¬G.Adj a.val w := by
            intro haw
            have heq : (⟨w, htw⟩ : T) = p.snd := huniq ⟨w, htw⟩ haw
            exact hne (congrArg Subtype.val heq)
          simp [SimpleGraph.adjMatrix_apply, hn]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    exact p.snd.property (hrow.symm.trans (congrFun hAt a.val))
  have hbit : ∀ a b : ZMod 2,
      (if a ≠ 0 then (1 : ℕ) else 0) +
        (if b ≠ 0 then 1 else 0) +
        (if a + b ≠ 0 then 1 else 0) ≤ 2 := by decide
  have hbit_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hscalar : ∀ a b c e : ZMod 2,
      (a = 0 ∨ c = 0) → (b = 0 ∨ e = 0) →
      (a + b = 0 ∨ c + e = 0) →
      (a = 0 ∧ b = 0) ∨ (c = 0 ∧ e = 0) := by
    intro a b c e hac hbe hs
    rcases hac with ha | hc
    · rcases hbe with hb | he
      · exact Or.inl ⟨ha, hb⟩
      · rcases hs with hab | hce
        · exact Or.inl ⟨ha, by simpa [ha] using hab⟩
        · exact Or.inr ⟨by simpa [he] using hce, he⟩
    · rcases hbe with hb | he
      · rcases hs with hab | hce
        · exact Or.inl ⟨by simpa [hb] using hab, hb⟩
        · exact Or.inr ⟨hc, by simpa [hc] using hce⟩
      · exact Or.inr ⟨hc, he⟩
  obtain ⟨z, hz⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := C) hk
  let x : V → ZMod 2 := (z 0).val
  let y : V → ZMod 2 := (z 1).val
  have hx : x ≠ 0 := by
    intro heq
    apply hz.ne_zero 0
    exact Subtype.ext heq
  have hy : y ≠ 0 := by
    intro heq
    apply hz.ne_zero 1
    exact Subtype.ext heq
  have hxy : x + y ≠ 0 := by
    intro heq
    have hzeq : z 0 = z 1 := by
      apply Subtype.ext
      funext i
      exact hbit_eq (x i) (y i) (congrFun heq i)
    exact (by decide : (0 : Fin 2) ≠ 1) (hz.injective hzeq)
  have hAx : A x = 0 := (z 0).property
  have hAy : A y = 0 := (z 1).property
  have hAxy : A (x + y) = 0 := by
    rw [map_add, hAx, hAy, add_zero]
  have hdx : d ≤ hammingNorm x := hd x hx hAx
  have hdy : d ≤ hammingNorm y := hd y hy hAy
  have hdxy : d ≤ hammingNorm (x + y) := hd (x + y) hxy hAxy
  let s : Finset V := Finset.univ.filter (fun v => x v ≠ 0 ∨ y v ≠ 0)
  let L := {v : V // v ∈ s}
  let R := {v : V // v ∉ s}
  have hSind (i j : L) : ¬G.Adj i.val j.val := by
    intro hij
    have hzero := hscalar (x i.val) (y i.val) (x j.val) (y j.val)
      (hsupport x hAx i.val j.val hij)
      (hsupport y hAy i.val j.val hij)
      (by simpa only [Pi.add_apply] using
        hsupport (x + y) hAxy i.val j.val hij)
    rcases hzero with hi | hj
    · rcases (Finset.mem_filter.mp i.property).2 with hix | hiy
      · exact hix hi.1
      · exact hiy hi.2
    · rcases (Finset.mem_filter.mp j.property).2 with hjx | hjy
      · exact hjx hj.1
      · exact hjy hj.2
  let B : Matrix R L (ZMod 2) :=
    Matrix.of fun i j => (G.adjMatrix (ZMod 2)) i.val j.val
  let E : (L → ZMod 2) → (V → ZMod 2) :=
    fun t v => if h : v ∈ s then t ⟨v, h⟩ else 0
  have hEL (t : L → ZMod 2) (i : L) : E t i.val = t i := by
    simp [E, i.property]
  have hsplit (t : V → ZMod 2) :
      (∑ v : V, t v) = (∑ v : L, t v.val) + (∑ v : R, t v.val) := by
    convert (Fintype.sum_subtype_add_sum_subtype (fun v : V => v ∈ s) t).symm using 1 <;>
      congr 1 <;> apply Finset.sum_congr (by ext i; simp) <;>
      intro i hi <;> rfl
  have hsumE (t : L → ZMod 2) (v : V) :
      A (E t) v = ∑ i : L, (G.adjMatrix (ZMod 2)) v i.val * t i := by
    change (∑ w : V, (G.adjMatrix (ZMod 2)) v w * E t w) =
      ∑ i : L, (G.adjMatrix (ZMod 2)) v i.val * t i
    rw [hsplit]
    have hzero : (∑ i : R, (G.adjMatrix (ZMod 2)) v i.val * E t i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [E, i.property]
    rw [hzero, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [hEL]
  have heker (t : LinearMap.ker B.mulVecLin) :
      A (E (t : L → ZMod 2)) = 0 := by
    funext v
    rw [hsumE]
    by_cases hv : v ∈ s
    · apply Finset.sum_eq_zero
      intro i _
      have hn : ¬G.Adj v i.val := hSind ⟨v, hv⟩ i
      simp [SimpleGraph.adjMatrix_apply, hn]
    · change B.mulVecLin (t : L → ZMod 2) ⟨v, hv⟩ = 0
      exact congrFun t.property ⟨v, hv⟩
  let e : LinearMap.ker B.mulVecLin →ₗ[ZMod 2] C :=
    { toFun := fun t => ⟨E (t : L → ZMod 2), heker t⟩
      map_add' := by
        intro t u
        apply Subtype.ext
        funext v
        by_cases hv : v ∈ s <;> simp [E, hv]
      map_smul' := by
        intro a t
        apply Subtype.ext
        funext v
        by_cases hv : v ∈ s <;> simp [E, hv] }
  have he : Function.Injective e := by
    intro t u htu
    apply Subtype.ext
    funext i
    have hh := congrArg (fun w : C => (w : V → ZMod 2) i.val) htu
    change E (t : L → ZMod 2) i.val = E (u : L → ZMod 2) i.val at hh
    simpa only [hEL] using hh
  have hbk : Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) ≤ 2 := by
    have hh := LinearMap.finrank_le_finrank_of_injective he
    change Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) ≤ k at hh
    omega
  have hbr : Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) ≤
      Fintype.card R := by
    calc
      _ ≤ Module.finrank (ZMod 2) (R → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card R := by rw [Module.finrank_fintype_fun_eq_card]
  have hcard : Fintype.card L + Fintype.card R = n := by
    simpa only [Fintype.card_sum] using
      (Fintype.card_congr (Equiv.sumCompl (fun v : V => v ∈ s)))
  have hleft : Fintype.card L = s.card := Fintype.card_coe s
  have hlen : 2 * s.card ≤ n + 2 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hdim
    omega
  have hpoint : ∀ i : V,
      (if x i ≠ 0 then (1 : ℕ) else 0) +
        (if y i ≠ 0 then 1 else 0) +
        (if (x + y) i ≠ 0 then 1 else 0) ≤
          if i ∈ s then 2 else 0 := by
    intro i
    by_cases hi : i ∈ s
    · simpa [hi, Pi.add_apply] using hbit (x i) (y i)
    · have hx0 : x i = 0 := by
        by_contra hxi
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hxi⟩)
      have hy0 : y i = 0 := by
        by_contra hyi
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr hyi⟩)
      simp [hi, hx0, hy0, Pi.add_apply]
  have hsfilter : (Finset.univ : Finset V).filter (fun i => i ∈ s) = s := by
    ext i
    simp
  have hsum : hammingNorm x + hammingNorm y + hammingNorm (x + y) ≤
      2 * s.card := by
    calc
      _ = ∑ i : V,
          ((if x i ≠ 0 then (1 : ℕ) else 0) +
            (if y i ≠ 0 then 1 else 0) +
            (if (x + y) i ≠ 0 then 1 else 0)) := by
        simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
      _ ≤ ∑ i : V, if i ∈ s then (2 : ℕ) else 0 :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = 2 * s.card := by
        rw [Finset.sum_ite]
        simp [hsfilter, Nat.mul_comm]
  have h3d : 3 * d ≤ 2 * s.card := by omega
  have h3dR : (3 : ℝ) * (d : ℝ) ≤ 2 * (s.card : ℝ) := by
    exact_mod_cast h3d
  have hceil : Int.ceil ((d : ℝ) / 2) ≤ (s.card : ℤ) - (d : ℤ) := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hceilR : (Int.ceil ((d : ℝ) / 2) : ℝ) ≤
      (s.card : ℝ) - (d : ℝ) := by
    exact_mod_cast hceil
  have hlenR : (2 : ℝ) * (s.card : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast hlen
  have hk2R : (k : ℝ) = 2 := by exact_mod_cast hk2
  linarith

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem model_4484035064be73e8a4fc {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (4 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let L : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  have hmin : G.minDegree = 4 := by
    have ha := abs_le.mp h_guard.2.1
    have hu : (G.minDegree : ℝ) < (5 : ℝ) := by
      linarith only [ha.2]
    have hl : (3 : ℝ) < (G.minDegree : ℝ) := by
      linarith only [ha.1]
    have hu' : G.minDegree < 5 := by exact_mod_cast hu
    have hl' : 3 < G.minDegree := by exact_mod_cast hl
    omega
  obtain ⟨d, hd⟩ := h_guard.1
  have hregular : G.IsRegularOfDegree 4 := by
    intro v
    letI : Nonempty V := ⟨v⟩
    calc
      G.degree v = d := hd v
      _ = G.minDegree := hd.minDegree_eq.symm
      _ = 4 := hmin
  have hone : L (1 : V → ZMod 2) = 0 := by
    ext v
    change (Matrix.mulVec (G.adjMatrix (ZMod 2))
      (Function.const V (1 : ZMod 2))) v = 0
    rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular hregular, mul_one]
    exact (ZMod.natCast_eq_zero_iff 4 2).2 (by norm_num)
  have hdim : 1 < Module.finrank (ZMod 2) L.ker := by
    have hr : (Module.finrank (ZMod 2) L.ker : ℝ) ≥
        (19999999 / 10000000 : ℝ) := h_guard.2.2
    have hs : (1 : ℝ) < (Module.finrank (ZMod 2) L.ker : ℝ) := by
      linarith only [hr]
    exact_mod_cast hs
  have hex : ∃ x : V → ZMod 2, x ≠ 0 ∧ L x = 0 ∧ x ≠ 1 := by
    by_contra h
    have hle : L.ker ≤
        Submodule.span (ZMod 2) ({1} : Set (V → ZMod 2)) := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Submodule.mem_span_singleton_self _
      exact False.elim (h ⟨x, hx0, LinearMap.mem_ker.mp hx, hx1⟩)
    have hspan : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) ({1} : Set (V → ZMod 2))) ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod 2)
        ({(1 : V → ZMod 2)} : Set (V → ZMod 2)))
    exact (not_le_of_gt hdim) ((Submodule.finrank_mono hle).trans hspan)
  obtain ⟨x, hx0, hxker, hx1⟩ := hex
  have hy0 : (1 : V → ZMod 2) - x ≠ 0 := by
    intro h
    exact hx1 (sub_eq_zero.mp h).symm
  have hyker : L ((1 : V → ZMod 2) - x) = 0 := by
    rw [map_sub, hone, hxker, sub_self]
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
    intro a
    have hlt := ZMod.val_lt a
    have hv : a.val = 0 ∨ a.val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl ((ZMod.val_eq_zero a).mp hv)
    · exact Or.inr ((ZMod.val_eq_one (n := 2) (by norm_num) a).mp hv)
  have hw : hammingNorm x + hammingNorm ((1 : V → ZMod 2) - x) =
      Fintype.card V := by
    have hf : (Finset.univ : Finset V).filter
        (fun v => ((1 : V → ZMod 2) - x) v ≠ 0) =
        (Finset.univ : Finset V).filter (fun v => ¬(x v ≠ 0)) := by
      apply Finset.filter_congr
      intro v hv
      change ((1 : ZMod 2) - x v ≠ 0) ↔ ¬(x v ≠ 0)
      rcases hbinary (x v) with h | h <;> simp [h]
    unfold hammingNorm
    rw [hf]
    simpa using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (fun v => x v ≠ 0))
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun z => z ≠ 0 ∧ L z = 0)).image hammingNorm
  have hne : weights.Nonempty := by simp [weights]
  change (2 : ℝ) * (weights.min' hne : ℝ) ≤ (Fintype.card V : ℝ)
  have hbound : ∀ z : V → ZMod 2, z ≠ 0 → L z = 0 →
      weights.min' hne ≤ hammingNorm z := by
    intro z hz0 hzker
    apply Finset.min'_le
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz0, hzker⟩, rfl⟩
  have hbx := hbound x hx0 hxker
  have hby := hbound ((1 : V → ZMod 2) - x) hy0 hyker
  have hnat : 2 * weights.min' hne ≤ Fintype.card V := by omega
  exact_mod_cast hnat

theorem nonzero_parity_code_distance_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≤ (Fintype.card V : ℝ) := by
  classical
  let K := LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hk : 0 < Module.finrank (ZMod 2) K := by
    have hr : (0 : ℝ) < (Module.finrank (ZMod 2) K : ℝ) := by
      dsimp [K]
      linarith [h_guard]
    exact_mod_cast hr
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2) (M := K)).mp hk
  have hxne : (x : V → ZMod 2) ≠ 0 := by
    intro heq
    apply hx
    exact Subtype.ext heq
  have hxcode : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 := x.property
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun y => y ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin y = 0)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  have hweights : weights.Nonempty := by simp [weights]
  have hxmem : (x : V → ZMod 2) ∈ words := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxcode⟩
  have hle : weights.min' hweights ≤ Fintype.card V :=
    le_trans (Finset.min'_le _ _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(x : V → ZMod 2), hxmem, rfl⟩)))) hammingNorm_le_card_fintype
  change (weights.min' hweights : ℝ) ≤ (Fintype.card V : ℝ)
  exact_mod_cast hle
theorem model_f77e93b699329a958881 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)))) + ((2 : ℝ) * ((Int.ceil ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) / ((2 : ℝ) * ((G.maxDegree : ℝ) - (1 : ℝ))))) : ℝ))) ≤ ((Fintype.card V : ℝ) + (4 : ℝ)) := by
  sorry
