import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic










open scoped BigOperators

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
  sorry
