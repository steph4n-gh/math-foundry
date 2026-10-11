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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

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

theorem model_19ffa035acae97b080f4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  have hbit : ∀ a b : ZMod 2,
      (if a ≠ 0 then (1 : ℕ) else 0) +
        (if b ≠ 0 then 1 else 0) +
        (if a + b ≠ 0 then 1 else 0) ≤ 2 := by
    decide
  have hbit_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    decide
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  let d : ℕ := weights.min' (by simp [weights])
  change (k : ℝ) + (d : ℝ) ≤ (n : ℝ)
  have hkreal : (19999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2
  have hk : 2 ≤ k := by
    by_contra h
    have hle : (k : ℝ) ≤ 1 := by
      exact_mod_cast (show k ≤ 1 by omega)
    linarith
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have heq : G.minDegree = 0 := by omega
    have hg := h_guard.1
    rw [heq] at hg
    norm_num at hg
  have hkn : k ≤ n := by
    calc
      k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
      _ = n := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hn : 0 < Fintype.card V := by
    change 0 < n
    omega
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp
    (lt_of_lt_of_le hdeg (G.minDegree_le_degree u))
  let a : LinearMap.range A :=
    ⟨A (Pi.single u 1), ⟨Pi.single u 1, rfl⟩⟩
  let b : LinearMap.range A :=
    ⟨A (Pi.single v 1), ⟨Pi.single v 1, rfl⟩⟩
  have hb : b ≠ 0 := by
    intro heq
    have hh := congrArg
      (fun w : LinearMap.range A => (w : V → ZMod 2) u) heq
    simp [b, A, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, huv] at hh
  have hba : ∀ c : ZMod 2, c • b ≠ a := by
    intro c heq
    have hh := congrArg
      (fun w : LinearMap.range A => (w : V → ZMod 2) v) heq
    simp [a, b, A, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      Matrix.col_apply, G.adj_symm huv] at hh
  have hab : LinearIndependent (ZMod 2) ![a, b] :=
    linearIndependent_fin2.mpr ⟨hb, hba⟩
  have hr : 2 ≤ Module.finrank (ZMod 2) (LinearMap.range A) := by
    simpa using hab.fintype_card_le_finrank
  have hrk : Module.finrank (ZMod 2) (LinearMap.range A) + k = n := by
    simpa [k, C, n, Module.finrank_fintype_fun_eq_card]
      using LinearMap.finrank_range_add_finrank_ker A
  have hkn2 : k + 2 ≤ n := by omega
  obtain ⟨s, hsu, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset V)) (n := k - 2)
    (by simpa [n] using (Nat.sub_le k 2).trans hkn)
  let p : C →ₗ[ZMod 2] (s → ZMod 2) :=
    { toFun := fun w i => (w : V → ZMod 2) i.1
      map_add' := by intro w z; rfl
      map_smul' := by intro c w; rfl }
  have hpr : Module.finrank (ZMod 2) (LinearMap.range p) ≤ k - 2 := by
    calc
      _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
      _ = s.card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      _ = k - 2 := hs
  have hpdim : 2 ≤ Module.finrank (ZMod 2) (LinearMap.ker p) := by
    have heq := LinearMap.finrank_range_add_finrank_ker p
    change Module.finrank (ZMod 2) (LinearMap.range p) +
      Module.finrank (ZMod 2) (LinearMap.ker p) = k at heq
    omega
  obtain ⟨z, hz⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod 2) (M := LinearMap.ker p) hpdim
  let x : V → ZMod 2 := (z 0).val.val
  let y : V → ZMod 2 := (z 1).val.val
  have hxA : A x = 0 := LinearMap.mem_ker.mp (z 0).val.property
  have hyA : A y = 0 := LinearMap.mem_ker.mp (z 1).val.property
  have hx : x ≠ 0 := by
    intro heq
    apply hz.ne_zero 0
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hy : y ≠ 0 := by
    intro heq
    apply hz.ne_zero 1
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hxy : x + y ≠ 0 := by
    intro heq
    have hzeq : z 0 = z 1 := by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact hbit_eq (x i) (y i) (congrFun heq i)
    exact (by decide : (0 : Fin 2) ≠ 1) (hz.injective hzeq)
  have hxyA : A (x + y) = 0 := by
    rw [map_add, hxA, hyA, add_zero]
  have hxs : ∀ i ∈ s, x i = 0 := by
    intro i hi
    have heq : p (z 0).val = 0 := LinearMap.mem_ker.mp (z 0).property
    exact congrFun heq ⟨i, hi⟩
  have hys : ∀ i ∈ s, y i = 0 := by
    intro i hi
    have heq : p (z 1).val = 0 := LinearMap.mem_ker.mp (z 1).property
    exact congrFun heq ⟨i, hi⟩
  have hd : ∀ t : V → ZMod 2, t ≠ 0 → A t = 0 → d ≤ hammingNorm t := by
    intro t ht hAt
    have hm : hammingNorm t ∈ weights := by
      dsimp only [weights]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht, hAt⟩, rfl⟩))
    exact Finset.min'_le weights (hammingNorm t) hm
  have hdx := hd x hx hxA
  have hdy := hd y hy hyA
  have hdxy := hd (x + y) hxy hxyA
  have hpoint : ∀ i : V,
      (if x i ≠ 0 then (1 : ℕ) else 0) +
        (if y i ≠ 0 then 1 else 0) +
        (if (x + y) i ≠ 0 then 1 else 0) ≤
          if i ∈ s then 0 else 2 := by
    intro i
    by_cases hi : i ∈ s
    · simp [hi, hxs i hi, hys i hi, Pi.add_apply]
    · simpa [hi, Pi.add_apply] using hbit (x i) (y i)
  have hcomp : (Finset.univ : Finset V).filter (fun i => i ∉ s) = sᶜ := by
    ext i
    simp
  have hsum : hammingNorm x + hammingNorm y + hammingNorm (x + y) ≤
      2 * (n - s.card) := by
    calc
      _ = ∑ i : V,
          ((if x i ≠ 0 then (1 : ℕ) else 0) +
            (if y i ≠ 0 then 1 else 0) +
            (if (x + y) i ≠ 0 then 1 else 0)) := by
        simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
      _ ≤ ∑ i : V, if i ∈ s then (0 : ℕ) else 2 :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = 2 * (n - s.card) := by
        rw [Finset.sum_ite]
        simp [hcomp, Finset.card_compl, n, Nat.mul_comm]
  have h3d : 3 * d ≤ 2 * (n - s.card) := by omega
  have hfinal : k + d ≤ n := by omega
  exact_mod_cast hfinal

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

theorem model_d5876bce3d63a657ae5c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
    letI : IsEmpty V := hV
    have hm : G.minDegree = 0 := by simp
    have hg := h_guard.2.1
    rw [hm] at hg
    norm_num at hg
  | inr hV =>
    letI : Nonempty V := hV
    rcases h_guard.1 with ⟨r, hr⟩
    have hclose : |(r : ℝ) - 2| ≤ (1 / 10000000 : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.1
    have hrlo : (1 : ℝ) < (r : ℝ) := by
      have ha := (abs_le.mp hclose).1
      linarith
    have hrhi : (r : ℝ) < (3 : ℝ) := by
      have ha := (abs_le.mp hclose).2
      linarith
    have hrlo_nat : 1 < r := by exact_mod_cast hrlo
    have hrhi_nat : r < 3 := by exact_mod_cast hrhi
    have hr2 : r = 2 := by omega
    have hdeg (v : V) : G.degree v = 2 := (hr.degree_eq v).trans hr2
    let K : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    letI : Fintype K := Fintype.ofFinite K
    let E : V → (K → ZMod 2) := fun v x => (x : V → ZMod 2) v
    let Q := {q : K → ZMod 2 // ∃ v : V, E v = q}
    letI : Fintype Q := Fintype.ofFinite Q
    let p : V → Q := fun v => ⟨E v, ⟨v, rfl⟩⟩
    let rep : Q → V := fun q => Classical.choose q.property
    have hrep (q : Q) : E (rep q) = q.val := by
      exact Classical.choose_spec q.property
    have hpairs : ∀ v : V, ∃ a b : V,
        a ≠ b ∧ G.neighborFinset v = {a, b} ∧ E a = E b := by
      intro v
      have hc : (G.neighborFinset v).card = 2 := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v
      rcases Finset.card_eq_two.mp hc with ⟨a, b, hab, hs⟩
      refine ⟨a, b, hab, hs, ?_⟩
      funext x
      change (x : V → ZMod 2) a = (x : V → ZMod 2) b
      have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
        x.property
      have hsum : (x : V → ZMod 2) a + (x : V → ZMod 2) b = 0 := by
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, Pi.zero_apply] using congrFun hx v
      simpa only [ZMod.neg_eq_self_mod_two] using
        (eq_neg_iff_add_eq_zero.mpr hsum)
    let f : K →ₗ[ZMod 2] (Q → ZMod 2) :=
      { toFun := fun x q => (x : V → ZMod 2) (rep q)
        map_add' := by
          intro x y
          funext q
          rfl
        map_smul' := by
          intro a x
          funext q
          rfl }
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      funext v
      calc
        (x : V → ZMod 2) v = (x : V → ZMod 2) (rep (p v)) :=
          (congrFun (hrep (p v)) x).symm
        _ = (y : V → ZMod 2) (rep (p v)) := congrFun hxy (p v)
        _ = (y : V → ZMod 2) v := congrFun (hrep (p v)) y
    have hkdim : Module.finrank (ZMod 2) K ≤ Fintype.card Q := by
      calc
        _ ≤ Module.finrank (ZMod 2) (Q → ZMod 2) :=
          LinearMap.finrank_le_finrank_of_injective hf
        _ = Fintype.card Q := Module.finrank_fintype_fun_eq_card (ZMod 2)
    let weights : Finset ℕ := {Fintype.card V + 1} ∪
      ((Finset.univ : Finset (V → ZMod 2)).filter
        (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
    have hw : weights.Nonempty := by simp [weights]
    let d : ℕ := weights.min' hw
    have hbound (q : Q) :
        d ≤ ((Finset.univ : Finset V).filter (fun v => p v = q)).card := by
      let c : V → ZMod 2 := fun v => if p v = q then 1 else 0
      have hp : p (rep q) = q := Subtype.ext (hrep q)
      have hc0 : c ≠ 0 := by
        intro hc
        have hh := congrFun hc (rep q)
        simpa [c, hp] using hh
      have hker : (G.adjMatrix (ZMod 2)).mulVecLin c = 0 := by
        apply funext
        intro v
        rcases hpairs v with ⟨a, b, hab, hs, he⟩
        have hpab : p a = p b := Subtype.ext he
        have hcab : c a = c b := by
          dsimp only [c]
          rw [hpab]
        have hz : c b + c b = 0 := by
          simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (c b)
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, hcab, Pi.zero_apply] using hz
      have hcw : hammingNorm c ∈ weights := by
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨c, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc0, hker⟩
      have hd : d ≤ hammingNorm c := Finset.min'_le weights (hammingNorm c) hcw
      simpa [hammingNorm, c] using hd
    have hsum :
        (∑ q : Q, ((Finset.univ : Finset V).filter (fun v => p v = q)).card) =
          Fintype.card V := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset V) (Finset.univ : Finset Q) p
    have hnat : Module.finrank (ZMod 2) K * d ≤ Fintype.card V := by
      calc
        _ ≤ Fintype.card Q * d := Nat.mul_le_mul_right d hkdim
        _ = ∑ q : Q, d := by simp [Nat.nsmul_eq_mul]
        _ ≤ ∑ q : Q, ((Finset.univ : Finset V).filter (fun v => p v = q)).card :=
          Finset.sum_le_sum (fun q _ => hbound q)
        _ = Fintype.card V := hsum
    change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast hnat

theorem model_b25136df53f5aa6f52de {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) = (Fintype.card V : ℝ) := by
  classical
    have hupper := model_d5876bce3d63a657ae5c G h_guard.2
    letI : Nonempty V := h_guard.1.nonempty
    rcases h_guard.2.1 with ⟨r, hr⟩
    have hclose : |(r : ℝ) - 2| ≤ (1 / 10000000 : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.2.1
    have hrlo : (1 : ℝ) < (r : ℝ) := by
      have ha := (abs_le.mp hclose).1
      linarith
    have hrhi : (r : ℝ) < (3 : ℝ) := by
      have ha := (abs_le.mp hclose).2
      linarith
    have hrlo_nat : 1 < r := by exact_mod_cast hrlo
    have hrhi_nat : r < 3 := by exact_mod_cast hrhi
    have hr2 : r = 2 := by omega
    have hdeg (w : V) : G.degree w = 2 := (hr.degree_eq w).trans hr2
    obtain ⟨u⟩ := h_guard.1.nonempty
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp
      (by rw [hdeg u]; norm_num)
    let K : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    letI : Fintype K := Fintype.ofFinite K
    let E : V → (K → ZMod 2) := fun w x => (x : V → ZMod 2) w
    let Q := {q : K → ZMod 2 // ∃ w : V, E w = q}
    letI : Fintype Q := Fintype.ofFinite Q
    let p : V → Q := fun w => ⟨E w, ⟨w, rfl⟩⟩
    let rep : Q → V := fun q => Classical.choose q.property
    have hrep (q : Q) : E (rep q) = q.val :=
      Classical.choose_spec q.property
    have hp (q : Q) : p (rep q) = q := Subtype.ext (hrep q)
    have hpairs : ∀ w : V, ∃ a b : V,
        a ≠ b ∧ G.neighborFinset w = {a, b} ∧ E a = E b := by
      intro w
      have hc : (G.neighborFinset w).card = 2 := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg w
      rcases Finset.card_eq_two.mp hc with ⟨a, b, hab, hs⟩
      refine ⟨a, b, hab, hs, ?_⟩
      funext x
      change (x : V → ZMod 2) a = (x : V → ZMod 2) b
      have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
        x.property
      have hsum : (x : V → ZMod 2) a + (x : V → ZMod 2) b = 0 := by
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, Pi.zero_apply] using congrFun hx w
      simpa only [ZMod.neg_eq_self_mod_two] using
        (eq_neg_iff_add_eq_zero.mpr hsum)
    have hcommon (w a b : V) (hwa : G.Adj w a) (hwb : G.Adj w b) :
        p a = p b := by
      rcases hpairs w with ⟨c, e, hce, hs, he⟩
      have ha : a ∈ G.neighborFinset w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hwa
      have hb : b ∈ G.neighborFinset w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hwb
      simp only [hs, Finset.mem_insert, Finset.mem_singleton] at ha hb
      have hpc : p c = p e := Subtype.ext he
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hpc
      · exact hpc.symm
      · rfl
    let P : V → Prop := fun w =>
      (p w = p u ∧ ∀ z : V, G.Adj w z → p z = p v) ∨
        (p w = p v ∧ ∀ z : V, G.Adj w z → p z = p u)
    have hstep (a b : V) (hab : G.Adj a b) : P a → P b := by
      intro ha
      rcases ha with ⟨ha, hna⟩ | ⟨ha, hna⟩
      · right
        refine ⟨hna b hab, ?_⟩
        intro c hbc
        exact (hcommon b c a hbc hab.symm).trans ha
      · left
        refine ⟨hna b hab, ?_⟩
        intro c hbc
        exact (hcommon b c a hbc hab.symm).trans ha
    have hwalk : ∀ {a b : V}, G.Walk a b → P a → P b := by
      intro a b walk
      induction walk with
      | nil => exact fun h => h
      | cons hab walk ih => exact fun h => ih (hstep _ _ hab h)
    have hlabels (w : V) : P w := by
      obtain ⟨walk⟩ := h_guard.1 u w
      exact hwalk walk (Or.inl ⟨rfl, fun z huz => hcommon u z v huz huv⟩)
    have hclasses (q : Q) : q = p u ∨ q = p v := by
      rcases hlabels (rep q) with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl ((hp q).symm.trans h)
      · exact Or.inr ((hp q).symm.trans h)
    let fiber : Q → Finset V := fun q =>
      (Finset.univ : Finset V).filter (fun w => p w = q)
    have hbalance : (fiber (p u)).card = (fiber (p v)).card := by
      by_cases heq : p u = p v
      · rw [heq]
      · have hbip : G.IsBipartiteWith
            (↑(fiber (p u)) : Set V) (↑(fiber (p v)) : Set V) := by
          refine ⟨?_, ?_⟩
          · apply Set.disjoint_left.mpr
            intro w hwu hwv
            have hwu' : p w = p u := (Finset.mem_filter.mp hwu).2
            have hwv' : p w = p v := (Finset.mem_filter.mp hwv).2
            exact heq (hwu'.symm.trans hwv')
          · intro a b hab
            rcases hlabels a with ⟨ha, hna⟩ | ⟨ha, hna⟩
            · left
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hna b hab⟩⟩
            · right
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hna b hab⟩⟩
        have hcount : (fiber (p u)).card * 2 = (fiber (p v)).card * 2 := by
          simpa only [hdeg, Finset.sum_const, Nat.nsmul_eq_mul] using
            (SimpleGraph.isBipartiteWith_sum_degrees_eq
              (s := fiber (p u)) (t := fiber (p v)) hbip)
        omega
    have huniform (q z : Q) : (fiber q).card = (fiber z).card := by
      rcases hclasses q with hq | hq <;> rcases hclasses z with hz | hz
      · rw [hq, hz]
      · simpa only [hq, hz] using hbalance
      · simpa only [hq, hz] using hbalance.symm
      · rw [hq, hz]
    have hker (y : Q → ZMod 2) :
        (G.adjMatrix (ZMod 2)).mulVecLin (fun w => y (p w)) = 0 := by
      apply funext
      intro w
      rcases hpairs w with ⟨a, b, hab, hs, he⟩
      have hpab : p a = p b := Subtype.ext he
      have hz : y (p b) + y (p b) = 0 := by
        simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (y (p b))
      simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
        hs, Finset.sum_pair hab, hpab, Pi.zero_apply] using hz
    let g : (Q → ZMod 2) →ₗ[ZMod 2] K :=
      { toFun := fun y => ⟨fun w => y (p w), hker y⟩
        map_add' := by
          intro y z
          apply Subtype.ext
          funext w
          rfl
        map_smul' := by
          intro a y
          apply Subtype.ext
          funext w
          rfl }
    have hg : Function.Injective g := by
      intro y z heq
      funext q
      have hh := congrArg (fun x : K => (x : V → ZMod 2) (rep q)) heq
      change y (p (rep q)) = z (p (rep q)) at hh
      simpa only [hp q] using hh
    have hkdim : Fintype.card Q ≤ Module.finrank (ZMod 2) K := by
      calc
        _ = Module.finrank (ZMod 2) (Q → ZMod 2) :=
          (Module.finrank_fintype_fun_eq_card (ZMod 2)).symm
        _ ≤ Module.finrank (ZMod 2) K :=
          LinearMap.finrank_le_finrank_of_injective hg
    have hsum : (∑ q : Q, (fiber q).card) = Fintype.card V := by
      simpa [fiber] using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset V) (Finset.univ : Finset Q) p
    have htotal : Fintype.card Q * (fiber (p u)).card = Fintype.card V := by
      calc
        _ = ∑ _q : Q, (fiber (p u)).card := by
          simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = ∑ q : Q, (fiber q).card := by
          apply Finset.sum_congr rfl
          intro q _
          exact (huniform q (p u)).symm
        _ = Fintype.card V := hsum
    have hcard : (fiber (p u)).card ≤ Fintype.card V := by
      calc
        _ ≤ (Finset.univ : Finset V).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card V := Finset.card_univ
    let weights : Finset ℕ := {Fintype.card V + 1} ∪
      ((Finset.univ : Finset (V → ZMod 2)).filter
        (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
    have hw : weights.Nonempty := by simp [weights]
    let d : ℕ := weights.min' hw
    have hmin : (fiber (p u)).card ≤ d := by
      refine Finset.le_min' weights hw ((fiber (p u)).card) ?_
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have heq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
        rw [heq]
        exact hcard.trans (Nat.le_succ _)
      · rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
        rcases (Finset.mem_filter.mp hx).2 with ⟨hx0, hxker⟩
        obtain ⟨w, hxn⟩ : ∃ w : V, x w ≠ 0 := by
          by_contra hn
          apply hx0
          funext w
          by_contra hxn
          exact hn ⟨w, hxn⟩
        let xc : K := ⟨x, hxker⟩
        have hsubset : fiber (p w) ⊆
            (Finset.univ : Finset V).filter (fun z => x z ≠ 0) := by
          intro z hz
          have hpzw : p z = p w := (Finset.mem_filter.mp hz).2
          have he : E z = E w := congrArg Subtype.val hpzw
          have hval : x z = x w := congrFun he xc
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hval]
          exact hxn
        calc
          _ = (fiber (p w)).card := huniform (p u) (p w)
          _ ≤ ((Finset.univ : Finset V).filter (fun z => x z ≠ 0)).card :=
            Finset.card_le_card hsubset
          _ = hammingNorm x := rfl
    have hnat : Fintype.card V ≤ Module.finrank (ZMod 2) K * d := by
      calc
        _ = Fintype.card Q * (fiber (p u)).card := htotal.symm
        _ ≤ Module.finrank (ZMod 2) K * d := Nat.mul_le_mul hkdim hmin
    have hlower : (Fintype.card V : ℝ) ≤
        (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) := by
      exact_mod_cast hnat
    change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) = (Fintype.card V : ℝ)
    exact le_antisymm hupper hlower
theorem model_ceb714b3b8492a9c6002 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) * ((1 : ℝ) - (((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))) * (Real.exp (((-(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ)))))))) ≤ (Fintype.card V : ℝ) := by
  sorry
