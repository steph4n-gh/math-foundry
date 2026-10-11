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

theorem model_9507736b3513f2c06029 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) = ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) + (1 : ℝ)) := by
  classical
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let words : Finset (V → ZMod 2) := Finset.univ.filter (fun x => x ≠ 0 ∧ A.mulVecLin x = 0)
  let stops : Finset (Finset V) := Finset.univ.filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))
  let cw : Finset ℕ := {Fintype.card V + 1} ∪ words.image hammingNorm
  let sw : Finset ℕ := {Fintype.card V + 1} ∪ stops.image Finset.card
  have hcw : cw.Nonempty := by simp [cw]
  have hsw : sw.Nonempty := by simp [sw]
  change (cw.min' hcw : ℝ) = ((sw.min' hsw - 1 : ℕ) : ℝ) + 1
  have hpos : 1 ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hS).2.1.card_pos
  have hcode : ∀ S ∈ stops, ∃ x : V → ZMod 2, x ≠ 0 ∧ A.mulVecLin x = 0 ∧ hammingNorm x ≤ S.card := by
    intro S hS
    have hs := (Finset.mem_filter.mp hS).2
    obtain ⟨t, ht⟩ := hs.1
    let c : G.Coloring (Fin 2) := h_guard.1.coloringTwo
    have sameColor : ∀ {v w u : V}, G.Adj v w → G.Adj v u → c w = c u := by
      intro v w u hvw hvu
      apply Fin.ext
      have hvw' : (c v).val ≠ (c w).val := fun h => c.valid hvw (Fin.ext h)
      have hvu' : (c v).val ≠ (c u).val := fun h => c.valid hvu (Fin.ext h)
      have hvlt := (c v).isLt
      have hwlt := (c w).isLt
      have hult := (c u).isLt
      omega
    let T : Finset V := S.filter (fun w => c w = c t)
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨ht, rfl⟩
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hTstop : ¬ (∃ v w, w ∈ T ∧ G.Adj v w ∧ ∀ u ∈ T, G.Adj v u → u = w) := by
      rintro ⟨v, w, hw, hvw, huniq⟩
      apply hs.2
      refine ⟨v, w, (Finset.mem_filter.mp hw).1, hvw, ?_⟩
      intro u hu hvu
      exact huniq u (Finset.mem_filter.mpr ⟨hu, (sameColor hvu hvw).trans (Finset.mem_filter.mp hw).2⟩) hvu
    let N : Finset V := Finset.univ.filter (fun v => ∃ w ∈ T, G.Adj v w)
    have hTN : Disjoint T N := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvN
      obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hvN).2
      exact c.valid hvw ((Finset.mem_filter.mp hvT).2.trans (Finset.mem_filter.mp hw).2.symm)
    let U : Finset V := T ∪ N
    let H : SimpleGraph ↥U := (G.between (T : Set V) (N : Set V)).induce (U : Set V)
    have hHacyc : H.IsAcyclic :=
      (SimpleGraph.IsAcyclic.anti
        (SimpleGraph.between_le (G := G) (s := (T : Set V)) (t := (N : Set V)))
        h_guard.1).induce (U : Set V)
    letI : Nonempty ↥U := ⟨⟨t, Finset.mem_union.mpr (Or.inl htT)⟩⟩
    obtain ⟨F, hHF, hFtop, hFT⟩ :=
      (SimpleGraph.connected_top (V := ↥U)).exists_isTree_le_of_le_of_isAcyclic
        (show H ≤ (⊤ : SimpleGraph ↥U) from le_top) hHacyc
    have hEF : H.edgeFinset.card ≤ F.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hHF)
    have hFTcard : F.edgeFinset.card + 1 = U.card := by
      simpa only [Fintype.card_coe] using hFT.card_edgeFinset
    have hHcard : H.edgeFinset.card < U.card := by omega
    let Tp : Finset ↥U := Finset.univ.filter (fun v => (v : V) ∈ T)
    let Np : Finset ↥U := Finset.univ.filter (fun v => (v : V) ∈ N)
    have hNpcard : Np.card = N.card := by
      refine Finset.card_bij (fun v _ => (v : V)) ?_ ?_ ?_
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
      · intro v hv w hw heq
        exact Subtype.ext heq
      · intro v hv
        refine ⟨⟨v, Finset.mem_union.mpr (Or.inr hv)⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    have hparts : H.IsBipartiteWith (Tp : Set ↥U) (Np : Set ↥U) := by
      refine ⟨?_, ?_⟩
      · apply Set.disjoint_left.mpr
        intro v hv hw
        exact Finset.disjoint_left.mp hTN (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2
      · intro v w hvw
        change G.Adj (v : V) (w : V) ∧ (((v : V) ∈ T ∧ (w : V) ∈ N) ∨ ((v : V) ∈ N ∧ (w : V) ∈ T)) at hvw
        rcases hvw.2 with ⟨hvT, hwN⟩ | ⟨hvN, hwT⟩
        · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvT⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwN⟩⟩
        · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwT⟩⟩
    have hdegree : ∀ v ∈ Np, 2 ≤ H.degree v := by
      intro v hv
      have hvN : (v : V) ∈ N := (Finset.mem_filter.mp hv).2
      obtain ⟨w, hw, hvw⟩ := (Finset.mem_filter.mp hvN).2
      have hsecond : ∃ u ∈ T, G.Adj (v : V) u ∧ u ≠ w := by
        by_contra hno
        apply hTstop
        refine ⟨(v : V), w, hw, hvw, ?_⟩
        intro u hu hvu
        by_contra hne
        exact hno ⟨u, hu, hvu, hne⟩
      obtain ⟨u, hu, hvu, hune⟩ := hsecond
      let ww : ↥U := ⟨w, Finset.mem_union.mpr (Or.inl hw)⟩
      let uu : ↥U := ⟨u, Finset.mem_union.mpr (Or.inl hu)⟩
      have hneq : ww ≠ uu := by
        intro heq
        exact hune (congrArg (fun z : ↥U => (z : V)) heq).symm
      have hww : ww ∈ H.neighborFinset v := by
        apply (H.mem_neighborFinset v ww).mpr
        exact ⟨hvw, Or.inr ⟨hvN, hw⟩⟩
      have huu : uu ∈ H.neighborFinset v := by
        apply (H.mem_neighborFinset v uu).mpr
        exact ⟨hvu, Or.inr ⟨hvN, hu⟩⟩
      have hpair : ({ww, uu} : Finset ↥U) ⊆ H.neighborFinset v := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hww
        · exact huu
      have hcard := Finset.card_le_card hpair
      simpa only [Finset.card_pair hneq, SimpleGraph.card_neighborFinset_eq_degree] using hcard
    have hsumEdges : 2 * Np.card ≤ H.edgeFinset.card := by
      rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hparts]
      calc
        2 * Np.card = ∑ v ∈ Np, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ Np, H.degree v := Finset.sum_le_sum hdegree
    have hUcard : U.card = T.card + N.card := Finset.card_union_of_disjoint hTN
    have hNT : N.card < T.card := by omega
    let M : Matrix ↥N ↥T (ZMod 2) := fun v w => A (v : V) (w : V)
    have hnoninj : ¬ Function.Injective M.mulVecLin := by
      intro hinj
      have hdim : T.card ≤ N.card := by
        simpa only [Module.finrank_pi, Fintype.card_coe] using
          (LinearMap.finrank_le_finrank_of_injective (f := M.mulVecLin) hinj)
      omega
    have hyexists : ∃ y : ↥T → ZMod 2, y ≠ 0 ∧ M.mulVecLin y = 0 := by
      by_contra hy
      apply hnoninj
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro y hyzero
      by_contra hyne
      exact hy ⟨y, hyne, hyzero⟩
    obtain ⟨y, hyne, hyker⟩ := hyexists
    let x : V → ZMod 2 := fun v => if hv : v ∈ T then y ⟨v, hv⟩ else 0
    have hxne : x ≠ 0 := by
      intro hx
      apply hyne
      funext w
      have hz := congrFun hx (w : V)
      simpa [x, w.property] using hz
    have hsumVector (v : V) : (A.mulVecLin x) v = ∑ w : ↥T, A v w * y w := by
      rw [Matrix.mulVecLin_apply]
      change (∑ w : V, A v w * x w) = ∑ w : ↥T, A v w * y w
      calc
        (∑ w : V, A v w * x w) = ∑ w ∈ T, A v w * x w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ T)
          intro w hw hwn
          simp [x, hwn]
        _ = ∑ w : ↥T, A v w * x w := (Finset.sum_coe_sort T (fun w => A v w * x w)).symm
        _ = ∑ w : ↥T, A v w * y w := by
          apply Finset.sum_congr rfl
          intro w hw
          simp [x, w.property]
    have hxker : A.mulVecLin x = 0 := by
      funext v
      rw [hsumVector v]
      by_cases hv : v ∈ N
      · have hz := congrFun hyker ⟨v, hv⟩
        change (∑ w : ↥T, A v w * y w) = 0 at hz
        exact hz
      · apply Finset.sum_eq_zero
        intro w hw
        have hnAdj : ¬ G.Adj v (w : V) := by
          intro hvw
          exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨(w : V), w.property, hvw⟩⟩)
        simp [A, hnAdj]
    have hxwt : hammingNorm x ≤ T.card := by
      change (Finset.univ.filter (fun v => x v ≠ 0)).card ≤ T.card
      apply Finset.card_le_card
      intro v hv
      have hnv : x v ≠ 0 := (Finset.mem_filter.mp hv).2
      by_contra hvT
      exact hnv (by simp [x, hvT])
    exact ⟨x, hxne, hxker, hxwt.trans (Finset.card_le_card hTS)⟩
  have hle : cw.min' hcw ≤ sw.min' hsw := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      subst a
      exact Finset.min'_le _ _ (by simp [cw])
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨x, hxne, hxker, hxwt⟩ := hcode S hS
      have hmem : hammingNorm x ∈ cw :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩, rfl⟩))
      exact (Finset.min'_le cw _ hmem).trans hxwt
  have hupper : (cw.min' hcw : ℝ) ≤ ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 := by
    have hn : cw.min' hcw ≤ sw.min' hsw - 1 + 1 := by omega
    exact_mod_cast hn
  have hlower : ((sw.min' hsw - 1 : ℕ) : ℝ) + 1 ≤ (cw.min' hcw : ℝ) :=
    parity_code_unique_neighbor_distance G
  exact le_antisymm hupper hlower
theorem model_d5cff71652de3b782468 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ ((Gᶜ.cliqueNum : ℝ) + (1 : ℝ)) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (Module.finrank (ZMod 2) K : ℝ) + (d : ℝ) ≤
    (Gᶜ.cliqueNum : ℝ) + 1
  have hkreal : (9999999 / 10000000 : ℝ) ≤
      (Module.finrank (ZMod 2) K : ℝ) := h_guard.2
  have hkpos : 0 < Module.finrank (ZMod 2) K := by
    by_contra h
    have hz : Module.finrank (ZMod 2) K = 0 := by omega
    rw [hz] at hkreal
    norm_num at hkreal
  have hsingle : ∀ (x : V → ZMod 2), A x = 0 →
      ∀ (u v : V), G.Adj u v → x u ≠ 0 → x v ≠ 0 → False := by
    intro x hAx u v hadj hxu hxv
    letI : Nonempty V := ⟨u⟩
    let H : SimpleGraph V :=
      { Adj := fun a b => G.Adj a b ∧ x a ≠ 0 ∧ x b ≠ 0
        symm := ⟨by
          intro a b h
          exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
        loopless := ⟨by
          intro a h
          exact G.loopless.irrefl a h.1⟩ }
    have hHG : H ≤ G := by
      intro a b h
      exact h.1
    have hHacyc : H.IsAcyclic :=
      SimpleGraph.IsAcyclic.anti hHG h_guard.1
    have huv : H.Adj u v := ⟨hadj, hxu, hxv⟩
    obtain ⟨a, b, p, hp, hmax⟩ :=
      SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
    have hlen : 1 ≤ p.length := by
      simpa only [SimpleGraph.Adj.length_toWalk] using
        hmax u v huv.toWalk huv.isPath_toWalk
    have hpnon : ¬ p.Nil :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
    have hleaf : ∀ w : V, H.Adj a w → w = p.snd := by
      intro w haw
      apply hHacyc.eq_snd_of_adj_start hp haw
      by_contra hw'
      have hpath : (p.cons haw.symm).IsPath := hp.cons hw'
      have hbound := hmax w b (p.cons haw.symm) hpath
      simp only [SimpleGraph.Walk.length_cons] at hbound
      omega
    have hap : H.Adj a p.snd := p.adj_snd hpnon
    have hsum : (∑ w ∈ G.neighborFinset a, x w) = x p.snd := by
      apply Finset.sum_eq_single p.snd
      · intro w hw' hne
        by_contra hxw
        have haw : H.Adj a w :=
          ⟨(G.mem_neighborFinset a w).mp hw', hap.2.1, hxw⟩
        exact hne (hleaf w haw)
      · intro hnot
        exact (hnot ((G.mem_neighborFinset a p.snd).mpr hap.1)).elim
    have hzero : (∑ w ∈ G.neighborFinset a, x w) = 0 := by
      simpa [A, Matrix.mulVecLin_apply] using congrFun hAx a
    exact hap.2.2 (hsum.symm.trans hzero)
  let T : Finset V := Finset.univ.filter
    (fun v => ∃ x : K, (x : V → ZMod 2) v ≠ 0)
  have hTclique : Gᶜ.IsClique (T : Set V) := by
    intro u hu v hv huv
    obtain ⟨x, hxu⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨y, hyv⟩ := (Finset.mem_filter.mp hv).2
    apply (SimpleGraph.compl_adj G u v).mpr
    refine ⟨huv, ?_⟩
    intro hadj
    have hxA : A (x : V → ZMod 2) = 0 :=
      LinearMap.mem_ker.mp x.property
    have hyA : A (y : V → ZMod 2) = 0 :=
      LinearMap.mem_ker.mp y.property
    have hxv : (x : V → ZMod 2) v = 0 := by
      by_contra hne
      exact hsingle (x : V → ZMod 2) hxA u v hadj hxu hne
    have hyu : (y : V → ZMod 2) u = 0 := by
      by_contra hne
      exact hsingle (y : V → ZMod 2) hyA u v hadj hne hyv
    have hsumA : A ((x : V → ZMod 2) + (y : V → ZMod 2)) = 0 := by
      rw [map_add, hxA, hyA, add_zero]
    have hsumu : ((x : V → ZMod 2) + (y : V → ZMod 2)) u ≠ 0 := by
      simpa [Pi.add_apply, hyu] using hxu
    have hsumv : ((x : V → ZMod 2) + (y : V → ZMod 2)) v ≠ 0 := by
      simpa [Pi.add_apply, hxv] using hyv
    exact hsingle _ hsumA u v hadj hsumu hsumv
  have hdpos : 1 ≤ d := by
    apply Finset.le_min'
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have heq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      exact hammingNorm_pos_iff.mpr (Finset.mem_filter.mp hx).2.1
  have hdmin : ∀ x : K, (x : V → ZMod 2) ≠ 0 →
      d ≤ hammingNorm (x : V → ZMod 2) := by
    intro x hx
    have hmem : hammingNorm (x : V → ZMod 2) ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨(x : V → ZMod 2), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hx, LinearMap.mem_ker.mp x.property⟩
    exact Finset.min'_le weights _ hmem
  have hTweight : ∀ x : K, hammingNorm (x : V → ZMod 2) ≤ T.card := by
    intro x
    change (Finset.univ.filter (fun v => (x : V → ZMod 2) v ≠ 0)).card ≤ T.card
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ v, ⟨x, (Finset.mem_filter.mp hv).2⟩⟩
  have hdle : d ≤ T.card := by
    obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero
      (R := ZMod 2) (M := K)).mp hkpos
    have hxne : (x : V → ZMod 2) ≠ 0 := by
      intro hz
      exact hx (Subtype.ext hz)
    exact (hdmin x hxne).trans (hTweight x)
  have hsub : d - 1 ≤ T.card := by omega
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq hsub
  let t : Finset V := T \ s
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
    have hmin := hdmin x hxne
    have hsupp :
        (Finset.univ.filter (fun v => (x : V → ZMod 2) v ≠ 0)) ⊆ s := by
      intro v hv
      by_contra hvs
      have hvT : v ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_univ v, ⟨x, (Finset.mem_filter.mp hv).2⟩⟩
      have hvt : v ∈ t := Finset.mem_sdiff.mpr ⟨hvT, hvs⟩
      have hzero : (x : V → ZMod 2) v = 0 :=
        congrFun hx ⟨v, hvt⟩
      exact (Finset.mem_filter.mp hv).2 hzero
    have hweight : hammingNorm (x : V → ZMod 2) ≤ s.card :=
      Finset.card_le_card hsupp
    omega
  have hk : Module.finrank (ZMod 2) K ≤ t.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      (LinearMap.finrank_le_finrank_of_injective (f := f) hf)
  have hcards : t.card + s.card = T.card := by
    simpa only [t] using Finset.card_sdiff_add_card_eq_card hs
  have hclique : T.card ≤ Gᶜ.cliqueNum := hTclique.card_le_cliqueNum
  have hfinal : Module.finrank (ZMod 2) K + d ≤ Gᶜ.cliqueNum + 1 := by
    omega
  exact_mod_cast hfinal
