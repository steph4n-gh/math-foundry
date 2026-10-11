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

theorem model_256a48c23c065a850877 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((G.maxDegree : ℝ) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ (((G.maxDegree : ℝ) - (1 : ℝ)) * (Fintype.card V : ℝ)) := by
  classical
  let A : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := Nat.eq_zero_of_not_pos h
    have hh := h_guard.1
    rw [hz] at hh
    norm_num at hh
  obtain ⟨s, hs, hcard, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (Set.range A.col)
  let supp : (V → ZMod 2) → Finset V :=
    fun x => Finset.univ.filter (fun v => x v ≠ 0)
  have hcover : s.biUnion supp = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have hzero : ∀ x ∈ s, x v = 0 := by
      intro x hx
      by_contra hxv
      exact hv (Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hxv⟩⟩)
    have hall : ∀ x ∈ Submodule.span (ZMod 2) (s : Set (V → ZMod 2)),
        x v = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hzero y hy
      | zero => rfl
      | add x y hx hy ihx ihy => simp [ihx, ihy]
      | smul a x hx ih => simp [ih]
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp
      (lt_of_lt_of_le hdeg (G.minDegree_le_degree v))
    have hmem : A.col w ∈ Submodule.span (ZMod 2) (s : Set (V → ZMod 2)) := by
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self w)
    have hz := hall (A.col w) hmem
    change (if G.Adj v w then (1 : ZMod 2) else 0) = 0 at hz
    rw [if_pos hvw] at hz
    exact one_ne_zero hz
  have hsupp : ∀ x ∈ s, (supp x).card ≤ G.maxDegree := by
    intro x hx
    obtain ⟨w, rfl⟩ := hs hx
    calc
      (supp (A.col w)).card ≤ (G.neighborFinset w).card := by
        apply Finset.card_le_card
        intro v hv
        apply (G.mem_neighborFinset w v).mpr
        apply G.adj_symm
        by_contra h
        have hv' : A.col w v ≠ 0 := (Finset.mem_filter.mp hv).2
        apply hv'
        change (if G.Adj v w then (1 : ZMod 2) else 0) = 0
        exact if_neg h
      _ = G.degree w := G.card_neighborFinset_eq_degree w
      _ ≤ G.maxDegree := G.degree_le_maxDegree w
  have hbound : Fintype.card V ≤ s.card * G.maxDegree := by
    calc
      Fintype.card V = (s.biUnion supp).card := by
        rw [hcover, Finset.card_univ]
      _ ≤ s.card * G.maxDegree :=
        Finset.card_biUnion_le_card_mul s supp G.maxDegree hsupp
  have hnull : s.card + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
      Fintype.card V := by
    rw [hcard, ← Matrix.range_mulVecLin]
    simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hboundR : (Fintype.card V : ℝ) ≤ (s.card : ℝ) * (G.maxDegree : ℝ) := by
    exact_mod_cast hbound
  have hnullR : (s.card : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
      (Fintype.card V : ℝ) := by
    exact_mod_cast hnull
  change (G.maxDegree : ℝ) *
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) ≤
      ((G.maxDegree : ℝ) - 1) * (Fintype.card V : ℝ)
  nlinarith only [hboundR,
    congrArg (fun x : ℝ => (G.maxDegree : ℝ) * x) hnullR]

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
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let D : ℕ := G.maxDegree
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (k : ℝ) + 2 * (d : ℝ) +
    2 * (Int.ceil ((k : ℝ) / (2 * ((D : ℝ) - 1))) : ℝ) ≤ (n : ℝ) + 4
  have hkreal : (9999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.2
  have hk : 1 ≤ k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz, Nat.cast_zero] at hkreal
    norm_num at hkreal
  have hmin : 1 ≤ G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := by omega
    have hh := h_guard.2.1
    rw [hz, Nat.cast_zero] at hh
    norm_num at hh
  have hD : 2 ≤ D := by
    by_contra h
    have hn : D ≤ 1 := by omega
    have hr : (D : ℝ) ≤ 1 := by exact_mod_cast hn
    have hh : (19999999 / 10000000 : ℝ) ≤ (D : ℝ) := h_guard.2.2.1
    linarith
  have hd : ∀ x : V → ZMod 2, x ≠ 0 → A x = 0 → d ≤ hammingNorm x := by
    intro x hx hAx
    apply Finset.min'_le
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hAx⟩, rfl⟩))
  have hlocal : ∀ (I T : Type _) [Fintype I] [Fintype T] [DecidableEq T]
      (M : Matrix I T (ZMod 2)) (δ e : ℕ),
      2 ≤ δ →
      (∀ i, hammingNorm (M i) ≤ δ) →
      (∀ j, ∃ i, M i j ≠ 0) →
      0 < Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) →
      (∀ x : T → ZMod 2, x ≠ 0 → M.mulVecLin x = 0 → e ≤ hammingNorm x) →
      ∃ t : ℕ, e + t = M.rank + 2 ∧
        Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) ≤ (δ - 1) * t := by
    intro I T _ _ _ M δ e hδ hrows hcols hpos hdist
    let q : ℕ := M.rank
    let ell : ℕ := Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin)
    let m : ℕ := Fintype.card T
    have hdim : q + ell = m := by
      simpa only [q, ell, m, Matrix.rank, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have hell : 0 < ell := hpos
    have hq : Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range M.row)) = q :=
      M.rank_eq_finrank_span_row.symm
    obtain ⟨f, hf, hspan, hli⟩ :
        ∃ f : Fin q → (T → ZMod 2),
          (∀ i, f i ∈ Set.range M.row) ∧
          Submodule.span (ZMod 2) (Set.range f) =
            Submodule.span (ZMod 2) (Set.range M.row) ∧
          LinearIndependent (ZMod 2) f := by
      rw [← hq]
      exact Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range M.row)
    have hfi (i : Fin q) : hammingNorm (f i) ≤ δ := by
      obtain ⟨j, hj⟩ := hf i
      rw [← hj]
      exact hrows j
    have hker (x : T → ZMod 2)
        (hx : ∀ i, dotProduct (f i) x = 0) : M.mulVecLin x = 0 := by
      have hz : Submodule.span (ZMod 2) (Set.range f) ≤
          LinearMap.ker (dotProductEquiv (ZMod 2) T x) := by
        apply Submodule.span_le.mpr
        rintro w ⟨i, rfl⟩
        change dotProduct x (f i) = 0
        exact (dotProduct_comm x (f i)).trans (hx i)
      funext i
      change dotProduct (M i) x = 0
      have hm : M i ∈ Submodule.span (ZMod 2) (Set.range f) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hh := LinearMap.mem_ker.mp (hz hm)
      change dotProduct x (M i) = 0 at hh
      exact (dotProduct_comm (M i) x).trans hh
    have hshort (s : Finset T) (u : Finset (Fin q))
        (hvan : ∀ i ∈ u, ∀ j ∈ s, f i j = 0)
        (hs : s.card < e) : s.card + u.card ≤ q := by
      let Q := {i : Fin q // i ∉ u}
      let E : (s → ZMod 2) → (T → ZMod 2) :=
        fun x j => if h : j ∈ s then x ⟨j, h⟩ else 0
      let N : Matrix Q s (ZMod 2) := fun i j => f i.val j.val
      have hEL (x : s → ZMod 2) (j : s) : E x j.val = x j := by
        simp [E, j.property]
      have hsplit (g : T → ZMod 2) :
          (∑ j : T, g j) = (∑ j : s, g j.val) +
            ∑ j : {j : T // j ∉ s}, g j.val := by
        convert (Fintype.sum_subtype_add_sum_subtype
          (fun j : T => j ∈ s) g).symm using 1 <;>
          congr 1 <;> apply Finset.sum_congr (by ext i; simp) <;>
          intro i hi <;> rfl
      have hdot (x : s → ZMod 2) (i : Fin q) :
          dotProduct (f i) (E x) = ∑ j : s, f i j.val * x j := by
        change (∑ j : T, f i j * E x j) = _
        rw [hsplit]
        have hz : (∑ j : {j : T // j ∉ s}, f i j.val * E x j.val) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          simp [E, j.property]
        rw [hz, add_zero]
        apply Finset.sum_congr rfl
        intro j _
        rw [hEL]
      have hNzero (x : s → ZMod 2) (hx : N.mulVecLin x = 0) : x = 0 := by
        have hFx : ∀ i, dotProduct (f i) (E x) = 0 := by
          intro i
          rw [hdot]
          by_cases hi : i ∈ u
          · apply Finset.sum_eq_zero
            intro j _
            rw [hvan i hi j.val j.property, zero_mul]
          · have hh := congrFun hx (⟨i, hi⟩ : Q)
            change (∑ j : s, f i j.val * x j) = 0 at hh
            exact hh
        have hMx := hker (E x) hFx
        have hnorm : hammingNorm (E x) ≤ s.card := by
          unfold hammingNorm
          apply Finset.card_le_card
          intro j hj
          have hn : E x j ≠ 0 := (Finset.mem_filter.mp hj).2
          by_contra hjs
          exact hn (by simp [E, hjs])
        have he : E x = 0 := by
          by_contra hne
          have hh := hdist (E x) hne hMx
          omega
        funext j
        have hh := congrFun he j.val
        simpa only [hEL, Pi.zero_apply] using hh
      have hinj : Function.Injective N.mulVecLin := by
        intro x y hxy
        have hz : N.mulVecLin (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        exact sub_eq_zero.mp (hNzero (x - y) hz)
      have hh := LinearMap.finrank_le_finrank_of_injective hinj
      have hfin : s.card ≤ Fintype.card Q := by
        simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hh
      have hQ : u.card + Fintype.card Q = q := by
        simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using
          Fintype.card_congr (Equiv.sumCompl (fun i : Fin q => i ∈ u))
      omega
    have hsingle : e ≤ q + 1 := by
      by_contra h
      obtain ⟨s, hsub, hsc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset T)) (n := q + 1) (by
          simp only [Finset.card_univ]
          change q + 1 ≤ m
          omega)
      have hs : s.card < e := by omega
      have hh := hshort s ∅ (by simp) hs
      simp only [Finset.card_empty, add_zero] at hh
      omega
    let support (i : Fin q) : Finset T :=
      Finset.univ.filter (fun j => f i j ≠ 0)
    have hcount (u : Finset (Fin q)) :
        (u.biUnion support).card ≤ u.card * δ := by
      calc
        _ ≤ ∑ i ∈ u, (support i).card := Finset.card_biUnion_le
        _ ≤ ∑ i ∈ u, δ := Finset.sum_le_sum (fun i _ => hfi i)
        _ = u.card * δ := by simp [Nat.mul_comm]
    have hcover : (Finset.univ : Finset (Fin q)).biUnion support = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro j
      by_contra h
      have hz : Submodule.span (ZMod 2) (Set.range f) ≤
          LinearMap.ker (LinearMap.proj j : (T → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
        apply Submodule.span_le.mpr
        rintro w ⟨i, rfl⟩
        change f i j = 0
        by_contra hn
        apply h
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩⟩
      obtain ⟨i, hi⟩ := hcols j
      have hm : M i ∈ Submodule.span (ZMod 2) (Set.range f) := by
        rw [hspan]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hj : M i j = 0 := LinearMap.mem_ker.mp (hz hm)
      exact hi hj
    have hmd : m ≤ q * δ := by
      have hh := hcount (Finset.univ : Finset (Fin q))
      rw [hcover] at hh
      simpa only [Finset.card_univ, Fintype.card_fin] using hh
    let t : ℕ := q + 2 - e
    have ht : e + t = q + 2 := by omega
    refine ⟨t, ht, ?_⟩
    change ell ≤ (δ - 1) * t
    by_cases he2 : e ≤ 2
    · have hqt : q ≤ t := by omega
      have hpred : δ = (δ - 1) + 1 := by omega
      rw [hpred, Nat.mul_add, Nat.mul_one] at hmd
      calc
        ell ≤ q * (δ - 1) := by omega
        _ ≤ t * (δ - 1) := Nat.mul_le_mul_right (δ - 1) hqt
        _ = (δ - 1) * t := Nat.mul_comm _ _
    · have he : 2 ≤ e := by omega
      have htq : t ≤ q := by omega
      obtain ⟨u, hu, huc⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin q))) (n := t)
        (by simpa only [Finset.card_univ, Fintype.card_fin] using htq)
      let H : Finset T := u.biUnion support
      let S : Finset T := Hᶜ
      have hvan : ∀ i ∈ u, ∀ j ∈ S, f i j = 0 := by
        intro i hi j hj
        by_contra hn
        have hjs : j ∉ H := Finset.mem_compl.mp hj
        apply hjs
        exact Finset.mem_biUnion.mpr
          ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hn⟩⟩
      have hS : S.card ≤ e - 2 := by
        by_contra h
        obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq
          (s := S) (n := e - 1) (by omega)
        have hh := hshort s u
          (fun i hi j hj => hvan i hi j (hs hj)) (by omega)
        omega
      have hH : H.card ≤ t * δ := by
        simpa only [huc] using hcount u
      have hcards : H.card + S.card = m := Finset.card_add_card_compl H
      have hm : m ≤ t * δ + (e - 2) := by omega
      have hqt : q = t + (e - 2) := by omega
      have hpred : δ = (δ - 1) + 1 := by omega
      rw [hpred, Nat.mul_add, Nat.mul_one] at hm
      rw [Nat.mul_comm (δ - 1) t]
      omega
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
  let r : ℕ := B.rank
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
  have hsplit (x : V → ZMod 2) :
      (∑ v : V, x v) = (∑ v : L, x v.val) + (∑ v : R, x v.val) :=
    (Fintype.sum_subtype_add_sum_subtype (fun v : V => c v = 0) x).symm
  have haL (x : V → ZMod 2) (i : L) :
      A x i.val = BT.mulVecLin (fun j : R => x j.val) i := by
    change (∑ v : V, (G.adjMatrix (ZMod 2)) i.val v * x v) =
      ∑ j : R, (G.adjMatrix (ZMod 2)) j.val i.val * x j.val
    have hz : (∑ j : L, (G.adjMatrix (ZMod 2)) i.val j.val * x j.val) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [hz0 i j, zero_mul]
    rw [hsplit, hz, zero_add]
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym i.val j.val]
  have haR (x : V → ZMod 2) (i : R) :
      A x i.val = B.mulVecLin (fun j : L => x j.val) i := by
    change (∑ v : V, (G.adjMatrix (ZMod 2)) i.val v * x v) =
      ∑ j : L, (G.adjMatrix (ZMod 2)) i.val j.val * x j.val
    have hz : (∑ j : R, (G.adjMatrix (ZMod 2)) i.val j.val * x j.val) = 0 := by
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
      LinearMap.finrank_le_finrank_of_injective hf
  have hr0 : r + k0 = Fintype.card L := by
    simpa only [r, Matrix.rank, k0, C0, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  have hr1 : r + k1 = Fintype.card R := by
    have hh : BT.rank + k1 = Fintype.card R := by
      simpa only [Matrix.rank, k1, C1, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker BT.mulVecLin
    simpa only [BT, Matrix.rank_transpose, r] using hh
  have hcard : Fintype.card L + Fintype.card R = n := by
    simpa only [Fintype.card_sum] using
      Fintype.card_congr (Equiv.sumCompl (fun v : V => c v = 0))
  have hknr : k + 2 * r ≤ n := by omega
  have hlarge : (0 < k0 ∧ k ≤ 2 * k0) ∨ (0 < k1 ∧ k ≤ 2 * k1) := by omega
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
  have hrow_bound : ∀ (T : Type _) [Fintype T] [DecidableEq T]
      (ι : T → V), Function.Injective ι → ∀ v : V,
      hammingNorm (fun i : T => (G.adjMatrix (ZMod 2)) v (ι i)) ≤ D := by
    intro T _ _ ι hinj v
    calc
      _ ≤ (G.neighborFinset v).card := by
        unfold hammingNorm
        refine Finset.card_le_card_of_injOn ι ?_ ?_
        · intro i hi
          apply (G.mem_neighborFinset v (ι i)).mpr
          by_contra hn
          have hne : (G.adjMatrix (ZMod 2)) v (ι i) ≠ 0 :=
            (Finset.mem_filter.mp hi).2
          exact hne (by simp [SimpleGraph.adjMatrix_apply, hn])
        · intro i hi j hj hij
          exact hinj hij
      _ = G.degree v := rfl
      _ ≤ D := G.degree_le_maxDegree v
  have hrows0 (i : R) : hammingNorm (B i) ≤ D :=
    hrow_bound L Subtype.val Subtype.val_injective i.val
  have hrows1 (i : L) : hammingNorm (BT i) ≤ D := by
    have heq : BT i = (fun j : R => (G.adjMatrix (ZMod 2)) i.val j.val) := by
      funext j
      exact hsym j.val i.val
    rw [heq]
    exact hrow_bound R Subtype.val Subtype.val_injective i.val
  have hcols0 (j : L) : ∃ i : R, B i j ≠ 0 := by
    have hdeg : 0 < G.degree j.val :=
      lt_of_lt_of_le (by omega : 0 < G.minDegree) (G.minDegree_le_degree j.val)
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj j.val).mp hdeg
    have hcv : c v ≠ 0 := by
      intro h
      exact c.valid hv (j.property.trans h.symm)
    refine ⟨⟨v, hcv⟩, ?_⟩
    change (G.adjMatrix (ZMod 2)) v j.val ≠ 0
    simp [SimpleGraph.adjMatrix_apply, hv.symm]
  have hcols1 (j : R) : ∃ i : L, BT i j ≠ 0 := by
    have hdeg : 0 < G.degree j.val :=
      lt_of_lt_of_le (by omega : 0 < G.minDegree) (G.minDegree_le_degree j.val)
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj j.val).mp hdeg
    have hcv : c v = 0 := by
      by_contra h
      exact c.valid hv (hcol (c j.val) (c v) j.property h)
    refine ⟨⟨v, hcv⟩, ?_⟩
    change (G.adjMatrix (ZMod 2)) j.val v ≠ 0
    simp [SimpleGraph.adjMatrix_apply, hv]
  have hbound : ∃ t : ℕ, d + t = r + 2 ∧ k ≤ 2 * ((D - 1) * t) := by
    rcases hlarge with ⟨hpos, hside⟩ | ⟨hpos, hside⟩
    · obtain ⟨t, ht, hbt⟩ := hlocal R L B D d hD hrows0 hcols0 hpos
        (fun x hx hMx => hd0 ⟨x, LinearMap.mem_ker.mpr hMx⟩ (by
          intro heq
          exact hx (congrArg (fun z : C0 => (z : L → ZMod 2)) heq)))
      refine ⟨t, ht, ?_⟩
      change k0 ≤ (D - 1) * t at hbt
      omega
    · obtain ⟨t, ht, hbt⟩ := hlocal L R BT D d hD hrows1 hcols1 hpos
        (fun x hx hMx => hd1 ⟨x, LinearMap.mem_ker.mpr hMx⟩ (by
          intro heq
          exact hx (congrArg (fun z : C1 => (z : R → ZMod 2)) heq)))
      have htrank : BT.rank = r := by
        simpa only [BT, r] using Matrix.rank_transpose B
      rw [htrank] at ht
      refine ⟨t, ht, ?_⟩
      change k1 ≤ (D - 1) * t at hbt
      omega
  obtain ⟨t, hdt, hbt⟩ := hbound
  have hDreal : 0 < (D : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hsub : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_one]
  have hkbound : (k : ℝ) ≤ 2 * ((D : ℝ) - 1) * (t : ℝ) := by
    have hh : (k : ℝ) ≤ 2 * (((D - 1 : ℕ) : ℝ) * (t : ℝ)) := by
      exact_mod_cast hbt
    rw [hsub] at hh
    simpa only [mul_assoc] using hh
  have hden : 0 < 2 * ((D : ℝ) - 1) := by linarith
  have hfrac : (k : ℝ) / (2 * ((D : ℝ) - 1)) ≤ (t : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hkbound]
  have hceil : Int.ceil ((k : ℝ) / (2 * ((D : ℝ) - 1))) ≤ (t : ℤ) := by
    apply Int.ceil_le.mpr
    simpa using hfrac
  have hceilR : (Int.ceil ((k : ℝ) / (2 * ((D : ℝ) - 1))) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hceil
  have hdtR : (d : ℝ) + (t : ℝ) = (r : ℝ) + 2 := by exact_mod_cast hdt
  have hknrR : (k : ℝ) + 2 * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hknr
  linarith only [hceilR, hdtR, hknrR]

theorem model_5c1b1cd577e96807f60f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((Fintype.card V : ℝ) / ((2 : ℝ) * (G.maxDegree : ℝ)))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have heven :
      ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W]
        (B : Matrix W W (ZMod 2)),
        Fintype.card W = n → (∀ i j, B i j = B j i) →
        (∀ i, B i i = 0) → Even B.rank := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ B hc hs hd
      by_cases hz : B = 0
      · rw [hz, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · obtain ⟨a, b, hab0⟩ : ∃ a b : W, B a b ≠ 0 := by
          by_contra hnot
          apply hz
          ext i j
          by_contra hij
          exact hnot ⟨i, j, hij⟩
        have hab : B a b = 1 := hone _ hab0
        have hba : B b a = 1 := (hs b a).trans hab
        have hne : a ≠ b := by
          intro h
          apply hab0
          rw [h]
          exact hd b
        let s : Finset W := ({a, b} : Finset W)ᶜ
        let T := ↥s
        have hsa : a ∉ s := by simp [s]
        have hsb : b ∉ s := by simp [s]
        have hcT : Fintype.card T = s.card := Fintype.card_coe s
        have hcards : Fintype.card T + 2 = Fintype.card W := by
          rw [hcT]
          have hh := Finset.card_add_card_compl ({a, b} : Finset W)
          rw [Finset.card_pair hne] at hh
          change 2 + s.card = Fintype.card W at hh
          omega
        have hlt : Fintype.card T < n := by omega
        have hsum (f : W → ZMod 2) :
            (∑ i : W, f i) = f a + f b + ∑ i : T, f (i : W) := by
          calc
            _ = (∑ i ∈ ({a, b} : Finset W), f i) + ∑ i ∈ s, f i :=
              (Finset.sum_add_sum_compl ({a, b} : Finset W) f).symm
            _ = _ := by
              rw [Finset.sum_pair hne, ← Finset.sum_coe_sort s f]
        let E : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) :=
          { toFun := fun y i => if hi : i ∈ s then y ⟨i, hi⟩ else 0
            map_add' := by
              intro x y
              funext i
              by_cases hi : i ∈ s <;> simp [hi]
            map_smul' := by
              intro c x
              funext i
              by_cases hi : i ∈ s <;> simp [hi] }
        let Q : Matrix W T (ZMod 2) := fun i j => B i (j : W)
        let P : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) := Q.mulVecLin
        have hP (y : T → ZMod 2) (i : W) :
            P y i = ∑ j : T, B i (j : W) * y j := rfl
        let U : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) :=
          E +
            (LinearMap.single (ZMod 2) (fun _ : W => ZMod 2) a).comp
              ((LinearMap.proj b).comp P) +
            (LinearMap.single (ZMod 2) (fun _ : W => ZMod 2) b).comp
              ((LinearMap.proj a).comp P)
        have hUa (y : T → ZMod 2) :
            U y a = ∑ j : T, B b (j : W) * y j := by
          change (E y a + (Pi.single a (P y b) : W → ZMod 2) a) +
            (Pi.single b (P y a) : W → ZMod 2) a = _
          simpa [E, hsa, hne, hne.symm, Pi.single_apply] using hP y b
        have hUb (y : T → ZMod 2) :
            U y b = ∑ j : T, B a (j : W) * y j := by
          change (E y b + (Pi.single a (P y b) : W → ZMod 2) b) +
            (Pi.single b (P y a) : W → ZMod 2) b = _
          simpa [E, hsb, hne, hne.symm, Pi.single_apply] using hP y a
        have hUt (y : T → ZMod 2) (i : T) : U y (i : W) = y i := by
          have hia : (i : W) ≠ a := by
            intro h
            exact hsa (h ▸ i.property)
          have hib : (i : W) ≠ b := by
            intro h
            exact hsb (h ▸ i.property)
          change (E y (i : W) + (Pi.single a (P y b) : W → ZMod 2) (i : W)) +
            (Pi.single b (P y a) : W → ZMod 2) (i : W) = y i
          simp [E, i.property, hia, hib, hia.symm, hib.symm, Pi.single_apply]
        let N : Matrix T T (ZMod 2) := fun i j =>
          B (i : W) (j : W) + B (i : W) a * B b (j : W) +
            B (i : W) b * B a (j : W)
        have hNs (i j : T) : N i j = N j i := by
          dsimp only [N]
          rw [hs (i : W) (j : W), hs b (j : W), hs a (j : W),
            hs (i : W) a, hs (i : W) b]
          ring
        have hNd (i : T) : N i i = 0 := by
          dsimp only [N]
          rw [hd (i : W), zero_add, hs b (i : W), hs a (i : W)]
          rw [mul_comm (B (i : W) b) (B (i : W) a)]
          exact htwo _
        have hUa0 (y : T → ZMod 2) : B.mulVecLin (U y) a = 0 := by
          change (∑ i : W, B a i * U y i) = 0
          rw [hsum]
          simp only [hd a, hab, zero_mul, one_mul, zero_add, hUb, hUt]
          exact htwo _
        have hUb0 (y : T → ZMod 2) : B.mulVecLin (U y) b = 0 := by
          change (∑ i : W, B b i * U y i) = 0
          rw [hsum]
          simp only [hba, hd b, one_mul, zero_mul, add_zero, hUa, hUt]
          exact htwo _
        have hUrow (y : T → ZMod 2) (i : T) :
            B.mulVecLin (U y) (i : W) = N.mulVecLin y i := by
          change (∑ j : W, B (i : W) j * U y j) = ∑ j : T, N i j * y j
          rw [hsum, hUa, hUb]
          simp only [hUt]
          dsimp only [N]
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
          ring
        have hUker (y : T → ZMod 2) (hy : N.mulVecLin y = 0) :
            B.mulVecLin (U y) = 0 := by
          funext i
          change B.mulVecLin (U y) i = 0
          by_cases hia : i = a
          · subst i
            exact hUa0 y
          by_cases hib : i = b
          · subst i
            exact hUb0 y
          have hi : i ∈ s := by simp [s, hia, hib]
          exact (hUrow y ⟨i, hi⟩).trans (congrFun hy ⟨i, hi⟩)
        have hrecon (x : W → ZMod 2) (hx : B.mulVecLin x = 0) :
            x = U (fun i : T => x (i : W)) := by
          have hxa : x a = ∑ i : T, B b (i : W) * x (i : W) := by
            apply heq
            have hh := congrFun hx b
            change (∑ i : W, B b i * x i) = 0 at hh
            rw [hsum] at hh
            simpa only [hba, hd b, one_mul, zero_mul, add_zero] using hh
          have hxb : x b = ∑ i : T, B a (i : W) * x (i : W) := by
            apply heq
            have hh := congrFun hx a
            change (∑ i : W, B a i * x i) = 0 at hh
            rw [hsum] at hh
            simpa only [hd a, hab, zero_mul, one_mul, zero_add] using hh
          funext i
          by_cases hia : i = a
          · subst i
            rw [hUa]
            exact hxa
          by_cases hib : i = b
          · subst i
            rw [hUb]
            exact hxb
          have hi : i ∈ s := by simp [s, hia, hib]
          exact (hUt (fun j : T => x (j : W)) ⟨i, hi⟩).symm
        let K := LinearMap.ker B.mulVecLin
        let K' := LinearMap.ker N.mulVecLin
        have hres (x : K) :
            N.mulVecLin (fun i : T => (x : W → ZMod 2) (i : W)) = 0 := by
          funext i
          have hx : B.mulVecLin (x : W → ZMod 2) = 0 :=
            LinearMap.mem_ker.mp x.property
          have hr := hUrow (fun j : T => (x : W → ZMod 2) (j : W)) i
          rw [← hrecon (x : W → ZMod 2) hx] at hr
          exact hr.symm.trans (congrFun hx (i : W))
        let R : K →ₗ[ZMod 2] K' :=
          { toFun := fun x => ⟨fun i : T => (x : W → ZMod 2) (i : W), hres x⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              rfl
            map_smul' := by
              intro c x
              apply Subtype.ext
              rfl }
        let e : K ≃ₗ[ZMod 2] K' :=
          { R with
            invFun := fun y =>
              ⟨U (y : T → ZMod 2),
                hUker (y : T → ZMod 2) (LinearMap.mem_ker.mp y.property)⟩
            left_inv := by
              intro x
              apply Subtype.ext
              change U (fun i : T => (x : W → ZMod 2) (i : W)) =
                (x : W → ZMod 2)
              exact (hrecon _ (LinearMap.mem_ker.mp x.property)).symm
            right_inv := by
              intro y
              apply Subtype.ext
              funext i
              change U (y : T → ZMod 2) (i : W) = (y : T → ZMod 2) i
              exact hUt (y : T → ZMod 2) i }
        have hk : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) K' :=
          e.finrank_eq
        have hrB : B.rank + Module.finrank (ZMod 2) K = Fintype.card W := by
          simpa only [Matrix.rank, K, Module.finrank_fintype_fun_eq_card] using
            LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        have hrN : N.rank + Module.finrank (ZMod 2) K' = Fintype.card T := by
          simpa only [Matrix.rank, K', Module.finrank_fintype_fun_eq_card] using
            LinearMap.finrank_range_add_finrank_ker N.mulVecLin
        have hstep : B.rank = N.rank + 2 := by omega
        obtain ⟨r, hr⟩ := ih (Fintype.card T) hlt T N rfl hNs hNd
        exact ⟨r + 1, by omega⟩
  let M := G.adjMatrix (ZMod 2)
  have hsym (v w : V) : M v w = M w v :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply w v
  have hdiag (v : V) : M v v = 0 :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).apply_diag v
  obtain ⟨q, hq⟩ := heven (Fintype.card V) V M rfl hsym hdiag
  have hr2 : M.rank = 2 * q := by omega
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := Nat.eq_zero_of_not_pos h
    have hg := h_guard.1
    rw [hz] at hg
    norm_num at hg
  have hD : 0 < G.maxDegree := by
    by_contra h
    have hz : G.maxDegree = 0 := Nat.eq_zero_of_not_pos h
    have hg := h_guard.2.1
    rw [hz] at hg
    norm_num at hg
  obtain ⟨S, hSsub, hScard, hSspan, hSind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (Set.range M.col)
  have hScard' : S.card = M.rank := by
    rw [M.rank_eq_finrank_span_cols]
    exact hScard
  let supp : (V → ZMod 2) → Finset V :=
    fun x => Finset.univ.filter (fun i => x i ≠ 0)
  have hsuppcol (v : V) : supp (M.col v) = G.neighborFinset v := by
    ext i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.mem_neighborFinset]
    change M i v ≠ 0 ↔ G.Adj v i
    rw [hsym i v]
    by_cases h : G.Adj v i <;> simp [M, SimpleGraph.adjMatrix_apply, h]
  have hsupp (x : V → ZMod 2) (hx : x ∈ S) :
      (supp x).card ≤ G.maxDegree := by
    obtain ⟨v, hv⟩ := hSsub hx
    rw [← hv, hsuppcol, G.card_neighborFinset_eq_degree]
    exact G.degree_le_maxDegree v
  have hcover : (Finset.univ : Finset V) ⊆ S.biUnion supp := by
    intro i hi
    by_contra hin
    have hz : ∀ x ∈ S, x i = 0 := by
      intro x hx
      by_contra hxi
      apply hin
      exact Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩⟩
    let Z : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (LinearMap.proj i)
    have hSZ : Submodule.span (ZMod 2) (S : Set (V → ZMod 2)) ≤ Z := by
      apply Submodule.span_le.mpr
      intro x hx
      change x i = 0
      exact hz x hx
    have hcol (v : V) : M.col v ∈ Z := by
      apply hSZ
      rw [hSspan]
      exact Submodule.subset_span ⟨v, rfl⟩
    obtain ⟨v, hiv⟩ := (G.degree_pos_iff_exists_adj i).mp
      (lt_of_lt_of_le hdeg (G.minDegree_le_degree i))
    have hzero : M i v = 0 := by
      have hh := hcol v
      change M i v = 0 at hh
      exact hh
    have h_one : M i v = 1 := by
      simp [M, SimpleGraph.adjMatrix_apply, hiv]
    exact zero_ne_one (hzero.symm.trans h_one)
  have hcount : Fintype.card V ≤ M.rank * G.maxDegree := by
    calc
      _ = (Finset.univ : Finset V).card := by simp
      _ ≤ (S.biUnion supp).card := Finset.card_le_card hcover
      _ ≤ ∑ x ∈ S, (supp x).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S, G.maxDegree :=
        Finset.sum_le_sum (fun x hx => hsupp x hx)
      _ = S.card * G.maxDegree := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      _ = M.rank * G.maxDegree := by rw [hScard']
  have hcountR : (Fintype.card V : ℝ) ≤ (M.rank : ℝ) * (G.maxDegree : ℝ) := by
    exact_mod_cast hcount
  have hr2R : (M.rank : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hr2
  have hDR : (0 : ℝ) < (G.maxDegree : ℝ) := by exact_mod_cast hD
  have hfrac : (Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ)) ≤ (q : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (G.maxDegree : ℝ))).2
    calc
      _ ≤ (M.rank : ℝ) * (G.maxDegree : ℝ) := hcountR
      _ = (q : ℝ) * (2 * (G.maxDegree : ℝ)) := by rw [hr2R]; ring
  have hceil : Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) ≤
      (q : ℤ) := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using hfrac
  have hceilR :
      (Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) : ℝ) ≤
        (q : ℝ) := by exact_mod_cast hceil
  have hdim : M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hdimR : (M.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) =
        (Fintype.card V : ℝ) := by exact_mod_cast hdim
  change (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) +
    2 * (Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) : ℝ) ≤
      (Fintype.card V : ℝ)
  linarith only [hdimR, hr2R, hceilR]

theorem model_01fb90bd2b4c0045f68b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((Fintype.card V : ℝ) / ((2 : ℝ) * (G.maxDegree : ℝ)))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  apply model_5c1b1cd577e96807f60f G
  refine ⟨h_guard.1, ?_, h_guard.2.2⟩
  exact le_trans (by norm_num : (9999999 / 10000000 : ℝ) ≤ (19999999 / 10000000 : ℝ)) h_guard.2.1
theorem model_87e1404743f540083555 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((G.maxDegree : ℝ) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ (((G.maxDegree : ℝ) - (1 : ℝ)) * (((Fintype.card V : ℝ) + (4 : ℝ)) - ((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))))) := by
  sorry
