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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

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

theorem model_c0b68b8f55a47e0a3735 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) := by
  classical
  let A := G.adjMatrix (ZMod 2)
  let r := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A.col))
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range A.col)
  choose a ha using hf
  have hspan' : Submodule.span (ZMod 2) (Set.range (A.col ∘ a)) =
      Submodule.span (ZMod 2) (Set.range A.col) := by
    have hfun : A.col ∘ a = f := by
      funext i
      exact ha i
    rw [hfun]
    exact hspan
  let T : Finset V := Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
  have hz : ∀ v : V, v ∉ T → G.degree v = 0 := by
    intro v hv
    have hbase (i : Fin r) : A.col (a i) v = 0 := by
      have hnot : ¬ G.Adj v (a i) := by
        intro h
        apply hv
        change v ∈ Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, (G.mem_neighborFinset (a i) v).mpr h.symm⟩
      simp [Matrix.col_apply, A, hnot]
    have hzero : ∀ x ∈ Submodule.span (ZMod 2) (Set.range (A.col ∘ a)), x v = 0 := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x v = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        exact hbase i
      · rfl
      · intro x y _ _ hx hy
        change x v + y v = 0
        rw [hx, hy, add_zero]
      · intro b x _ hx
        change b * x v = 0
        rw [hx, mul_zero]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hpos
    have hwzero : A.col w v = 0 := hzero (A.col w) (by
      rw [hspan']
      exact Submodule.subset_span ⟨w, rfl⟩)
    simpa [Matrix.col_apply, A, hw] using hwzero
  have hT : T.card ≤ r * G.maxDegree := by
    calc
      T.card ≤ ∑ i : Fin r, (G.neighborFinset (a i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin r, G.maxDegree := Finset.sum_le_sum (fun i _ => by
        simpa only [G.card_neighborFinset_eq_degree] using G.degree_le_maxDegree (a i))
      _ = r * G.maxDegree := by simp
  have he : 2 * G.edgeFinset.card ≤ r * G.maxDegree ^ 2 := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ v ∈ T, G.degree v := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro v _ hv
        exact hz v hv
      _ ≤ ∑ _v ∈ T, G.maxDegree :=
        Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
      _ = T.card * G.maxDegree := by simp
      _ ≤ (r * G.maxDegree) * G.maxDegree := Nat.mul_le_mul_right _ hT
      _ = r * G.maxDegree ^ 2 := by ring
  have hr : r + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = Fintype.card V := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at h
    exact h
  have hrreal : (r : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
      (Fintype.card V : ℝ) := by
    exact_mod_cast hr
  have hrsub : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) = (r : ℝ) := by
    linarith
  change (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
    ((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ)) *
      (G.maxDegree : ℝ) ^ 2
  rw [hrsub]
  exact_mod_cast he

theorem model_92bb8eaf5887bd185218 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((G.edgeFinset.card : ℝ) / ((G.maxDegree : ℝ) ^ 2))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  have hD : (0 : ℝ) < (G.maxDegree : ℝ) := by
    linarith only [h_guard.1]
  have hD2 : (0 : ℝ) < (G.maxDegree : ℝ) ^ 2 := by
    positivity
  let k : ℤ := Int.floor
    (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2)
        (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / 2)
  have hk : (k : ℝ) =
      ((Fintype.card V : ℝ) -
        (Module.finrank (ZMod 2)
          (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / 2 := by
    exact model_8507aba979de2b196665 G
  have hedge := model_c0b68b8f55a47e0a3735 G
  have hratio : (G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2 ≤
      (k : ℝ) := by
    apply (div_le_iff₀ hD2).2
    rw [hk]
    nlinarith only [hedge]
  have hceil : Int.ceil
      ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2) ≤ k :=
    Int.ceil_le.mpr hratio
  have hceilR :
      (Int.ceil ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ^ 2) : ℝ) ≤
        (k : ℝ) := by
    exact_mod_cast hceil
  linarith only [hk, hceilR]

theorem model_d1a96951729d303c134a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  have hrow :
      ∀ (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj]
        (S : Set W) [DecidablePred (fun w => w ∈ S)]
        (x : W → ZMod 2) (z : S),
        (∀ w : W, w ∉ S → H.adjMatrix (ZMod 2) (z : W) w * x w = 0) →
        ((H.induce S).adjMatrix (ZMod 2)).mulVecLin (fun w : S => x (w : W)) z =
          (H.adjMatrix (ZMod 2)).mulVecLin x (z : W) := by
    intro W _ _ H _ S _ x z hz
    change (∑ w : S, (H.induce S).adjMatrix (ZMod 2) z w * x (w : W)) =
      ∑ w : W, H.adjMatrix (ZMod 2) (z : W) w * x w
    symm
    apply Finset.sum_congr_set S
    · intro w hw
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.induce_adj]
    · exact hz
  have haux :
      ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ),
        Fintype.card W = n → H.IsAcyclic → (∀ w, H.degree w ≤ D) →
        ∃ k : ℕ,
          Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) +
            2 * k ≤ Fintype.card W ∧ H.edgeFinset.card ≤ k * D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H _ D hcard hac hdeg
      by_cases hadj : ∃ a b : W, H.Adj a b
      · obtain ⟨a, b, hab⟩ := hadj
        letI : Nonempty W := ⟨a⟩
        obtain ⟨u, z, p, hp, hmax⟩ :=
          SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
        have hnil : ¬ p.Nil := by
          intro hn
          have hh := hmax a b (SimpleGraph.Walk.cons hab .nil) (by simp [hab.ne])
          have hzero : p.length = 0 := hn.length_eq_zero
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hzero] at hh
          omega
        let v : W := p.snd
        have huv : H.Adj u v := p.adj_snd hnil
        have hleaf (w : W) (hw : H.Adj u w) : w = v := by
          apply hac.eq_snd_of_adj_start hp hw
          by_contra hnot
          have hpath : (p.cons hw.symm).IsPath := hp.cons hnot
          have hh := hmax w z (p.cons hw.symm) hpath
          simp only [SimpleGraph.Walk.length_cons] at hh
          omega
        have hnu : H.neighborFinset u = {v} := by
          ext w
          constructor
          · intro hw
            exact Finset.mem_singleton.mpr
              (hleaf w ((H.mem_neighborFinset u w).mp hw))
          · intro hw
            have hwv : w = v := Finset.mem_singleton.mp hw
            rw [hwv]
            exact (H.mem_neighborFinset u v).mpr huv
        let W1 := ↥(({v} : Set W)ᶜ)
        let H1 : SimpleGraph W1 := H.induce ({v} : Set W)ᶜ
        let u1 : W1 := ⟨u, by simpa using huv.ne⟩
        let W2 := ↥(({u1} : Set W1)ᶜ)
        let H2 : SimpleGraph W2 := H1.induce ({u1} : Set W1)ᶜ
        have hnone (w : W1) : ¬ H1.Adj u1 w := by
          intro hw
          have heq : (w : W) = v := hleaf (w : W) hw
          exact w.property (Set.mem_singleton_iff.mpr heq)
        have hu1deg : H1.degree u1 = 0 := by
          rw [← H1.card_neighborFinset_eq_degree u1]
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          exact hnone w ((H1.mem_neighborFinset u1 w).mp hw)
        have hc1 : Fintype.card W1 = Fintype.card W - 1 := by
          dsimp only [W1]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hc2 : Fintype.card W2 = Fintype.card W1 - 1 := by
          dsimp only [W2]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos1 : 0 < Fintype.card W1 := Fintype.card_pos_iff.mpr ⟨u1⟩
        have hcards : Fintype.card W2 + 2 = Fintype.card W := by omega
        have hlt : Fintype.card W2 < n := by omega
        let K := LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin
        let K2 := LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin
        have hxv (x : K) : (x : W → ZMod 2) v = 0 := by
          have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
            x.property
          have hh := congrFun hxA u
          simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
            hnu, Finset.sum_singleton, Pi.zero_apply] using hh
        have hres (x : K) :
            (H2.adjMatrix (ZMod 2)).mulVecLin
              (fun w : W2 => (x : W → ZMod 2) w.val.val) = 0 := by
          funext w
          have hz1 (j : W) (hj : j ∉ ({v} : Set W)ᶜ) :
              H.adjMatrix (ZMod 2) w.val.val j * (x : W → ZMod 2) j = 0 := by
            have heq : j = v := by simpa using hj
            subst j
            rw [hxv x, mul_zero]
          have hz2 (j : W1) (hj : j ∉ ({u1} : Set W1)ᶜ) :
              H1.adjMatrix (ZMod 2) w.val j * (x : W → ZMod 2) j.val = 0 := by
            have heq : j = u1 := by simpa using hj
            subst j
            have hn : ¬ H1.Adj w.val u1 := fun h => hnone w.val h.symm
            change (if H1.Adj w.val u1 then (1 : ZMod 2) else 0) *
              (x : W → ZMod 2) (u1 : W) = 0
            rw [if_neg hn, zero_mul]
          calc
            (H2.adjMatrix (ZMod 2)).mulVecLin
                (fun j : W2 => (x : W → ZMod 2) j.val.val) w =
                (H1.adjMatrix (ZMod 2)).mulVecLin
                  (fun j : W1 => (x : W → ZMod 2) j.val) w.val :=
              hrow W1 H1 ({u1} : Set W1)ᶜ
                (fun j : W1 => (x : W → ZMod 2) j.val) w hz2
            _ = (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) w.val.val :=
              hrow W H ({v} : Set W)ᶜ (x : W → ZMod 2) w.val hz1
            _ = 0 := congrFun
              (show (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 from
                x.property) w.val.val
        let R : K →ₗ[ZMod 2] K2 :=
          { toFun := fun x => ⟨fun w => (x : W → ZMod 2) w.val.val, hres x⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              rfl
            map_smul' := by
              intro c x
              apply Subtype.ext
              rfl }
        have hRinj : Function.Injective R := by
          have hzero (x : K) (hx : R x = 0) : x = 0 := by
            have hrest (j : W) (hju : j ≠ u) (hjv : j ≠ v) :
                (x : W → ZMod 2) j = 0 := by
              let j1 : W1 := ⟨j, by simpa using hjv⟩
              let j2 : W2 := ⟨j1, by
                change j1 ≠ u1
                intro heq
                exact hju (congrArg (fun t : W1 => (t : W)) heq)⟩
              have hh := congrArg (fun t : K2 => (t : W2 → ZMod 2) j2) hx
              change (x : W → ZMod 2) j = 0 at hh
              exact hh
            have hxu : (x : W → ZMod 2) u = 0 := by
              have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
                x.property
              have hr : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) v =
                  (x : W → ZMod 2) u := by
                rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
                apply Finset.sum_eq_single u
                · intro j hj hju
                  by_cases hjv : j = v
                  · simpa only [hjv] using hxv x
                  · exact hrest j hju hjv
                · intro hnot
                  exact (hnot ((H.mem_neighborFinset v u).mpr huv.symm)).elim
              exact hr.symm.trans (congrFun hxA v)
            apply Subtype.ext
            funext j
            change (x : W → ZMod 2) j = 0
            by_cases hju : j = u
            · simpa only [hju] using hxu
            by_cases hjv : j = v
            · simpa only [hjv] using hxv x
            exact hrest j hju hjv
          intro x y hxy
          apply sub_eq_zero.mp
          apply hzero
          rw [map_sub, hxy, sub_self]
        have hdim : Module.finrank (ZMod 2) K ≤ Module.finrank (ZMod 2) K2 :=
          LinearMap.finrank_le_finrank_of_injective hRinj
        change Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) ≤
          Module.finrank (ZMod 2) (LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin) at hdim
        have hdeg2 (w : W2) : H2.degree w ≤ D := by
          calc
            H2.degree w ≤ H1.degree w.val :=
              (SimpleGraph.Copy.induce H1 ({u1} : Set W1)ᶜ).degree_le w
            _ ≤ H.degree w.val.val :=
              (SimpleGraph.Copy.induce H ({v} : Set W)ᶜ).degree_le w.val
            _ ≤ D := hdeg w.val.val
        obtain ⟨k, hkdim, hkedge⟩ := ih (Fintype.card W2) hlt W2 H2 D rfl
          ((hac.induce ({v} : Set W)ᶜ).induce ({u1} : Set W1)ᶜ) hdeg2
        have hm1 : H1.edgeFinset.card = H.edgeFinset.card - H.degree v := by
          dsimp only [H1]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet]
        have hm2 : H2.edgeFinset.card = H1.edgeFinset.card := by
          dsimp only [H2]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet, hu1deg, Nat.sub_zero]
        have heq : H.edgeFinset.card = H2.edgeFinset.card + H.degree v := by
          have hem := H.degree_le_card_edgeFinset v
          omega
        refine ⟨k + 1, ?_, ?_⟩
        · omega
        · rw [Nat.add_mul, Nat.one_mul]
          have hdv := hdeg v
          omega
      · have hbot : H = ⊥ := by
          apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
          intro a b hab
          exact hadj ⟨a, b, hab⟩
        refine ⟨0, ?_, ?_⟩
        · simp only [Nat.mul_zero, Nat.add_zero]
          calc
            _ ≤ Module.finrank (ZMod 2) (W → ZMod 2) := Submodule.finrank_le _
            _ = Fintype.card W := Module.finrank_fintype_fun_eq_card (ZMod 2)
        · simp [hbot]
  obtain ⟨k, hkdim, hkedge⟩ := haux (Fintype.card V) V G G.maxDegree rfl
    h_guard.1 (fun v => G.degree_le_maxDegree v)
  have hD : (0 : ℝ) < (G.maxDegree : ℝ) := by
    linarith only [h_guard.2.1]
  have hdimR :
      (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) +
        2 * (k : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hkdim
  have hedgeR : (G.edgeFinset.card : ℝ) ≤ (k : ℝ) * (G.maxDegree : ℝ) := by
    exact_mod_cast hkedge
  have hratio : (G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ) ≤ (k : ℝ) :=
    (div_le_iff₀ hD).2 hedgeR
  have hceil : Int.ceil ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ)) ≤ (k : ℤ) := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using hratio
  have hceilR :
      (Int.ceil ((G.edgeFinset.card : ℝ) / (G.maxDegree : ℝ)) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hceil
  linarith only [hdimR, hceilR]

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

theorem model_f625da6cfd36c5bd35d9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.floor ((G.cliqueNum : ℝ) / (2 : ℝ))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let q : ℕ := G.cliqueNum / 2
  obtain ⟨c, hc⟩ := G.exists_isNClique_cliqueNum
  have hq : 2 * q ≤ c.card := by
    rw [hc.card_eq]
    dsimp only [q]
    omega
  obtain ⟨s, hsc, hscard⟩ := Finset.exists_subset_card_eq (s := c) (n := 2 * q) hq
  have hsclique : G.IsClique (s : Set V) := by
    intro v hv w hw hne
    exact hc.isClique (hsc hv) (hsc hw) hne
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hzero (x : V → ZMod 2) (hx : A x = 0)
      (hout : ∀ v : V, v ∉ s → x v = 0) : x = 0 := by
    let z : ZMod 2 := ∑ w ∈ s, x w
    have hrow (v : V) (hv : v ∈ s) :
        A x v = ∑ w ∈ s.erase v, x w := by
      change (∑ w : V, (G.adjMatrix (ZMod 2)) v w * x w) = _
      calc
        _ = ∑ w ∈ s.erase v, (G.adjMatrix (ZMod 2)) v w * x w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ (s.erase v))
          intro w _ hw
          by_cases hws : w ∈ s
          · have hwv : w = v := by
              by_contra hne
              exact hw (Finset.mem_erase.mpr ⟨hne, hws⟩)
            subst w
            simp
          · rw [hout w hws, mul_zero]
        _ = ∑ w ∈ s.erase v, x w := by
          apply Finset.sum_congr rfl
          intro w hw
          have hw' := Finset.mem_erase.mp hw
          have hadj : G.Adj v w := hsclique hv hw'.2 (Ne.symm hw'.1)
          simp [hadj]
    have hval (v : V) (hv : v ∈ s) : x v = z := by
      have hr : (∑ w ∈ s.erase v, x w) = 0 := by
        have hh := congrFun hx v
        rw [hrow v hv] at hh
        exact hh
      have hh := Finset.sum_erase_add s x hv
      rw [hr, zero_add] at hh
      exact hh
    have hz : z = 0 := by
      calc
        z = ∑ w ∈ s, z := Finset.sum_congr rfl (fun w hw => hval w hw)
        _ = (s.card : ZMod 2) * z := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = 0 := by
          rw [hscard, Nat.cast_mul, Nat.cast_ofNat, htwo, zero_mul, zero_mul]
    funext v
    by_cases hv : v ∈ s
    · exact (hval v hv).trans hz
    · exact hout v hv
  let p : K →ₗ[ZMod 2] ((sᶜ : Finset V) → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) v.1
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hx : A (x : V → ZMod 2) = 0 := x.property
    have hy : A (y : V → ZMod 2) = 0 := y.property
    have hker : A ((x : V → ZMod 2) - (y : V → ZMod 2)) = 0 := by
      rw [map_sub, hx, hy, sub_self]
    have hout : ∀ v : V, v ∉ s →
        ((x : V → ZMod 2) - (y : V → ZMod 2)) v = 0 := by
      intro v hv
      have hh := congrFun hxy ⟨v, Finset.mem_compl.mpr hv⟩
      change (x : V → ZMod 2) v = (y : V → ZMod 2) v at hh
      simp only [Pi.sub_apply, hh, sub_self]
    exact sub_eq_zero.mp (hzero _ hker hout)
  have hdim : Module.finrank (ZMod 2) K ≤ (sᶜ).card := by
    calc
      _ ≤ Module.finrank (ZMod 2) ((sᶜ : Finset V) → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hinj
      _ = (sᶜ).card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hcount : s.card + (sᶜ).card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hnat : Module.finrank (ZMod 2) K + 2 * q ≤ Fintype.card V := by
    omega
  have hfloor : Int.floor ((G.cliqueNum : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    have hlo : 2 * q ≤ G.cliqueNum := by
      dsimp only [q]
      omega
    have hhi : G.cliqueNum < 2 * (q + 1) := by
      dsimp only [q]
      omega
    have hloR : (2 : ℝ) * (q : ℝ) ≤ (G.cliqueNum : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (G.cliqueNum : ℝ) < (2 : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast hhi
    constructor <;> simp only [Int.cast_natCast] <;> linarith only [hloR, hhiR]
  change (Module.finrank (ZMod 2) K : ℝ) +
    (2 : ℝ) * (Int.floor ((G.cliqueNum : ℝ) / 2) : ℝ) ≤ (Fintype.card V : ℝ)
  rw [hfloor, Int.cast_natCast]
  exact_mod_cast hnat
theorem model_e81886cff56180757296 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((G.maxDegree : ℝ) - (1 : ℝ)) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ ((((G.maxDegree : ℝ) - (2 : ℝ)) * (Fintype.card V : ℝ)) + (2 : ℝ)) := by
  classical
  let A := G.adjMatrix (ZMod 2)
  let U : Finset V → Finset V := fun S => S.biUnion (fun v => G.neighborFinset v)
  have hD : 1 ≤ G.maxDegree := by
    have hp : (0 : ℝ) < (G.maxDegree : ℝ) := by
      linarith only [h_guard.2.1]
    have hn : 0 < G.maxDegree := by exact_mod_cast hp
    omega
  have hadj : ∃ a b : V, G.Adj a b := by
    by_contra h
    have hbot : G = ⊥ := by
      apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
      intro a b hab
      exact h ⟨a, b, hab⟩
    have hz : G.maxDegree = 0 := by simp [hbot]
    omega
  obtain ⟨a, b, hab⟩ := hadj
  have hentry (i j : V) (h : G.Adj i j) : A i j = 1 := by
    simp [A, SimpleGraph.adjMatrix_apply, h]
  have hdiag (i : V) : A i i = 0 := by
    simp [A, SimpleGraph.adjMatrix_apply]
  have hspanzero (S : Finset V) (i : V) (hi : i ∉ U S) :
      ∀ x ∈ Submodule.span (ZMod 2) (A.col '' (S : Set V)), x i = 0 := by
    let Z : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (LinearMap.proj i)
    have hle : Submodule.span (ZMod 2) (A.col '' (S : Set V)) ≤ Z := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      change A i j = 0
      have hn : ¬ G.Adj i j := by
        intro h
        apply hi
        exact Finset.mem_biUnion.mpr
          ⟨j, hj, (G.mem_neighborFinset j i).mpr h.symm⟩
      simp [A, SimpleGraph.adjMatrix_apply, hn]
    intro x hx
    have hz := hle hx
    change x i = 0 at hz
    exact hz
  have hnz : A.col a ≠ 0 := by
    intro h
    have hh := congrFun h b
    change A b a = 0 at hh
    rw [hentry b a hab.symm] at hh
    exact one_ne_zero hh
  have hinitLI :
      LinearIndepOn (ZMod 2) A.col (({a, b} : Finset V) : Set V) := by
    rw [Finset.coe_pair]
    apply (linearIndepOn_pair_iff (K := ZMod 2) A.col hab.ne hnz).mpr
    intro c hc
    have hh := congrFun hc a
    change c * A a a = A a b at hh
    rw [hdiag a, hentry a b hab, mul_zero] at hh
    exact zero_ne_one hh
  have hinitSub : ({a, b} : Finset V) ⊆ U {a, b} := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hva | hvb
    · rw [hva]
      exact Finset.mem_biUnion.mpr
        ⟨b, by simp, (G.mem_neighborFinset b a).mpr hab.symm⟩
    · rw [hvb]
      exact Finset.mem_biUnion.mpr
        ⟨a, by simp, (G.mem_neighborFinset a b).mpr hab⟩
  have hinitBound :
      (U {a, b}).card ≤ (G.maxDegree - 1) * ({a, b} : Finset V).card + 2 := by
    have hc : (U {a, b}).card ≤ 2 * G.maxDegree := by
      calc
        (U {a, b}).card =
            (G.neighborFinset a ∪ G.neighborFinset b).card := by simp [U]
        _ ≤ (G.neighborFinset a).card + (G.neighborFinset b).card :=
          Finset.card_union_le _ _
        _ = G.degree a + G.degree b := by
          rw [G.card_neighborFinset_eq_degree a, G.card_neighborFinset_eq_degree b]
        _ ≤ 2 * G.maxDegree := by
          have ha := G.degree_le_maxDegree a
          have hb := G.degree_le_maxDegree b
          omega
    rw [Finset.card_pair hab.ne]
    omega
  let Good : Finset V → Prop := fun S =>
    LinearIndepOn (ZMod 2) A.col (S : Set V) ∧
      S ⊆ U S ∧ a ∈ S ∧ (U S).card ≤ (G.maxDegree - 1) * S.card + 2
  let F : Finset (Finset V) := Finset.univ.filter Good
  have hF : F.Nonempty := by
    refine ⟨({a, b} : Finset V), ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨hinitLI, hinitSub, by simp, hinitBound⟩
  obtain ⟨S, hSF, hmax⟩ :=
    Finset.exists_max_image F (fun S : Finset V => S.card) hF
  have hgood : Good S := (Finset.mem_filter.mp hSF).2
  rcases hgood with ⟨hLI, hsub, has, hbound⟩
  have hcover : (Finset.univ : Finset V) ⊆ U S := by
    intro w _
    by_contra hw
    have haU : a ∈ U S := hsub has
    obtain ⟨p⟩ := h_guard.1 a w
    obtain ⟨d, _, hu, hv⟩ :=
      p.exists_boundary_dart (U S : Set V) haU hw
    have hnew : d.fst ∉ S := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr
        ⟨d.fst, h, (G.mem_neighborFinset d.fst d.snd).mpr d.adj⟩
    have hnotspan : A.col d.fst ∉
        Submodule.span (ZMod 2) (A.col '' (S : Set V)) := by
      intro hx
      have hz := hspanzero S d.snd hv (A.col d.fst) hx
      change A d.snd d.fst = 0 at hz
      rw [hentry d.snd d.fst d.adj.symm] at hz
      exact one_ne_zero hz
    have hLI' : LinearIndepOn (ZMod 2) A.col
        ((insert d.fst S : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      exact hLI.insert hnotspan
    have hUeq : U (insert d.fst S) = G.neighborFinset d.fst ∪ U S := by
      simp only [U, Finset.biUnion_insert]
    have hUS : U S ⊆ U (insert d.fst S) := by
      rw [hUeq]
      exact Finset.subset_union_right
    have hsub' : insert d.fst S ⊆ U (insert d.fst S) := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hUS hu
      · exact hUS (hsub hj)
    obtain ⟨t, ht, htu⟩ := Finset.mem_biUnion.mp hu
    have hinter : 0 < (G.neighborFinset d.fst ∩ U S).card := by
      apply Finset.card_pos.mpr
      refine ⟨t, Finset.mem_inter.mpr ⟨?_, hsub ht⟩⟩
      exact (G.mem_neighborFinset d.fst t).mpr
        ((G.mem_neighborFinset t d.fst).mp htu).symm
    have hinc : (U (insert d.fst S)).card ≤ (U S).card + (G.maxDegree - 1) := by
      have hh := Finset.card_union_add_card_inter (G.neighborFinset d.fst) (U S)
      have hd : (G.neighborFinset d.fst).card ≤ G.maxDegree := by
        simpa only [G.card_neighborFinset_eq_degree] using G.degree_le_maxDegree d.fst
      rw [← hUeq] at hh
      omega
    have hbound' : (U (insert d.fst S)).card ≤
        (G.maxDegree - 1) * (insert d.fst S).card + 2 := by
      rw [Finset.card_insert_of_notMem hnew, Nat.mul_add, Nat.mul_one]
      omega
    have hgood' : Good (insert d.fst S) :=
      ⟨hLI', hsub', Finset.mem_insert_of_mem has, hbound'⟩
    have hmem' : insert d.fst S ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hgood'⟩
    have hle := hmax (insert d.fst S) hmem'
    have hcard := Finset.card_insert_of_notMem hnew
    omega
  have hcard : Fintype.card V ≤ (G.maxDegree - 1) * S.card + 2 := by
    calc
      Fintype.card V = (Finset.univ : Finset V).card := by simp
      _ ≤ (U S).card := Finset.card_le_card hcover
      _ ≤ (G.maxDegree - 1) * S.card + 2 := hbound
  have hrank : S.card ≤ A.rank := by
    let f : ↥S → (V → ZMod 2) := fun v => A.col (v : V)
    have hf : LinearIndependent (ZMod 2) f := hLI
    have hsp : Submodule.span (ZMod 2) (Set.range f) ≤
        Submodule.span (ZMod 2) (Set.range A.col) := by
      apply Submodule.span_mono
      rintro _ ⟨v, rfl⟩
      exact ⟨(v : V), rfl⟩
    calc
      S.card = Fintype.card (↥S) := (Fintype.card_coe S).symm
      _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range f)) :=
        (finrank_span_eq_card hf).symm
      _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A.col)) :=
        Submodule.finrank_mono hsp
      _ = A.rank := A.rank_eq_finrank_span_cols.symm
  have hrankBound : Fintype.card V ≤ (G.maxDegree - 1) * A.rank + 2 :=
    hcard.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hrank) 2)
  have hboundR : (Fintype.card V : ℝ) ≤
      ((G.maxDegree : ℝ) - 1) * (A.rank : ℝ) + 2 := by
    have hh : (Fintype.card V : ℝ) ≤
        ((G.maxDegree - 1 : ℕ) : ℝ) * (A.rank : ℝ) + 2 := by
      exact_mod_cast hrankBound
    simpa only [Nat.cast_sub hD, Nat.cast_one] using hh
  have hdim : A.rank + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hdimR : (A.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
        (Fintype.card V : ℝ) := by exact_mod_cast hdim
  change ((G.maxDegree : ℝ) - 1) *
    (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) ≤
      ((G.maxDegree : ℝ) - 2) * (Fintype.card V : ℝ) + 2
  rw [← hdimR] at hboundR ⊢
  nlinarith only [hboundR]
