import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic








open scoped BigOperators

theorem hull_min_degree_le_1_average_degree_0_36a8fb326490 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.minDegree : ℝ) ≤ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · rw [if_neg hV]
    have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
      calc
        Fintype.card V * G.minDegree =
            Finset.univ.sum (fun _ : V => G.minDegree) := by simp
        _ ≤ Finset.univ.sum (fun v : V => G.degree v) :=
          Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    apply (le_div_iff₀ hpos).2
    calc
      (G.minDegree : ℝ) * (Fintype.card V : ℝ) =
          (Fintype.card V : ℝ) * (G.minDegree : ℝ) := mul_comm _ _
      _ ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hsum

theorem hull3d_min_degree_le_0_0222222_0_8_size_spectral_spread_0_is_connected_98b1a636aa35 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.minDegree : ℝ) ≤ (((1111111111111157 / 50000000000000000 : ℝ) * (G.edgeFinset.card : ℝ)) + ((4 / 5 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) := by
  classical
  letI : Nonempty V := h_guard.nonempty
  have hV : Fintype.card V ≠ 0 := ne_of_gt (Fintype.card_pos (α := V))
  simp only [if_neg hV]
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  change (G.minDegree : ℝ) ≤
    (1111111111111157 / 50000000000000000 : ℝ) * (G.edgeFinset.card : ℝ) +
      (4 / 5 : ℝ) * (sSup (Set.range f) - sInf (Set.range f))
  have hspread0 : 0 ≤ sSup (Set.range f) - sInf (Set.range f) := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    have hi := csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self v)
    have hs := le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v)
    linarith
  by_cases hd0 : G.minDegree = 0
  · simp only [hd0, Nat.cast_zero]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) hspread0)
  · let E := EuclideanSpace ℝ V
    let T : E →ₗ[ℝ] E := (G.adjMatrix ℝ).toEuclideanLin
    have hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    let C : E →L[ℝ] E := hT.toSelfAdjoint.val
    let q : E → ℝ := fun x => inner ℝ (T x) x / ‖x‖ ^ 2
    have hqabs (x : E) : |q x| ≤ ‖C‖ := by
      change |C.rayleighQuotient x| ≤ ‖C‖
      exact C.rayleighQuotient_le_norm x
    have hqb : BddAbove (Set.range fun x : {x : E // x ≠ 0} => q x) := by
      refine ⟨‖C‖, ?_⟩
      rintro y ⟨x, rfl⟩
      exact (le_abs_self (q x)).trans (hqabs x)
    have hqlb : BddBelow (Set.range fun x : {x : E // x ≠ 0} => q x) := by
      refine ⟨-‖C‖, ?_⟩
      rintro y ⟨x, rfl⟩
      exact (neg_le_neg (hqabs x)).trans (neg_abs_le (q x))
    have hqtop : (⨆ x : {x : E // x ≠ 0}, q x) ∈ Set.range f := by
      change (⨆ x : {x : E // x ≠ 0}, q x) ∈
        Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues
      rw [← (G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues,
        ← Matrix.spectrum_toLpLin 2]
      exact hT.hasEigenvalue_iSup_of_finiteDimensional.mem_spectrum
    have hqbot : (⨅ x : {x : E // x ≠ 0}, q x) ∈ Set.range f := by
      change (⨅ x : {x : E // x ≠ 0}, q x) ∈
        Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues
      rw [← (G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues,
        ← Matrix.spectrum_toLpLin 2]
      exact hT.hasEigenvalue_iInf_of_finiteDimensional.mem_spectrum
    have hqle (x : E) (hx : x ≠ 0) : q x ≤ sSup (Set.range f) := by
      exact (le_ciSup hqb (⟨x, hx⟩ : {x : E // x ≠ 0})).trans
        (le_csSup (Set.finite_range f).bddAbove hqtop)
    have hleq (x : E) (hx : x ≠ 0) : sInf (Set.range f) ≤ q x := by
      exact (csInf_le (Set.finite_range f).bddBelow hqbot).trans
        (ciInf_le hqlb (⟨x, hx⟩ : {x : E // x ≠ 0}))
    have hqform (x : V → ℝ) :
        q (WithLp.toLp 2 x) =
          dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) / dotProduct x x := by
      change inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (WithLp.toLp 2 x))
          (WithLp.toLp 2 x) /
            ‖(WithLp.toLp 2 x : EuclideanSpace ℝ V)‖ ^ 2 =
          dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) / dotProduct x x
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp,
        EuclideanSpace.real_norm_sq_eq]
      simp only [WithLp.ofLp_toLp, star_trivial, PiLp.toLp_apply,
        dotProduct, pow_two]
    have hone : (WithLp.toLp 2 (1 : V → ℝ) : E) ≠ 0 := by
      intro h
      have hzero : (1 : V → ℝ) = 0 := (WithLp.toLp_eq_zero 2).mp h
      exact (one_ne_zero : (1 : V → ℝ) ≠ 0) hzero
    have hnumone : dotProduct (1 : V → ℝ)
        (Matrix.mulVec (G.adjMatrix ℝ) 1) =
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      calc
        _ = ∑ v : V, (G.degree v : ℝ) := by simp [dotProduct]
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hqone : q (WithLp.toLp 2 (1 : V → ℝ)) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) := by
      rw [hqform, hnumone]
      simp [dotProduct]
    have hminavg := hull_min_degree_le_1_average_degree_0_36a8fb326490 G
    rw [if_neg hV] at hminavg
    have hmax : (G.minDegree : ℝ) ≤ sSup (Set.range f) := by
      have h := hqle (WithLp.toLp 2 (1 : V → ℝ)) hone
      rw [hqone] at h
      exact hminavg.trans h
    let a : V := Classical.choice (inferInstance : Nonempty V)
    obtain ⟨b, hab⟩ := (G.degree_pos_iff_exists_adj a).mp
      (lt_of_lt_of_le (Nat.pos_of_ne_zero hd0) (G.minDegree_le_degree a))
    let x : V → ℝ := Pi.single a 1 - Pi.single b 1
    have hxne : (WithLp.toLp 2 x : E) ≠ 0 := by
      intro h
      have hzero : x = 0 := (WithLp.toLp_eq_zero 2).mp h
      have hval := congrFun hzero a
      simp [x, hab.ne, hab.ne'] at hval
    have hnum : dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) = -2 := by
      norm_num [x, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
        Matrix.mulVec_single_one, Matrix.col_apply, hab, hab.symm]
    have hden : dotProduct x x = 2 := by
      norm_num [x, sub_dotProduct, dotProduct_sub, hab.ne, hab.ne']
    have hqedge : q (WithLp.toLp 2 x) = -1 := by
      rw [hqform, hnum, hden]
      norm_num
    have hsmall : sInf (Set.range f) ≤ -1 := by
      have h := hleq (WithLp.toLp 2 x) hxne
      rw [hqedge] at h
      exact h
    have hspread : (G.minDegree : ℝ) + 1 ≤
        sSup (Set.range f) - sInf (Set.range f) := by
      linarith
    have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    have hprod : (G.minDegree : ℝ) * (Fintype.card V : ℝ) ≤
        (2 : ℝ) * (G.edgeFinset.card : ℝ) :=
      (le_div_iff₀ hnpos).mp hminavg
    have hn : G.minDegree + 1 ≤ Fintype.card V :=
      Nat.succ_le_of_lt G.minDegree_lt_card
    have hn' : (G.minDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hn
    have hsize : (G.minDegree : ℝ) * ((G.minDegree : ℝ) + 1) ≤
        (2 : ℝ) * (G.edgeFinset.card : ℝ) :=
      (mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg G.minDegree)).trans hprod
    have hpoly : 0 ≤ ((G.minDegree : ℝ) - 8) * ((G.minDegree : ℝ) - 9) := by
      by_cases hd8 : G.minDegree ≤ 8
      · have hd8' : (G.minDegree : ℝ) ≤ 8 := by exact_mod_cast hd8
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hd9 : (9 : ℕ) ≤ G.minDegree := by omega
        have hd9' : (9 : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast hd9
        exact mul_nonneg (by linarith) (by linarith)
    have hcoef : (1 / 45 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (1111111111111157 / 50000000000000000 : ℝ) * (G.edgeFinset.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    nlinarith only [hsize, hpoly, hspread, hcoef]
