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

theorem hull3d_min_degree_le_0_0277778_0_8_size_spectral_spread_0_is_connected_f7cbf7fc2dc8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.minDegree : ℝ) ≤ (((13888888888888583 / 500000000000000000 : ℝ) * (G.edgeFinset.card : ℝ)) + ((4 / 5 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp only [if_pos hV, sub_self, mul_zero, add_zero,
      SimpleGraph.minDegree_of_subsingleton, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let S : ℝ := sSup (Set.range f)
    let I : ℝ := sInf (Set.range f)
    let t : ℝ := S - I
    let n : ℝ := Fintype.card V
    let m : ℝ := G.edgeFinset.card
    let d : ℝ := G.minDegree
    have hS (v : V) : f v ≤ S :=
      le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v)
    have hI (v : V) : I ≤ f v :=
      csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self v)
    obtain ⟨v0⟩ := (inferInstance : Nonempty V)
    have ht0 : 0 ≤ t := sub_nonneg.mpr ((hI v0).trans (hS v0))
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hd : 0 ≤ d := Nat.cast_nonneg _
    change d ≤ (13888888888888583 / 500000000000000000 : ℝ) * m +
      (4 / 5 : ℝ) * t
    by_cases hd0 : G.minDegree = 0
    · have hdz : d = 0 := by simp [d, hd0]
      rw [hdz]
      exact add_nonneg (mul_nonneg (by norm_num) hm0)
        (mul_nonneg (by norm_num) ht0)
    · have hn2 : 1 < Fintype.card V := by
        have hp := Nat.pos_of_ne_zero hd0
        have hl := G.minDegree_lt_card
        omega
      have hn1 : 1 < n := by
        change (1 : ℝ) < (Fintype.card V : ℝ)
        exact_mod_cast hn2
      have hn0 : 0 < n := by linarith only [hn1]
      have hdavg : d ≤ 2 * m / n := by
        simpa only [if_neg hV, d, m, n] using
          hull_min_degree_le_1_average_degree_0_36a8fb326490 G
      have hdm : n * d ≤ 2 * m := by
        simpa only [mul_comm] using (le_div_iff₀ hn0).mp hdavg
      let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
        (G.adjMatrix ℝ).toEuclideanLin
      let C : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V :=
        LinearMap.toContinuousLinearMap T
      have hT : T.IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
      let q : {x : EuclideanSpace ℝ V // x ≠ 0} → ℝ :=
        fun x => C.rayleighQuotient x
      let μ : ℝ := iSup q
      have hbq : BddAbove (Set.range q) := by
        refine ⟨‖C‖, ?_⟩
        rintro y ⟨z, rfl⟩
        exact (le_abs_self _).trans (C.rayleighQuotient_le_norm z)
      have hμev : Module.End.HasEigenvalue T μ := by
        simpa [μ, q, C, ContinuousLinearMap.rayleighQuotient,
          ContinuousLinearMap.reApplyInnerSelf_apply] using
          hT.hasEigenvalue_iSup_of_finiteDimensional
      have hμ : μ ∈ spectrum ℝ (G.adjMatrix ℝ) := by
        rw [← Matrix.spectrum_toLpLin 2]
        exact hμev.mem_spectrum
      rw [(G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hμ
      have hμS : μ ≤ S := le_csSup (Set.finite_range f).bddAbove hμ
      let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
      have hx : x ≠ 0 := by
        intro hh
        have hh' : (1 : ℝ) = 0 := by
          simpa only [x, PiLp.toLp_apply, PiLp.zero_apply] using
            congrArg (fun z : EuclideanSpace ℝ V => z v0) hh
        norm_num at hh'
      have hxnorm : ‖x‖ ^ 2 = n := by
        rw [← real_inner_self_eq_norm_sq]
        change (∑ _v : V, (1 : ℝ) * 1) = (Fintype.card V : ℝ)
        simp
      have hxinner : inner ℝ (T x) x = 2 * m := by
        change dotProduct (fun _ : V => (1 : ℝ))
          (Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ))) = 2 * m
        have hdeg : Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)) =
            fun v : V => (G.degree v : ℝ) := by
          funext v
          simp
        rw [hdeg]
        simp only [dotProduct, one_mul]
        change (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ)
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      have hqx : q ⟨x, hx⟩ = 2 * m / n := by
        change inner ℝ (T x) x / ‖x‖ ^ 2 = 2 * m / n
        rw [hxinner, hxnorm]
      have havgS : 2 * m / n ≤ S := by
        calc
          2 * m / n = q ⟨x, hx⟩ := hqx.symm
          _ ≤ μ := le_ciSup hbq ⟨x, hx⟩
          _ ≤ S := hμS
      have hdS : d ≤ S := hdavg.trans havgS
      have hsum0 : (∑ v : V, f v) = 0 := by
        simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
      obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
      change f v = S at hv
      have hcard : ((Finset.univ.erase v).card : ℝ) = n - 1 := by
        simp only [Finset.card_erase_of_mem (Finset.mem_univ v),
          Finset.card_univ, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
          Nat.cast_one, n]
      have hrest : (n - 1) * I ≤ ∑ w ∈ Finset.univ.erase v, f w := by
        calc
          (n - 1) * I = ∑ _w ∈ Finset.univ.erase v, I := by
            simp only [Finset.sum_const, nsmul_eq_mul, hcard]
          _ ≤ ∑ w ∈ Finset.univ.erase v, f w :=
            Finset.sum_le_sum (fun w _ => hI w)
      have hsumerase : f v + (∑ w ∈ Finset.univ.erase v, f w) = 0 :=
        (Finset.add_sum_erase Finset.univ f (Finset.mem_univ v)).trans hsum0
      have htrace : S + (n - 1) * I ≤ 0 := by
        linarith only [hrest, hsumerase, hv]
      have hspread : n * d ≤ (n - 1) * t := by
        have hprod : n * d ≤ n * S :=
          mul_le_mul_of_nonneg_left hdS (le_of_lt hn0)
        change n * d ≤ (n - 1) * (S - I)
        nlinarith only [hprod, htrace]
      have hquad : 0 ≤ n ^ 2 - 17 * n + 80 := by
        nlinarith only [sq_nonneg (n - (17 / 2 : ℝ))]
      have hquadD : 0 ≤ (n ^ 2 - 17 * n + 80) * d := mul_nonneg hquad hd
      have hmass : 0 ≤ (n - 1) * (2 * m - n * d) :=
        mul_nonneg (le_of_lt (sub_pos.mpr hn1)) (sub_nonneg.mpr hdm)
      have hlower : d ≤ (1 / 40 : ℝ) * m + (4 / 5 : ℝ) * t := by
        by_contra hh
        have hh' : (1 / 40 : ℝ) * m + (4 / 5 : ℝ) * t < d :=
          lt_of_not_ge hh
        have hbad : (n - 1) * ((1 / 40 : ℝ) * m + (4 / 5 : ℝ) * t - d) < 0 :=
          mul_neg_of_pos_of_neg (sub_pos.mpr hn1) (sub_neg.mpr hh')
        nlinarith only [hspread, hmass, hquadD, hbad]
      have hcoef : (1 / 40 : ℝ) * m ≤
          (13888888888888583 / 500000000000000000 : ℝ) * m :=
        mul_le_mul_of_nonneg_right (by norm_num) hm0
      exact hlower.trans (add_le_add hcoef le_rfl)
