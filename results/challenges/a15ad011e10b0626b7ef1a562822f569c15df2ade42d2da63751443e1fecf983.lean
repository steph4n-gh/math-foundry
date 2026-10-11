import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

theorem estrada_ge_energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  classical
  have hsum : (∑ v : V, (G.isHermitian_adjMatrix ℝ).eigenvalues v) = 0 := by
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have hpoint (x : ℝ) : |x| + x ≤ Real.exp x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hexp := Real.quadratic_le_exp_of_nonneg hx
      nlinarith [sq_nonneg (x - 1)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have hbound :
      (∑ v : V, (|(G.isHermitian_adjMatrix ℝ).eigenvalues v| +
        (G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≤
      ∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v) := by
    exact Finset.sum_le_sum (fun v _ => hpoint _)
  simpa only [Finset.sum_add_distrib, hsum, add_zero] using hbound

theorem graph_energy_spectral_radius_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  have hsum : (∑ v : V, f v) = 0 := by
    simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hnonneg (w : V) : 0 ≤ |f w| + f w := by
      linarith [neg_abs_le (f w)]
    have hsingle : |f v| + f v ≤ ∑ w : V, (|f w| + f w) :=
      Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
    simp only [Finset.sum_add_distrib, hsum, add_zero] at hsingle
    change 2 * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) ≤
      ∑ w : V, |f w|
    rw [if_neg hV, ← hv]
    linarith [le_abs_self (f v)]

theorem hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.minDegree : ℝ) ≤ ((1 / 2 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    have hmem : (d : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) :=
      SimpleGraph.IsRegularOfDegree.mem_spectrum_adjMatrix (R := ℝ) (G := G) hd
    rw [(G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hmem
    have hdle : (d : ℝ) ≤
        sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) :=
      le_csSup (Set.finite_range (G.isHermitian_adjMatrix ℝ).eigenvalues).bddAbove hmem
    have henergy := graph_energy_spectral_radius_lower G
    rw [if_neg hV] at henergy
    rw [SimpleGraph.IsRegularOfDegree.minDegree_eq (G := G) hd]
    linarith

theorem hull3d_graph_energy_ge_2_0_average_degree_size_0_is_regular_479d55ae89c3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
      simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
    have hsum : (Fintype.card V : ℝ) * (d : ℝ) =
        2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hsum_nat
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast hV
    have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        (Fintype.card V : ℝ) = (d : ℝ) := by
      apply (div_eq_iff hcard).2
      exact hsum.symm.trans (mul_comm _ _)
    have henergy :=
      hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939
        G ⟨d, hd⟩
    rw [hd.minDegree_eq] at henergy
    rw [if_neg hV, havg]
    linarith

theorem hull3d_graph_energy_le_0_2_average_degree_size_0_is_regular_99710b2e7422 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨d, hd⟩ := h_guard
  have hbound (i : V) : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (d : ℝ) := by
    let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    obtain ⟨w, _, hw⟩ := Finset.exists_max_image Finset.univ (fun v => |x v|)
      ⟨j, Finset.mem_univ j⟩
    have hwpos : 0 < |x w| :=
      lt_of_lt_of_le (abs_pos.mpr hj) (hw j (Finset.mem_univ j))
    have heq : (∑ u ∈ G.neighborFinset w, x u) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i * x w := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) w
    have hmul : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| ≤
        (d : ℝ) * |x w| := by
      calc
        |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| =
            |∑ u ∈ G.neighborFinset w, x u| := by rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset w, |x u| :=
          Finset.abs_sum_le_sum_abs x (G.neighborFinset w)
        _ ≤ ∑ u ∈ G.neighborFinset w, |x w| :=
          Finset.sum_le_sum (fun u _ => hw u (Finset.mem_univ u))
        _ = (d : ℝ) * |x w| := by
          simp only [Finset.sum_const, G.card_neighborFinset_eq_degree,
            hd.degree_eq, nsmul_eq_mul]
    exact (mul_le_mul_iff_left₀ hwpos).mp hmul
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤
        ∑ _v : V, (d : ℝ) :=
      Finset.sum_le_sum (fun v _ => hbound v)
    _ = ∑ v : V, (G.degree v : ℝ) := by simp only [hd.degree_eq]
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith
theorem koolen_moulton_order_2003 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((Fintype.card V : ℝ) / (2 : ℝ)) * ((1 : ℝ) + (Real.sqrt (Fintype.card V : ℝ)))) := by
  sorry
