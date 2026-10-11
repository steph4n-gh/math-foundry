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

theorem hull3d_average_degree_le_0_5_0_graph_energy_diameter_0_is_regular_634736df2435 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ ((1 / 2 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) := by
  have checked_0 := hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939 G h_guard; have checked_1 := hull3d_graph_energy_ge_2_0_average_degree_size_0_is_regular_479d55ae89c3 G h_guard; have checked_2 := estrada_ge_energy G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem hull3d_signless_laplacian_spectral_radius_ge_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_26c733c31f3e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    rw [if_neg hV, hd.maxDegree_eq]
    have hspec : (2 : ℝ) * (d : ℝ) ∈
        spectrum ℝ (G.degMatrix ℝ + G.adjMatrix ℝ) := by
      rw [hd.degMatrix_eq (R := ℝ)]
      simpa only [map_natCast, two_mul] using
        (spectrum.add_mem_add_iff (a := G.adjMatrix ℝ)
          (r := (d : ℝ)) (s := (d : ℝ))).2
          (hd.mem_spectrum_adjMatrix (R := ℝ))
    rw [((G.isHermitian_degMatrix ℝ).add
      (G.isHermitian_adjMatrix ℝ)).spectrum_real_eq_range_eigenvalues] at hspec
    exact le_csSup (Set.finite_range _).bddAbove hspec

theorem hull3d_order_ge__1_2_density_average_degree_1_is_tree_39f653f393cf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (Fintype.card V : ℝ) ≥ ((((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))) + (1 : ℝ)) := by
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := h_guard.card_edgeFinset
  rcases (show Fintype.card V = 1 ∨ Fintype.card V = 2 ∨ 3 ≤ Fintype.card V by omega) with h | h | h
  · have he : G.edgeFinset.card = 0 := by omega
    norm_num [h, he]
  · have he : G.edgeFinset.card = 1 := by omega
    norm_num [h, he]
  · have hn : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h
    have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
    have hz : Fintype.card V ≠ 0 := by omega
    have ht : ¬ Fintype.card V < 2 := by omega
    have he : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have he' : (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
      linarith
    simp only [if_neg hz, if_neg ht]
    rw [he']
    have hf :
        2 * (2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) -
          2 * ((Fintype.card V : ℝ) - 1) /
            ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) + 1 =
        (5 * (Fintype.card V : ℝ) - 6) / (Fintype.card V : ℝ) := by
      field_simp [ne_of_gt hn0, hn1] <;> ring
    rw [hf]
    apply (div_le_iff₀ hn0).2
    have hprod :
        0 ≤ ((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]

theorem hull3d_order_ge__3_3_density_average_degree_1_is_tree_f65c2da0bfec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (Fintype.card V : ℝ) ≥ ((((3 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - ((3 : ℝ) * (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))))) + (1 : ℝ)) := by
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := h_guard.card_edgeFinset
  rcases (show Fintype.card V = 1 ∨ Fintype.card V = 2 ∨ Fintype.card V = 3 ∨ 4 ≤ Fintype.card V by omega) with h | h | h | h
  · have he : G.edgeFinset.card = 0 := by omega
    norm_num [h, he]
  · have he : G.edgeFinset.card = 1 := by omega
    norm_num [h, he]
  · have he : G.edgeFinset.card = 2 := by omega
    norm_num [h, he]
  · have hn : (4 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h
    have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
    have hz : Fintype.card V ≠ 0 := by omega
    have ht : ¬ Fintype.card V < 2 := by omega
    have he : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have he' : (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
      linarith
    simp only [if_neg hz, if_neg ht]
    rw [he']
    have hf :
        3 * (2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) -
          3 * (2 * ((Fintype.card V : ℝ) - 1) /
            ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) + 1 =
        (7 * (Fintype.card V : ℝ) - 12) / (Fintype.card V : ℝ) := by
      field_simp [ne_of_gt hn0, hn1] <;> ring
    rw [hf]
    apply (div_le_iff₀ hn0).2
    have hprod :
        0 ≤ ((Fintype.card V : ℝ) - 3) * ((Fintype.card V : ℝ) - 4) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
theorem signless_laplacian_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  sorry
