import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic




open scoped BigOperators
theorem hull3d_max_degree_ge_0_1_order_density_0_is_regular_3887d517131d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≥ (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) := by
  classical
  by_cases hsmall : Fintype.card V < 2
  · rw [if_pos hsmall]
    exact Nat.cast_nonneg _
  · rw [if_neg hsmall]
    have hn : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.not_lt.mp hsmall)
    have hsum : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
      calc
        2 * G.edgeFinset.card =
            Finset.sum Finset.univ (fun v : V => G.degree v) :=
          G.sum_degrees_eq_twice_card_edges.symm
        _ ≤ Finset.sum Finset.univ (fun _ : V => G.maxDegree) :=
          Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
        _ = Fintype.card V * G.maxDegree := by simp
    have hsumR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hsum
    have hden : 0 < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    apply (div_le_iff₀ hden).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
          (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
      _ ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) *
          ((Fintype.card V : ℝ) - 1) :=
        le_mul_of_one_le_right
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (by linarith)
      _ = (G.maxDegree : ℝ) *
          ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring

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

theorem hull3d_max_degree_le_1__1_order_density_0_is_regular_f85632d19957 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ ((Fintype.card V : ℝ) - (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))) := by
  classical
  have hmax : G.maxDegree ≤ Fintype.card V - 1 := by
    apply G.maxDegree_le_of_forall_degree_le
    intro v
    have hv := G.degree_lt_card_verts v
    omega
  by_cases hsmall : Fintype.card V < 2
  · rw [if_pos hsmall, sub_zero]
    exact_mod_cast (hmax.trans (Nat.sub_le (Fintype.card V) 1))
  · rw [if_neg hsmall]
    have hn : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.not_lt.mp hsmall)
    have hmaxR : (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (show G.maxDegree + 1 ≤ Fintype.card V from by omega)
    have hsum : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
      calc
        2 * G.edgeFinset.card =
            Finset.sum Finset.univ (fun v : V => G.degree v) :=
          G.sum_degrees_eq_twice_card_edges.symm
        _ ≤ Finset.sum Finset.univ (fun _ : V => G.maxDegree) :=
          Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
        _ = Fintype.card V * G.maxDegree := by simp
    have hsumR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hsum
    have hden : 0 < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have hdensity : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      calc
        (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
            (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
        _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = 1 * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring
    linarith
theorem hull3d_max_degree_ge_1_0_min_degree_girth_0_is_regular_9277ab7750da {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≥ (G.minDegree : ℝ) := by
  sorry
