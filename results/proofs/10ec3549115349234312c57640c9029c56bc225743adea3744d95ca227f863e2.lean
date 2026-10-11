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

theorem signless_laplacian_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    let hQ := (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    let f : V → ℝ := hQ.eigenvalues
    have htrace : (∑ v : V, f v) = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      change (∑ v : V, hQ.eigenvalues v) = (2 : ℝ) * (G.edgeFinset.card : ℝ)
      have htrace_eq : Matrix.trace (G.degMatrix ℝ + G.adjMatrix ℝ) =
          ∑ v : V, hQ.eigenvalues v := by
        simpa using hQ.trace_eq_sum_eigenvalues
      rw [← htrace_eq]
      simp only [Matrix.trace_add, SimpleGraph.trace_adjMatrix, add_zero,
        SimpleGraph.degMatrix, Matrix.trace_diagonal]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : (∑ v : V, f v) ≤
        (Fintype.card V : ℝ) * sSup (Set.range f) := by
      calc
        (∑ v : V, f v) ≤ ∑ _ : V, sSup (Set.range f) :=
          Finset.sum_le_sum (fun v _ =>
            le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v))
        _ = (Fintype.card V : ℝ) * sSup (Set.range f) := by simp
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    change (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤
      sSup (Set.range f)
    apply (div_le_iff₀ hpos).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) = ∑ v : V, f v := htrace.symm
      _ ≤ (Fintype.card V : ℝ) * sSup (Set.range f) := hbound
      _ = sSup (Set.range f) * (Fintype.card V : ℝ) := mul_comm _ _

theorem composed_f0d095cf27d0fbe6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.minDegree : ℝ) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) := by
  have hmin := hull_min_degree_le_1_average_degree_0_36a8fb326490 G
  exact hmin.trans (signless_laplacian_avg_deg_lower G)

theorem hull3d_max_degree_ge_0_1_diameter_min_degree_0_is_bipartite_4065a324009b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≥ (G.minDegree : ℝ) := by
  simp

theorem hull3d_max_degree_ge_1_0_min_degree_girth_0_is_regular_9277ab7750da {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≥ (G.minDegree : ℝ) := by
  simp

theorem hull3d_max_degree_le_1_0_min_degree_girth_0_is_regular_a8cd4d70ab45 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ (G.minDegree : ℝ) := by
  classical
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨d, hd⟩ := h_guard
    rw [SimpleGraph.IsRegularOfDegree.maxDegree_eq (G := G) hd,
      SimpleGraph.IsRegularOfDegree.minDegree_eq (G := G) hd]

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
theorem hull3d_min_degree_le_0_0_5_nordhaus_gaddum_spectral_product_nordhaus_gaddum_spectral_sum_0_5_is_bipartite_fe51971bfc87 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.minDegree : ℝ) ≤ (((1 / 2 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)))) + (1 / 2 : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    norm_num [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    have hquadratic (A : Matrix V V ℝ) (hA : A.IsHermitian)
        (x : EuclideanSpace ℝ V) :
        inner ℝ x (A.toEuclideanLin x) ≤
          sSup (Set.range hA.eigenvalues) * ‖x‖ ^ 2 := by
      let b := hA.eigenvectorBasis
      have heig (v : V) :
          A.toEuclideanLin (b v) = hA.eigenvalues v • b v := by
        apply WithLp.ofLp_injective 2
        simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
          WithLp.ofLp_smul] using hA.mulVec_eigenvectorBasis v
      have hcoord (v : V) :
          inner ℝ (b v) (A.toEuclideanLin x) =
            hA.eigenvalues v * inner ℝ (b v) x := by
        rw [← (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (b v) x,
          heig v, real_inner_smul_left]
      calc
        inner ℝ x (A.toEuclideanLin x) =
            ∑ v : V, inner ℝ x (b v) *
              inner ℝ (b v) (A.toEuclideanLin x) :=
          (b.sum_inner_mul_inner x (A.toEuclideanLin x)).symm
        _ = ∑ v : V, hA.eigenvalues v * (inner ℝ (b v) x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro v _
          rw [hcoord v, real_inner_comm (b v) x]
          ring
        _ ≤ ∑ v : V, sSup (Set.range hA.eigenvalues) *
            (inner ℝ (b v) x) ^ 2 := by
          apply Finset.sum_le_sum
          intro v _
          exact mul_le_mul_of_nonneg_right
            (le_csSup (Set.finite_range hA.eigenvalues).bddAbove
              (Set.mem_range_self v)) (sq_nonneg _)
        _ = sSup (Set.range hA.eigenvalues) * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, b.sum_sq_inner_right x]
    have hbound (H : SimpleGraph V) [DecidableRel H.Adj] :
        (∑ v : V, (H.degree v : ℝ)) ≤
          sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) *
            (Fintype.card V : ℝ) := by
      let x : EuclideanSpace ℝ V :=
        WithLp.toLp 2 (fun _ : V => (1 : ℝ))
      have hn : ‖x‖ ^ 2 = (Fintype.card V : ℝ) := by
        simp [EuclideanSpace.real_norm_sq_eq, x, PiLp.toLp_apply]
      have hi : inner ℝ x ((H.adjMatrix ℝ).toEuclideanLin x) =
          ∑ v : V, (H.degree v : ℝ) := by
        simp [Matrix.toLpLin_apply, PiLp.inner_apply, x,
          PiLp.toLp_apply, WithLp.ofLp_toLp]
      simpa only [hi, hn] using
        hquadratic (H.adjMatrix ℝ) (H.isHermitian_adjMatrix ℝ) x
    have hdeg (v : V) :
        (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) =
          (Fintype.card V : ℝ) - 1 := by
      have hnat : G.degree v + Gᶜ.degree v + 1 = Fintype.card V := by
        rw [G.degree_compl v]
        have hv := G.degree_lt_card_verts v
        omega
      have hr : (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) + 1 =
          (Fintype.card V : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hsum :
        (∑ v : V, (G.degree v : ℝ)) +
          (∑ v : V, (Gᶜ.degree v : ℝ)) =
            (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hdeg]
      simp
      ring
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    have hNG : (Fintype.card V : ℝ) - 1 ≤
        sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) +
          sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) := by
      have hscaled :
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) ≤
            (Fintype.card V : ℝ) *
              (sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) +
                sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)) := by
        calc
          (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) =
              (∑ v : V, (G.degree v : ℝ)) +
                (∑ v : V, (Gᶜ.degree v : ℝ)) := hsum.symm
          _ ≤ sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) *
                (Fintype.card V : ℝ) +
              sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) *
                (Fintype.card V : ℝ) :=
            add_le_add (hbound G) (hbound Gᶜ)
          _ = _ := by ring
      exact le_of_mul_le_mul_left hscaled hpos
    have hdelta_nat : 2 * G.minDegree ≤ Fintype.card V := by
      by_cases hd : G.minDegree = 0
      · simp [hd]
      · obtain ⟨u⟩ := ‹Nonempty V›
        obtain ⟨w, huw⟩ := (G.degree_pos_iff_exists_adj u).mp
          ((Nat.pos_of_ne_zero hd).trans_le (G.minDegree_le_degree u))
        obtain ⟨c⟩ := h_guard
        have hcolors : ∀ a b c : Fin 2,
            a ≠ b → a ≠ c → b ≠ c → False := by decide
        have hdisjoint : Disjoint (G.neighborFinset u) (G.neighborFinset w) := by
          apply Finset.disjoint_left.mpr
          intro z hzu hzw
          exact hcolors (c u) (c w) (c z) (c.valid huw)
            (c.valid (by simpa only [SimpleGraph.mem_neighborFinset] using hzu))
            (c.valid (by simpa only [SimpleGraph.mem_neighborFinset] using hzw))
        have hcard := (G.neighborFinset u ∪ G.neighborFinset w).card_le_univ
        rw [Finset.card_union_of_disjoint hdisjoint,
          G.card_neighborFinset_eq_degree u,
          G.card_neighborFinset_eq_degree w] at hcard
        have hu := G.minDegree_le_degree u
        have hw := G.minDegree_le_degree w
        omega
    have hdelta : (2 : ℝ) * (G.minDegree : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hdelta_nat
    linarith
