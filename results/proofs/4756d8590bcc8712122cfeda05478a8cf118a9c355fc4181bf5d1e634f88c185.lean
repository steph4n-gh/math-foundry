import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h

theorem hull3d_size_ge_1_0_max_degree_normalized_laplacian_spectral_gap_0_is_connected_9b83028c151a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ (G.maxDegree : ℝ) := by
  classical
  have hn : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le G.edgeFinset.card
      (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast hn

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

theorem hull_density_le_1_max_degree_0_f5fbcb14104c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) ≤ (G.maxDegree : ℝ) := by
  classical
  by_cases hn : Fintype.card V < 2
  · rw [if_pos hn]
    exact Nat.cast_nonneg _
  · rw [if_neg hn]
    have hn2nat : 2 ≤ Fintype.card V := by omega
    have hn2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hn2nat
    have hsum : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
      calc
        2 * G.edgeFinset.card = Finset.univ.sum (fun v : V => G.degree v) :=
          G.sum_degrees_eq_twice_card_edges.symm
        _ ≤ Finset.univ.sum (fun _ : V => G.maxDegree) :=
          Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
        _ = Fintype.card V * G.maxDegree := by simp
    have hsumR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hsum
    have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hmpos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by linarith
    have hmone : (1 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by linarith
    apply (div_le_iff₀ (mul_pos hnpos hmpos)).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
          (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
      _ ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) *
          ((Fintype.card V : ℝ) - 1) :=
        le_mul_of_one_le_right (by positivity) hmone
      _ = (G.maxDegree : ℝ) *
          ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring
theorem hull3d_max_degree_le__0_5_1_graph_energy_size_1_is_regular_27c4eb6febfd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ (((G.edgeFinset.card : ℝ) - ((1 / 2 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|))) + (1 : ℝ)) := by
  classical
  rcases isEmpty_or_nonempty V with hempty | hnonempty
  · letI : IsEmpty V := hempty
    simp only [SimpleGraph.maxDegree_of_subsingleton, Nat.cast_zero,
      Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero]
    positivity
  · letI : Nonempty V := hnonempty
    obtain ⟨d, hd⟩ := h_guard
    have hmax : G.maxDegree = d := hd.maxDegree_eq
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let eig : V → ℝ := hA.eigenvalues
    have hspectral : A = Unitary.conjStarAlgAut ℝ (Matrix V V ℝ)
        hA.eigenvectorUnitary (Matrix.diagonal eig) := by
      simpa [eig] using hA.spectral_theorem
    have htrace : Matrix.trace (A * A) =
        Matrix.trace (Matrix.diagonal eig * Matrix.diagonal eig) := by
      calc
        Matrix.trace (A * A) = Matrix.trace
            (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
              (Matrix.diagonal eig * Matrix.diagonal eig)) := by
          simp only [map_mul, ← hspectral]
        _ = Matrix.trace (Matrix.diagonal eig * Matrix.diagonal eig) := by
          rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, Matrix.one_mul]
    have hsq : (∑ v : V, eig v ^ 2) =
        (Fintype.card V : ℝ) * (d : ℝ) := by
      calc
        (∑ v : V, eig v ^ 2) =
            Matrix.trace (Matrix.diagonal eig * Matrix.diagonal eig) := by
          simp [pow_two]
        _ = Matrix.trace (A * A) := htrace.symm
        _ = (Fintype.card V : ℝ) * (d : ℝ) := by
          simp [A, Matrix.trace, G.adjMatrix_mul_self_apply_self, hd.degree_eq]
    have hsum : (Fintype.card V : ℝ) * (d : ℝ) =
        2 * (G.edgeFinset.card : ℝ) := by
      have hn : Fintype.card V * d = 2 * G.edgeFinset.card := by
        simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
      exact_mod_cast hn
    change (G.maxDegree : ℝ) ≤
      (G.edgeFinset.card : ℝ) - (1 / 2 : ℝ) * (∑ v : V, |eig v|) + 1
    by_cases hd0 : d = 0
    · have hsq0 : (∑ v : V, eig v ^ 2) = 0 := by
        simpa [hd0] using hsq
      have hzero (v : V) : eig v = 0 := by
        have hv : eig v ^ 2 ≤ 0 := by
          calc
            eig v ^ 2 ≤ ∑ w : V, eig w ^ 2 :=
              Finset.single_le_sum (fun w _ => sq_nonneg (eig w))
                (Finset.mem_univ v)
            _ = 0 := hsq0
        exact sq_eq_zero_iff.mp (le_antisymm hv (sq_nonneg (eig v)))
      have he : (∑ v : V, |eig v|) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [hzero v, abs_zero]
      rw [hmax, hd0, he]
      simp only [Nat.cast_zero, mul_zero, sub_zero]
      exact add_nonneg (Nat.cast_nonneg G.edgeFinset.card) (zero_le_one : (0 : ℝ) ≤ 1)
    · have hvec : Module.End.HasEigenvector A.toLin' (d : ℝ)
          (Function.const V (1 : ℝ)) := by
        refine Module.End.hasEigenvector_iff.mpr ⟨?_, ?_⟩
        · apply Module.End.mem_eigenspace_iff.mpr
          ext v
          change Matrix.mulVec (G.adjMatrix ℝ)
            (Function.const V (1 : ℝ)) v = (d : ℝ) * 1
          exact SimpleGraph.adjMatrix_mulVec_const_apply_of_regular
            (G := G) (α := ℝ) hd
        · intro hz
          have hzv := congrFun hz (Classical.arbitrary V)
          norm_num [Function.const] at hzv
      have hmem : (d : ℝ) ∈ spectrum ℝ A := by
        rw [← Matrix.spectrum_toLin']
        exact (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
      rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
      obtain ⟨i, hi⟩ : ∃ i : V, eig i = (d : ℝ) := hmem
      have habs (x : ℝ) : 2 * |x| ≤ x ^ 2 + 1 := by
        nlinarith only [sq_nonneg (|x| - 1), sq_abs x]
      have hrest :
          (∑ v ∈ (Finset.univ : Finset V).erase i, 2 * |eig v|) ≤
          (∑ v ∈ (Finset.univ : Finset V).erase i, (eig v ^ 2 + 1)) :=
        Finset.sum_le_sum (fun v _ => habs (eig v))
      have hsplitL :
          (∑ v ∈ (Finset.univ : Finset V).erase i, 2 * |eig v|) +
            2 * (d : ℝ) = 2 * (∑ v : V, |eig v|) := by
        calc
          (∑ v ∈ (Finset.univ : Finset V).erase i, 2 * |eig v|) +
              2 * (d : ℝ) = ∑ v : V, 2 * |eig v| := by
            simpa only [hi, abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
              using Finset.sum_erase_add (Finset.univ : Finset V)
                (fun v => 2 * |eig v|) (Finset.mem_univ i)
          _ = 2 * (∑ v : V, |eig v|) := by rw [Finset.mul_sum]
      have hsplitR :
          (∑ v ∈ (Finset.univ : Finset V).erase i, (eig v ^ 2 + 1)) +
            ((d : ℝ) ^ 2 + 1) =
            (Fintype.card V : ℝ) * (d : ℝ) + (Fintype.card V : ℝ) := by
        calc
          (∑ v ∈ (Finset.univ : Finset V).erase i, (eig v ^ 2 + 1)) +
              ((d : ℝ) ^ 2 + 1) = ∑ v : V, (eig v ^ 2 + 1) := by
            simpa only [hi] using Finset.sum_erase_add (Finset.univ : Finset V)
              (fun v => eig v ^ 2 + 1) (Finset.mem_univ i)
          _ = (Fintype.card V : ℝ) * (d : ℝ) + (Fintype.card V : ℝ) := by
            rw [Finset.sum_add_distrib, hsq]
            simp
      have hdlt : d < Fintype.card V := by
        simpa only [hd.degree_eq] using G.degree_lt_card_verts i
      have hfac : 0 ≤ ((d : ℝ) - 1) *
          ((Fintype.card V : ℝ) + (d : ℝ) - 5) := by
        by_cases hd1 : d = 1
        · simp [hd1]
        · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast (show 2 ≤ d by omega)
          have hn : (d : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
            exact_mod_cast (show d + 1 ≤ Fintype.card V by omega)
          exact mul_nonneg (by linarith) (by linarith)
      rw [hmax]
      nlinarith only [hrest, hsplitL, hsplitR, hfac, hsum]
