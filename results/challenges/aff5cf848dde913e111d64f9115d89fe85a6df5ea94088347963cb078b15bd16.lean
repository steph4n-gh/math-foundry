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

theorem hull3d_algebraic_connectivity_le_0_1_min_degree_laplacian_spectral_radius_0_2a2b3957145e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn0 : Fintype.card V = 0
  · have hn : ¬ 2 ≤ Fintype.card V := by omega
    simp [hn0, hn]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
    rw [if_neg hn0]
    let H := G.isHermitian_lapMatrix ℝ
    have hbdd : BddAbove (Set.range H.eigenvalues) :=
      (Set.finite_range H.eigenvalues).bddAbove
    have hzero : (0 : ℝ) ∈ Set.range H.eigenvalues := by
      rw [← H.spectrum_real_eq_range_eigenvalues]
      exact G.zero_mem_spectrum_lapMatrix ℝ
    have hnonneg : (0 : ℝ) ≤ sSup (Set.range H.eigenvalues) :=
      le_csSup hbdd hzero
    by_cases hc : G.Connected
    · simp only [if_pos hc]
      by_cases hn : 2 ≤ Fintype.card V
      · simp only [dif_pos hn]
        let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
        let e : Fin (Fintype.card V) ≃ V :=
          Fintype.equivOfCardEq (Fintype.card_fin _)
        have he : H.eigenvalues (e j) = H.eigenvalues₀ j := by
          change H.eigenvalues₀ (e.symm (e j)) = H.eigenvalues₀ j
          rw [e.symm_apply_apply]
        change H.eigenvalues₀ j ≤ sSup (Set.range H.eigenvalues)
        rw [← he]
        exact le_csSup hbdd ⟨e j, rfl⟩
      · simp only [dif_neg hn]
        exact hnonneg
    · simp only [if_neg hc]
      exact hnonneg

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

theorem hull3d_order_ge_1_0_laplacian_spectral_radius_signless_laplacian_spectral_radius_0_is_connected_88f94a53c8e1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Fintype.card V : ℝ) ≥ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · rw [if_neg hn]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    let u : EuclideanSpace ℝ V := (G.isHermitian_lapMatrix ℝ).eigenvectorBasis i
    let x : V → ℝ := ⇑u
    have hu : ‖u‖ = 1 :=
      (G.isHermitian_lapMatrix ℝ).eigenvectorBasis.orthonormal.1 i
    have hnorm : (∑ v : V, (x v) ^ 2) = 1 := by
      have hh := EuclideanSpace.real_norm_sq_eq u
      rw [hu, one_pow] at hh
      exact hh.symm
    have heig : (G.isHermitian_lapMatrix ℝ).eigenvalues i =
        Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x := by
      simpa only [Matrix.toLinearMap₂'_apply', star_trivial, RCLike.re_to_real]
        using (G.isHermitian_lapMatrix ℝ).eigenvalues_eq i
    have hsumle :
        (∑ v : V, ∑ w : V, if G.Adj v w then (x v - x w) ^ 2 else 0) ≤
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      by_cases hadj : G.Adj v w
      · simp only [if_pos hadj, le_refl]
      · simpa only [if_neg hadj] using sq_nonneg (x v - x w)
    have hsum :
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) =
        2 * ((Fintype.card V : ℝ) * (∑ v : V, (x v) ^ 2) -
          (∑ v : V, x v) ^ 2) := by
      have hrow (v : V) :
          (∑ w : V, (x v - x w) ^ 2) =
          (Fintype.card V : ℝ) * (x v) ^ 2 -
            2 * x v * (∑ w : V, x w) + (∑ w : V, (x w) ^ 2) := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [hrow]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum, hnorm] at hsumle
    rw [heig, G.lapMatrix_toLinearMap₂' ℝ x]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [hsumle, sq_nonneg (∑ v : V, x v)]
theorem model_8381b1d261739251d279 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((2 : ℝ) * (((((Fintype.card V : ℝ) - (1 : ℝ)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues))) - ((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) * (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))) ≥ (((2 : ℝ) * (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * (((Fintype.card V : ℝ) - (1 : ℝ)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))))) + (((Fintype.card V : ℝ) - (1 : ℝ)) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2))) := by
  sorry
