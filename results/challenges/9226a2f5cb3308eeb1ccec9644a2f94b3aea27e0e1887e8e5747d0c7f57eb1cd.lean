import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

theorem clique_edges_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hdv : ∀ v ∈ s, (G.cliqueNum : ℝ) - 1 ≤ (G.degree v : ℝ) := by
    intro v hv
    have hsubset : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [G.mem_neighborFinset]
      exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
    have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
    have hn : G.cliqueNum ≤ G.degree v + 1 := by omega
    have hr : (G.cliqueNum : ℝ) ≤ (G.degree v : ℝ) + 1 := by exact_mod_cast hn
    linarith
  calc
    (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) = ∑ v ∈ s, ((G.cliqueNum : ℝ) - 1) := by
      simp [hs.card_eq]
      ring
    _ ≤ ∑ v ∈ s, (G.degree v : ℝ) := Finset.sum_le_sum hdv
    _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ s) (fun v _ _ => Nat.cast_nonneg _)
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem model_e679ce9c7fa60e2c7bfd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) * ((G.chromaticNumber.toNat : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
    let n := G.chromaticNumber.toNat
    obtain ⟨c⟩ := G.colorable_chromaticNumber_of_fintype
    let H : SimpleGraph (Fin n) := G.map c
    have hn : (n : ℕ∞) ≤ H.chromaticNumber :=
      (ENat.natCast_toNat_le_self G.chromaticNumber).trans
        (SimpleGraph.chromaticNumber_mono_of_hom c.homMap)
    have hH : H = ⊤ := by
      apply SimpleGraph.eq_top_of_chromaticNumber_eq_card
      apply le_antisymm H.chromaticNumber_le_card
      simpa only [Fintype.card_fin] using hn
    have hsurj : Function.Surjective c.homMap.mapDart := by
      intro d
      obtain ⟨_, u, v, huv, hu, hv⟩ :=
        (SimpleGraph.map_adj' c G d.fst d.snd).mp d.adj
      refine ⟨⟨(u, v), huv⟩, ?_⟩
      apply SimpleGraph.Dart.ext
      exact Prod.ext hu hv
    have hcard : Fintype.card H.Dart ≤ Fintype.card G.Dart :=
      Fintype.card_le_of_surjective c.homMap.mapDart hsurj
    rw [H.dart_card_eq_twice_card_edges,
      G.dart_card_eq_twice_card_edges] at hcard
    have hreal : (2 : ℝ) * (H.edgeFinset.card : ℝ) ≤
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hcard
    have hclique : H.cliqueNum = n := by
      rw [hH, SimpleGraph.cliqueNum_top, Nat.card_fin]
    have hbound := clique_edges_density_bound H
    rw [hclique] at hbound
    exact hbound.trans hreal

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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h
theorem model_c0b68b8f55a47e0a3735 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) := by
  sorry
