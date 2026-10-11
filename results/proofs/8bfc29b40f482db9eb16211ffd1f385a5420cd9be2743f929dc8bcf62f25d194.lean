import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
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

theorem hull3d_size_ge_1_0_parity_code_distance_normalized_laplacian_spectral_gap__2_is_connected_97851a6e314b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) - (2 : ℝ)) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  have hd : weights.min' hw ≤ Fintype.card V + 1 := by
    apply Finset.min'_le weights (Fintype.card V + 1)
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr rfl))
  have hn : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
      h_guard.card_vert_le_card_edgeSet_add_one
  have hdR : (weights.min' hw : ℝ) ≤ (Fintype.card V : ℝ) + 1 := by
    exact_mod_cast hd
  have hnR : (Fintype.card V : ℝ) ≤ (G.edgeFinset.card : ℝ) + 1 := by
    exact_mod_cast hn
  change (G.edgeFinset.card : ℝ) ≥ (weights.min' hw : ℝ) - 2
  linarith only [hdR, hnR]
