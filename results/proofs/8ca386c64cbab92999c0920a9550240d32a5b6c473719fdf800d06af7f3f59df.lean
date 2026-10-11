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

theorem hull3d_min_degree_le_0_0310263_0_1_parity_code_distance_size_6_5_is_connected_8f22405c2232 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.minDegree : ℝ) ≤ ((((6205250596658711 / 200000000000000000 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) + ((1 / 10 : ℝ) * (G.edgeFinset.card : ℝ))) + (13 / 2 : ℝ)) := by
  classical
  letI : Nonempty V := h_guard.nonempty
  have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
    calc
      Fintype.card V * G.minDegree = ∑ _ : V, G.minDegree := by simp
      _ ≤ ∑ v : V, G.degree v :=
        Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hdn : G.minDegree + 1 ≤ Fintype.card V :=
    Nat.succ_le_of_lt G.minDegree_lt_card
  have hdmNat : G.minDegree * (G.minDegree + 1) ≤ 2 * G.edgeFinset.card := by
    calc
      G.minDegree * (G.minDegree + 1) = (G.minDegree + 1) * G.minDegree :=
        Nat.mul_comm _ _
      _ ≤ Fintype.card V * G.minDegree := Nat.mul_le_mul_right _ hdn
      _ ≤ 2 * G.edgeFinset.card := hsum
  have hdm : (G.minDegree : ℝ) * ((G.minDegree : ℝ) + 1) ≤
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hdmNat
  have hbase : (G.minDegree : ℝ) ≤
      (1 / 10 : ℝ) * (G.edgeFinset.card : ℝ) + (13 / 2 : ℝ) := by
    nlinarith only [hdm, sq_nonneg ((G.minDegree : ℝ) - (19 / 2 : ℝ))]
  apply hbase.trans
  apply add_le_add
  · exact le_add_of_nonneg_left
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · exact le_rfl
