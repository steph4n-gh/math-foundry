import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped BigOperators

theorem unique_neighbor_radius_nonnegative {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (0 : ℝ) ≤ (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) := by
  positivity
