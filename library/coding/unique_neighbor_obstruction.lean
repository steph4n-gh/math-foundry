import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

open scoped BigOperators

theorem unique_neighbor_obstructs_parity_code
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ZMod 2)
    (hcode : ∀ v, ∑ u ∈ G.neighborFinset v, x u = 0)
    (v w : V) (hw : x w ≠ 0) (hvw : G.Adj v w)
    (hunique : ∀ u, x u ≠ 0 → G.Adj v u → u = w) : False := by
  have heq : ∑ u ∈ G.neighborFinset v, x u = x w := by
    apply Finset.sum_eq_single w
    · intro u hu hne
      by_contra hxu
      exact hne (hunique u hxu ((G.mem_neighborFinset v u).mp hu))
    · intro hnot
      exact (hnot ((G.mem_neighborFinset v w).mpr hvw)).elim
  exact hw (heq.symm.trans (hcode v))
