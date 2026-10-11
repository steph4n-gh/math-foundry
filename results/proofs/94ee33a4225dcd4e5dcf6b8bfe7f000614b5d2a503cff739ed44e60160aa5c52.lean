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
theorem model_67bca380d677e1278e8a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.CliqueFree 3) ∧ ((Gᶜ.cliqueNum : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (Fintype.card V : ℝ) ≤ (5 : ℝ) := by
  classical
  have hcomp : Gᶜ.cliqueNum ≤ 2 := by
    have hlt : (Gᶜ.cliqueNum : ℝ) < (3 : ℝ) :=
      lt_of_le_of_lt h_guard.2 (by norm_num)
    have hnat : Gᶜ.cliqueNum < 3 := by exact_mod_cast hlt
    omega
  have hclique : G.cliqueNum ≤ 2 := by
    by_contra h
    have hthree : 3 ≤ G.cliqueNum := by omega
    obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    exact (SimpleGraph.CliqueFree.mono hthree h_guard.1) s hs
  have hcompfree : Gᶜ.CliqueFree 3 := by
    intro s hs
    have hle : s.card ≤ Gᶜ.cliqueNum := hs.isClique.card_le_cliqueNum
    have hcard : s.card = 3 := hs.card_eq
    omega
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have hd : G.degree v ≤ Gᶜ.cliqueNum := by
      have hc : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
        simpa only [SimpleGraph.coe_neighborFinset, SimpleGraph.isClique_compl] using
          G.isIndepSet_neighborSet_of_triangleFree h_guard.1 v
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        hc.card_le_cliqueNum
    have hdcomp : Gᶜ.degree v ≤ G.cliqueNum := by
      have hc : G.IsClique (Gᶜ.neighborFinset v : Set V) := by
        simpa only [SimpleGraph.coe_neighborFinset, SimpleGraph.isIndepSet_compl] using
          Gᶜ.isIndepSet_neighborSet_of_triangleFree hcompfree v
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
        hc.card_le_cliqueNum
    have hlt := G.degree_lt_card_verts v
    have heq := G.degree_compl v
    have hn : Fintype.card V ≤ 5 := by omega
    exact_mod_cast hn
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    simp
