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
theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem model_886a365b7173b119a27a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Gᶜ.cliqueNum : ℝ) + (G.edgeFinset.card : ℝ)) ≥ (Fintype.card V : ℝ) := by
  classical
  let T : Finset V := G.edgeFinset.image (fun e : Sym2 V => e.out.1)
  let S : Finset V := Finset.univ \ T
  have hT : T.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hS : Gᶜ.IsClique (S : Set V) := by
    intro u hu v hv hne
    change u ≠ v ∧ ¬ G.Adj u v
    refine ⟨hne, ?_⟩
    intro huv
    have he : s(u, v) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr huv)
    have hm : (s(u, v) : Sym2 V).out.1 ∈ T :=
      Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem (s(u, v))) with h | h
    · apply (Finset.mem_sdiff.mp hu).2
      exact h ▸ hm
    · apply (Finset.mem_sdiff.mp hv).2
      exact h ▸ hm
  have hclique : S.card ≤ Gᶜ.cliqueNum := hS.card_le_cliqueNum
  have hcards : S.card + T.card = Fintype.card V := by
    simpa only [S, Finset.card_univ] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T))
  have hnat : Fintype.card V ≤ Gᶜ.cliqueNum + G.edgeFinset.card := by
    omega
  exact_mod_cast hnat
theorem composed_523e52793bb52ffb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) + (G.edgeFinset.card : ℝ)) := by
  sorry
