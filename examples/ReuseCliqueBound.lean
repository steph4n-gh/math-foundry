-- Apache-2.0. Standalone reuse example; the archived source below is unchanged.
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic




theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)
theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))


-- A consumer theorem: reuse the checked bound under a separate namespace.
namespace MathFoundryExamples

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact archetype_chi_ge_omega G

end MathFoundryExamples

#print axioms MathFoundryExamples.clique_bound
