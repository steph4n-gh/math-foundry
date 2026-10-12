-- SPDX-License-Identifier: Apache-2.0
-- Compile in a separate Lake project requiring the certifiedResearch package.
import MathFoundry

namespace FoundryConsumer

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact MathFoundry.archetype_chi_ge_omega G

-- A verified clique larger than k rules out every proper k-coloring.
theorem coloring_obstruction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hclique : k < G.cliqueNum) : ¬ G.Colorable k := by
  intro hcolor
  have hupper : G.chromaticNumber.toNat ≤ k :=
    ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  have hupperR : (G.chromaticNumber.toNat : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hupper
  have hstrict : (k : ℝ) < (G.cliqueNum : ℝ) := by
    exact_mod_cast hclique
  have hlower := MathFoundry.archetype_chi_ge_omega G
  linarith

-- Matching clique and greedy degree bounds certify the exact color count.
-- The historical "brooks_standard" name exports χ ≤ Δ + 1.
theorem chromatic_number_from_matching_bounds {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hclique : G.cliqueNum = k) (hdegree : G.maxDegree + 1 = k) :
    G.chromaticNumber.toNat = k := by
  have hlower := MathFoundry.archetype_chi_ge_omega G
  have hupper := MathFoundry.archetype_brooks_standard G
  rw [hclique] at hlower
  have hdegreeR : (G.maxDegree : ℝ) + 1 = (k : ℝ) := by
    exact_mod_cast hdegree
  have hexact : (G.chromaticNumber.toNat : ℝ) = (k : ℝ) := by
    linarith
  exact_mod_cast hexact

-- Convert the archive's real-valued bound to a natural-number dimension budget.
-- This is the kernel of the adjacency matrix over GF(2), with the same vertices
-- indexing both rows and columns.
theorem adjacency_code_dimension_budget {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (budget : ℕ) (horder : Fintype.card V ≤ budget) :
    Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
      ≤ budget := by
  have hdimension :
      Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
        ≤ Fintype.card V := by
    exact_mod_cast (MathFoundry.parity_code_dimension_le_order G)
  exact hdimension.trans horder

-- Concrete applications used in the practical guide; CI audits these too.
theorem no_three_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclique : 3 < G.cliqueNum) : ¬ G.Colorable 3 := by
  exact coloring_obstruction G 3 hclique

theorem four_colors_from_matching_bounds {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclique : G.cliqueNum = 4) (hdegree : G.maxDegree + 1 = 4) :
    G.chromaticNumber.toNat = 4 := by
  exact chromatic_number_from_matching_bounds G 4 hclique hdegree

theorem sixteen_vertex_dimension_budget (G : SimpleGraph (Fin 16))
    [DecidableRel G.Adj] :
    Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin)
      ≤ 16 := by
  exact adjacency_code_dimension_budget G 16 (by simp)

end FoundryConsumer
