-- SPDX-License-Identifier: Apache-2.0
-- Compile in a separate Lake project requiring the certifiedResearch package.
import MathFoundry

namespace FoundryConsumer

theorem clique_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
  exact MathFoundry.archetype_chi_ge_omega G

end FoundryConsumer
