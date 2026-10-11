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

theorem hull_spectral_radius_le_0_5_size_0_5_bf1d5973d871 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (((1 / 2 : ℝ) * (G.edgeFinset.card : ℝ)) + (1 / 2 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · rw [if_pos hn]
    positivity
  · rw [if_neg hn]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    have hpair (v w : V) (hvw : G.Adj v w) :
        G.degree v + G.degree w ≤ G.edgeFinset.card + 1 := by
      have hinter : G.incidenceFinset v ∩ G.incidenceFinset w = {s(v, w)} := by
        apply Finset.coe_injective
        simpa only [Finset.coe_inter, SimpleGraph.coe_incidenceFinset,
          Finset.coe_singleton] using G.incidenceSet_inter_incidenceSet_of_adj hvw
      have hcard := Finset.card_union_add_card_inter
        (G.incidenceFinset v) (G.incidenceFinset w)
      simp only [hinter, Finset.card_singleton,
        SimpleGraph.card_incidenceFinset_eq_degree] at hcard
      have hunion : (G.incidenceFinset v ∪ G.incidenceFinset w).card ≤
          G.edgeFinset.card :=
        Finset.card_le_card (Finset.union_subset
          (G.incidenceFinset_subset v) (G.incidenceFinset_subset w))
      omega
    have hneighbor (v : V) :
        (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) ≤
          (G.degree v : ℝ) *
            ((G.edgeFinset.card : ℝ) + 1 - (G.degree v : ℝ)) := by
      calc
        _ ≤ ∑ _w ∈ G.neighborFinset v,
            ((G.edgeFinset.card : ℝ) + 1 - (G.degree v : ℝ)) := by
          apply Finset.sum_le_sum
          intro w hw
          have hp : (G.degree v : ℝ) + (G.degree w : ℝ) ≤
              (G.edgeFinset.card : ℝ) + 1 := by
            exact_mod_cast hpair v w ((G.mem_neighborFinset v w).mp hw)
          linarith only [hp]
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let hA := G.isHermitian_adjMatrix ℝ
    let r : ℝ := hA.eigenvalues i
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    change r ≤ (1 / 2 : ℝ) * (G.edgeFinset.card : ℝ) + (1 / 2 : ℝ)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        (hA.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    have hw0 : x w ≠ 0 := by
      simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V)
        (fun u => |x u|) Finset.univ_nonempty
    have hpos : 0 < |x v| :=
      (abs_pos.mpr hw0).trans_le (hmax w (Finset.mem_univ w))
    have heig (u : V) :
        (∑ z ∈ G.neighborFinset u, x z) = r * x u := by
      simpa only [x, r, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis i) u
    have hdouble : r ^ 2 * x v =
        ∑ u ∈ G.neighborFinset v, ∑ z ∈ G.neighborFinset u, x z := by
      calc
        r ^ 2 * x v = r * (r * x v) := by ring
        _ = r * (∑ u ∈ G.neighborFinset v, x u) := by rw [heig v]
        _ = ∑ u ∈ G.neighborFinset v, r * x u := by rw [Finset.mul_sum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (heig u).symm
    have hbound : r ^ 2 * |x v| ≤
        ((G.degree v : ℝ) *
          ((G.edgeFinset.card : ℝ) + 1 - (G.degree v : ℝ))) * |x v| := by
      calc
        r ^ 2 * |x v| = |r ^ 2 * x v| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
        _ = |∑ u ∈ G.neighborFinset v,
            ∑ z ∈ G.neighborFinset u, x z| := by rw [hdouble]
        _ ≤ ∑ u ∈ G.neighborFinset v,
            |∑ z ∈ G.neighborFinset u, x z| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ u ∈ G.neighborFinset v, (G.degree u : ℝ) * |x v| := by
          apply Finset.sum_le_sum
          intro u hu
          calc
            |∑ z ∈ G.neighborFinset u, x z| ≤
                ∑ z ∈ G.neighborFinset u, |x z| :=
              Finset.abs_sum_le_sum_abs x (G.neighborFinset u)
            _ ≤ ∑ _z ∈ G.neighborFinset u, |x v| :=
              Finset.sum_le_sum (fun z _ => hmax z (Finset.mem_univ z))
            _ = (G.degree u : ℝ) * |x v| := by
              simp only [Finset.sum_const, nsmul_eq_mul,
                SimpleGraph.card_neighborFinset_eq_degree]
        _ = (∑ u ∈ G.neighborFinset v, (G.degree u : ℝ)) * |x v| := by
          rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (hneighbor v) (abs_nonneg _)
    have hsquared : r ^ 2 ≤ (G.degree v : ℝ) *
        ((G.edgeFinset.card : ℝ) + 1 - (G.degree v : ℝ)) :=
      le_of_mul_le_mul_right hbound hpos
    have hfinal : r ^ 2 ≤
        ((1 / 2 : ℝ) * (G.edgeFinset.card : ℝ) + (1 / 2 : ℝ)) ^ 2 := by
      nlinarith only [hsquared,
        sq_nonneg ((G.degree v : ℝ) - (((G.edgeFinset.card : ℝ) + 1) / 2))]
    have hb : (0 : ℝ) ≤
        (1 / 2 : ℝ) * (G.edgeFinset.card : ℝ) + (1 / 2 : ℝ) := by
      positivity
    have habs : |r| ≤
        (1 / 2 : ℝ) * (G.edgeFinset.card : ℝ) + (1 / 2 : ℝ) :=
      (sq_le_sq₀ (abs_nonneg r) hb).mp (by simpa only [sq_abs] using hfinal)
    exact (le_abs_self r).trans habs

theorem hull_spectral_radius_le_0_25_size_1_5_fafb16939177 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (((1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)) + (3 / 2 : ℝ)) := by
  sorry
