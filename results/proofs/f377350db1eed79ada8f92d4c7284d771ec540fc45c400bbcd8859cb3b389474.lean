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

theorem hull3d_size_ge_1_0_signless_laplacian_spectral_radius_clique_number__1_is_connected_e56f65d5cb44 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - (1 : ℝ)) := by
  classical
  have hdeg (v w : V) (hadj : G.Adj v w) :
      G.degree v + G.degree w ≤ G.edgeFinset.card + 1 := by
    have hinter : G.incidenceFinset v ∩ G.incidenceFinset w ⊆
        ({s(v, w)} : Finset (Sym2 V)) := by
      intro e he
      rcases Finset.mem_inter.mp he with ⟨hev, hew⟩
      apply Finset.mem_singleton.mpr
      exact Set.mem_singleton_iff.mp
        (G.incidenceSet_inter_incidenceSet_subset hadj.ne
          ⟨SimpleGraph.mem_incidenceFinset.mp hev,
           SimpleGraph.mem_incidenceFinset.mp hew⟩)
    have hi : (G.incidenceFinset v ∩ G.incidenceFinset w).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hinter
    have hu : (G.incidenceFinset v ∪ G.incidenceFinset w).card ≤
        G.edgeFinset.card :=
      Finset.card_le_card
        (Finset.union_subset (G.incidenceFinset_subset v)
          (G.incidenceFinset_subset w))
    have hc := Finset.card_union_add_card_inter
      (G.incidenceFinset v) (G.incidenceFinset w)
    simp only [SimpleGraph.card_incidenceFinset_eq_degree] at hc
    omega
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    have hm : (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
    linarith
  · rw [if_neg hV]
    letI : Nonempty V :=
      Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hV)
    let hQ := (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    change (G.edgeFinset.card : ℝ) ≥ sSup (Set.range hQ.eigenvalues) - 1
    suffices hs : sSup (Set.range hQ.eigenvalues) ≤
        (G.edgeFinset.card : ℝ) + 1 by
      linarith only [hs]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    by_cases hnonpos : hQ.eigenvalues i ≤ 0
    · exact hnonpos.trans (by positivity)
    have hpos : 0 < hQ.eigenvalues i := lt_of_not_ge hnonpos
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        (hQ.eigenvectorBasis.orthonormal.ne_zero i)
    have hrow (v : V) :
        (∑ u ∈ G.neighborFinset v, (x v + x u)) = hQ.eigenvalues i * x v := by
      calc
        (∑ u ∈ G.neighborFinset v, (x v + x u)) =
            (G.degree v : ℝ) * x v + ∑ u ∈ G.neighborFinset v, x u := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
        _ = hQ.eigenvalues i * x v := by
          simpa only [Matrix.add_mulVec, Pi.add_apply,
            SimpleGraph.degMatrix_mulVec_apply,
            SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
            using congrFun (hQ.mulVec_eigenvectorBasis i) v
    let E : Finset (V × V) := Finset.univ.filter (fun p => G.Adj p.1 p.2)
    have hex : ∃ p : V × V, p ∈ E ∧ x p.1 + x p.2 ≠ 0 := by
      by_contra hn
      have hz (v : V) : hQ.eigenvalues i * x v = 0 := by
        rw [← hrow v]
        apply Finset.sum_eq_zero
        intro u hu
        by_contra hne
        apply hn
        exact ⟨(v, u), by simp [E, (G.mem_neighborFinset v u).mp hu], hne⟩
      apply hx
      funext v
      exact (mul_eq_zero.mp (hz v)).resolve_left (ne_of_gt hpos)
    obtain ⟨r, hrE, hr0⟩ := hex
    obtain ⟨p, hpE, hmax⟩ :=
      Finset.exists_max_image E (fun p => |x p.1 + x p.2|) ⟨r, hrE⟩
    have hp : 0 < |x p.1 + x p.2| :=
      lt_of_lt_of_le (abs_pos.mpr hr0) (hmax r hrE)
    have hmax' (a b : V) (hab : G.Adj a b) :
        |x a + x b| ≤ |x p.1 + x p.2| :=
      hmax (a, b) (by simp [E, hab])
    have hbound (v : V) :
        |∑ u ∈ G.neighborFinset v, (x v + x u)| ≤
          (G.degree v : ℝ) * |x p.1 + x p.2| := by
      calc
        _ ≤ ∑ u ∈ G.neighborFinset v, |x v + x u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |x p.1 + x p.2| :=
          Finset.sum_le_sum (fun u hu =>
            hmax' v u ((G.mem_neighborFinset v u).mp hu))
        _ = (G.degree v : ℝ) * |x p.1 + x p.2| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have hprod : |hQ.eigenvalues i| * |x p.1 + x p.2| ≤
        ((G.degree p.1 : ℝ) + (G.degree p.2 : ℝ)) * |x p.1 + x p.2| := by
      calc
        _ = |hQ.eigenvalues i * x p.1 + hQ.eigenvalues i * x p.2| := by
          rw [← mul_add, abs_mul]
        _ = |(∑ u ∈ G.neighborFinset p.1, (x p.1 + x u)) +
              (∑ u ∈ G.neighborFinset p.2, (x p.2 + x u))| := by
          rw [hrow p.1, hrow p.2]
        _ ≤ |∑ u ∈ G.neighborFinset p.1, (x p.1 + x u)| +
              |∑ u ∈ G.neighborFinset p.2, (x p.2 + x u)| := abs_add_le _ _
        _ ≤ (G.degree p.1 : ℝ) * |x p.1 + x p.2| +
              (G.degree p.2 : ℝ) * |x p.1 + x p.2| :=
          add_le_add (hbound p.1) (hbound p.2)
        _ = ((G.degree p.1 : ℝ) + (G.degree p.2 : ℝ)) *
              |x p.1 + x p.2| := by ring
    have heigen : hQ.eigenvalues i ≤
        (G.degree p.1 : ℝ) + (G.degree p.2 : ℝ) :=
      (le_abs_self _).trans (le_of_mul_le_mul_right hprod hp)
    have hdegR : (G.degree p.1 : ℝ) + (G.degree p.2 : ℝ) ≤
        (G.edgeFinset.card : ℝ) + 1 := by
      exact_mod_cast hdeg p.1 p.2 ((Finset.mem_filter.mp hpE).2)
    exact heigen.trans hdegR
