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

theorem cvetkovic_signless_laplacian_max_deg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    positivity
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    rw [if_neg hV]
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    change sSup (Set.range hQ.eigenvalues) ≤ (2 : ℝ) * (G.maxDegree : ℝ)
    apply csSup_le (Set.range_nonempty hQ.eigenvalues)
    rintro r ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hQ.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun w : V => |x w|) Finset.univ_nonempty
    obtain ⟨u, hu⟩ := Function.ne_iff.mp hx
    have hpos : 0 < |x v| :=
      lt_of_lt_of_le (abs_pos.mpr hu) (hmax u (Finset.mem_univ u))
    have heig : (G.degree v : ℝ) * x v +
        (∑ w ∈ G.neighborFinset v, x w) = hQ.eigenvalues i * x v := by
      simpa only [x, Matrix.add_mulVec, Pi.add_apply,
        G.degMatrix_mulVec_apply, G.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul] using
        congrFun (hQ.mulVec_eigenvectorBasis i) v
    have hsum : |∑ w ∈ G.neighborFinset v, x w| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
        _ = (G.degree v : ℝ) * |x v| := by
          rw [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
    have hbound : |hQ.eigenvalues i| * |x v| ≤
        (2 : ℝ) * (G.degree v : ℝ) * |x v| := by
      calc
        _ = |hQ.eigenvalues i * x v| := (abs_mul _ _).symm
        _ = |(G.degree v : ℝ) * x v +
            (∑ w ∈ G.neighborFinset v, x w)| := congrArg abs heig.symm
        _ ≤ |(G.degree v : ℝ) * x v| +
            |∑ w ∈ G.neighborFinset v, x w| := abs_add_le _ _
        _ ≤ (G.degree v : ℝ) * |x v| +
            (G.degree v : ℝ) * |x v| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (G.degree v))]
          exact add_le_add (le_refl _) hsum
        _ = (2 : ℝ) * (G.degree v : ℝ) * |x v| := by ring
    have hlambda : |hQ.eigenvalues i| ≤ (2 : ℝ) * (G.degree v : ℝ) :=
      le_of_mul_le_mul_right hbound hpos
    have hdeg : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast G.degree_le_maxDegree v
    calc
      hQ.eigenvalues i ≤ |hQ.eigenvalues i| := le_abs_self _
      _ ≤ (2 : ℝ) * (G.degree v : ℝ) := hlambda
      _ ≤ (2 : ℝ) * (G.maxDegree : ℝ) :=
        mul_le_mul_of_nonneg_left hdeg (by norm_num)

theorem hull3d_algebraic_connectivity_le_0_1_min_degree_laplacian_spectral_radius_0_2a2b3957145e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn0 : Fintype.card V = 0
  · have hn : ¬ 2 ≤ Fintype.card V := by omega
    simp [hn0, hn]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
    rw [if_neg hn0]
    let H := G.isHermitian_lapMatrix ℝ
    have hbdd : BddAbove (Set.range H.eigenvalues) :=
      (Set.finite_range H.eigenvalues).bddAbove
    have hzero : (0 : ℝ) ∈ Set.range H.eigenvalues := by
      rw [← H.spectrum_real_eq_range_eigenvalues]
      exact G.zero_mem_spectrum_lapMatrix ℝ
    have hnonneg : (0 : ℝ) ≤ sSup (Set.range H.eigenvalues) :=
      le_csSup hbdd hzero
    by_cases hc : G.Connected
    · simp only [if_pos hc]
      by_cases hn : 2 ≤ Fintype.card V
      · simp only [dif_pos hn]
        let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
        let e : Fin (Fintype.card V) ≃ V :=
          Fintype.equivOfCardEq (Fintype.card_fin _)
        have he : H.eigenvalues (e j) = H.eigenvalues₀ j := by
          change H.eigenvalues₀ (e.symm (e j)) = H.eigenvalues₀ j
          rw [e.symm_apply_apply]
        change H.eigenvalues₀ j ≤ sSup (Set.range H.eigenvalues)
        rw [← he]
        exact le_csSup hbdd ⟨e j, rfl⟩
      · simp only [dif_neg hn]
        exact hnonneg
    · simp only [if_neg hc]
      exact hnonneg

theorem spectral_spread_le_two_max_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, sub_self]
    positivity
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let hA := G.isHermitian_adjMatrix ℝ
    change sSup (Set.range hA.eigenvalues) - sInf (Set.range hA.eigenvalues) ≤
      (2 : ℝ) * (G.maxDegree : ℝ)
    have hbound : ∀ i : V, |hA.eigenvalues i| ≤ (G.maxDegree : ℝ) := by
      intro i
      let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
      have hx : x ≠ 0 :=
        (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
      obtain ⟨v, _, hmax⟩ :=
        Finset.exists_max_image Finset.univ (fun w : V => |x w|) Finset.univ_nonempty
      obtain ⟨u, hu⟩ := Function.ne_iff.mp hx
      have hpos : 0 < |x v| :=
        lt_of_lt_of_le (abs_pos.mpr hu) (hmax u (Finset.mem_univ u))
      have heig : (∑ w ∈ G.neighborFinset v, x w) = hA.eigenvalues i * x v := by
        simpa only [x, G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
          congrFun (hA.mulVec_eigenvectorBasis i) v
      have hsum : |∑ w ∈ G.neighborFinset v, x w| ≤
          (G.degree v : ℝ) * |x v| := by
        calc
          _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _w ∈ G.neighborFinset v, |x v| :=
            Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
          _ = (G.degree v : ℝ) * |x v| := by
            rw [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
      have hprod : |hA.eigenvalues i| * |x v| ≤
          (G.degree v : ℝ) * |x v| := by
        calc
          _ = |hA.eigenvalues i * x v| := (abs_mul _ _).symm
          _ = |∑ w ∈ G.neighborFinset v, x w| := congrArg abs heig.symm
          _ ≤ (G.degree v : ℝ) * |x v| := hsum
      have hlambda : |hA.eigenvalues i| ≤ (G.degree v : ℝ) :=
        le_of_mul_le_mul_right hprod hpos
      have hdeg : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
        exact_mod_cast G.degree_le_maxDegree v
      exact hlambda.trans hdeg
    have hsup : sSup (Set.range hA.eigenvalues) ≤ (G.maxDegree : ℝ) := by
      apply csSup_le (Set.range_nonempty hA.eigenvalues)
      rintro r ⟨i, rfl⟩
      exact (abs_le.mp (hbound i)).2
    have hinf : -(G.maxDegree : ℝ) ≤ sInf (Set.range hA.eigenvalues) := by
      apply le_csInf (Set.range_nonempty hA.eigenvalues)
      rintro r ⟨i, rfl⟩
      exact (abs_le.mp (hbound i)).1
    linarith

theorem hull3d_order_ge_1_0_laplacian_spectral_radius_signless_laplacian_spectral_radius_0_is_connected_88f94a53c8e1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Fintype.card V : ℝ) ≥ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · rw [if_neg hn]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    let u : EuclideanSpace ℝ V := (G.isHermitian_lapMatrix ℝ).eigenvectorBasis i
    let x : V → ℝ := ⇑u
    have hu : ‖u‖ = 1 :=
      (G.isHermitian_lapMatrix ℝ).eigenvectorBasis.orthonormal.1 i
    have hnorm : (∑ v : V, (x v) ^ 2) = 1 := by
      have hh := EuclideanSpace.real_norm_sq_eq u
      rw [hu, one_pow] at hh
      exact hh.symm
    have heig : (G.isHermitian_lapMatrix ℝ).eigenvalues i =
        Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x := by
      simpa only [Matrix.toLinearMap₂'_apply', star_trivial, RCLike.re_to_real]
        using (G.isHermitian_lapMatrix ℝ).eigenvalues_eq i
    have hsumle :
        (∑ v : V, ∑ w : V, if G.Adj v w then (x v - x w) ^ 2 else 0) ≤
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      by_cases hadj : G.Adj v w
      · simp only [if_pos hadj, le_refl]
      · simpa only [if_neg hadj] using sq_nonneg (x v - x w)
    have hsum :
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) =
        2 * ((Fintype.card V : ℝ) * (∑ v : V, (x v) ^ 2) -
          (∑ v : V, x v) ^ 2) := by
      have hrow (v : V) :
          (∑ w : V, (x v - x w) ^ 2) =
          (Fintype.card V : ℝ) * (x v) ^ 2 -
            2 * x v * (∑ w : V, x w) + (∑ w : V, (x w) ^ 2) := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [hrow]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum, hnorm] at hsumle
    rw [heig, G.lapMatrix_toLinearMap₂' ℝ x]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [hsumle, sq_nonneg (∑ v : V, x v)]

theorem hull3d_signless_laplacian_spectral_radius_ge_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_26c733c31f3e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    rw [if_neg hV, hd.maxDegree_eq]
    have hspec : (2 : ℝ) * (d : ℝ) ∈
        spectrum ℝ (G.degMatrix ℝ + G.adjMatrix ℝ) := by
      rw [hd.degMatrix_eq (R := ℝ)]
      simpa only [map_natCast, two_mul] using
        (spectrum.add_mem_add_iff (a := G.adjMatrix ℝ)
          (r := (d : ℝ)) (s := (d : ℝ))).2
          (hd.mem_spectrum_adjMatrix (R := ℝ))
    rw [((G.isHermitian_degMatrix ℝ).add
      (G.isHermitian_adjMatrix ℝ)).spectrum_real_eq_range_eigenvalues] at hspec
    exact le_csSup (Set.finite_range _).bddAbove hspec

theorem hull3d_signless_laplacian_spectral_radius_le_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_fd3eb1d598b5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    rw [if_neg hV, hd.maxDegree_eq]
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    change sSup (Set.range hQ.eigenvalues) ≤ (2 : ℝ) * (d : ℝ)
    apply csSup_le (Set.range_nonempty hQ.eigenvalues)
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hx : dotProduct x x = (1 : ℝ) := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
        hQ.eigenvectorBasis.inner_eq_one i
    have hdeg : dotProduct x (Matrix.mulVec (G.degMatrix ℝ) x) = (d : ℝ) := by
      simp only [hd.degMatrix_eq (R := ℝ), Matrix.natCast_mulVec,
        dotProduct_smul, hx, smul_eq_mul, mul_one]
    have heig : hQ.eigenvalues i =
        dotProduct x (Matrix.mulVec (G.degMatrix ℝ) x) +
        dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) := by
      simpa only [star_trivial, RCLike.re_to_real, Matrix.add_mulVec,
        dotProduct_add] using hQ.eigenvalues_eq i
    have hpos : (0 : ℝ) ≤
        dotProduct x (Matrix.mulVec (G.degMatrix ℝ) x) -
        dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) := by
      simpa only [SimpleGraph.lapMatrix, Matrix.sub_mulVec,
        dotProduct_sub, star_trivial] using
        (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
    rw [hdeg] at heig hpos
    linarith
theorem hull_laplacian_spectral_radius_le_2_max_degree_0_3b14564974f2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) ≤ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    positivity
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    rw [if_neg hV]
    let hL := G.isHermitian_lapMatrix ℝ
    change sSup (Set.range hL.eigenvalues) ≤ (2 : ℝ) * (G.maxDegree : ℝ)
    apply csSup_le (Set.range_nonempty hL.eigenvalues)
    rintro r ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hL.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hL.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun w : V => |x w|) Finset.univ_nonempty
    obtain ⟨u, hu⟩ := Function.ne_iff.mp hx
    have hpos : 0 < |x v| :=
      lt_of_lt_of_le (abs_pos.mpr hu) (hmax u (Finset.mem_univ u))
    have heig : (G.degree v : ℝ) * x v -
        (∑ w ∈ G.neighborFinset v, x w) = hL.eigenvalues i * x v := by
      simpa only [x, G.lapMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun (hL.mulVec_eigenvectorBasis i) v
    have hsum : |∑ w ∈ G.neighborFinset v, x w| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
        _ = (G.degree v : ℝ) * |x v| := by
          rw [Finset.sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
    have hbound : |hL.eigenvalues i| * |x v| ≤
        (2 : ℝ) * (G.degree v : ℝ) * |x v| := by
      calc
        _ = |hL.eigenvalues i * x v| := (abs_mul _ _).symm
        _ = |(G.degree v : ℝ) * x v -
            (∑ w ∈ G.neighborFinset v, x w)| := congrArg abs heig.symm
        _ ≤ |(G.degree v : ℝ) * x v| +
            |∑ w ∈ G.neighborFinset v, x w| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le ((G.degree v : ℝ) * x v)
              (-(∑ w ∈ G.neighborFinset v, x w)))
        _ ≤ (G.degree v : ℝ) * |x v| +
            (G.degree v : ℝ) * |x v| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (G.degree v))]
          exact add_le_add (le_refl _) hsum
        _ = (2 : ℝ) * (G.degree v : ℝ) * |x v| := by ring
    have hlambda : |hL.eigenvalues i| ≤ (2 : ℝ) * (G.degree v : ℝ) :=
      le_of_mul_le_mul_right hbound hpos
    have hdeg : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast G.degree_le_maxDegree v
    calc
      hL.eigenvalues i ≤ |hL.eigenvalues i| := le_abs_self _
      _ ≤ (2 : ℝ) * (G.degree v : ℝ) := hlambda
      _ ≤ (2 : ℝ) * (G.maxDegree : ℝ) :=
        mul_le_mul_of_nonneg_left hdeg (by norm_num)
