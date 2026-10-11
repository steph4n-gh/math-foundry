import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

theorem signless_laplacian_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    let hQ := (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    let f : V → ℝ := hQ.eigenvalues
    have htrace : (∑ v : V, f v) = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      change (∑ v : V, hQ.eigenvalues v) = (2 : ℝ) * (G.edgeFinset.card : ℝ)
      have htrace_eq : Matrix.trace (G.degMatrix ℝ + G.adjMatrix ℝ) =
          ∑ v : V, hQ.eigenvalues v := by
        simpa using hQ.trace_eq_sum_eigenvalues
      rw [← htrace_eq]
      simp only [Matrix.trace_add, SimpleGraph.trace_adjMatrix, add_zero,
        SimpleGraph.degMatrix, Matrix.trace_diagonal]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : (∑ v : V, f v) ≤
        (Fintype.card V : ℝ) * sSup (Set.range f) := by
      calc
        (∑ v : V, f v) ≤ ∑ _ : V, sSup (Set.range f) :=
          Finset.sum_le_sum (fun v _ =>
            le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v))
        _ = (Fintype.card V : ℝ) * sSup (Set.range f) := by simp
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    change (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤
      sSup (Set.range f)
    apply (div_le_iff₀ hpos).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) = ∑ v : V, f v := htrace.symm
      _ ≤ (Fintype.card V : ℝ) * sSup (Set.range f) := hbound
      _ = sSup (Set.range f) * (Fintype.card V : ℝ) := mul_comm _ _

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

theorem signless_laplacian_spectral_plus_max_deg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, zero_add]
    exact Nat.cast_nonneg _
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let hA : (G.adjMatrix ℝ).IsHermitian := G.isHermitian_adjMatrix ℝ
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add hA
    let r : ℝ := sSup (Set.range hA.eigenvalues)
    change sSup (Set.range hQ.eigenvalues) ≤ r + (G.maxDegree : ℝ)
    have hr (i : V) : hA.eigenvalues i ≤ r :=
      le_csSup (Set.finite_range hA.eigenvalues).bddAbove (Set.mem_range_self i)
    have hC : (r • (1 : Matrix V V ℝ) - G.adjMatrix ℝ).PosSemidef := by
      have hp : (Matrix.diagonal (fun i : V => r - hA.eigenvalues i)).PosSemidef :=
        Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hr i))
      have hs :
          Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
            (Matrix.diagonal (fun i : V => r - hA.eigenvalues i)) =
          r • (1 : Matrix V V ℝ) - G.adjMatrix ℝ := by
        rw [← Matrix.diagonal_sub (fun _ : V => r) hA.eigenvalues,
          ← Matrix.smul_one_eq_diagonal r, map_sub, map_smul, map_one]
        exact congrArg (fun M : Matrix V V ℝ => r • (1 : Matrix V V ℝ) - M)
          hA.spectral_theorem.symm
      rw [← hs]
      simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose] using
        hp.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix V V ℝ)
    have hD :
        ((G.maxDegree : ℝ) • (1 : Matrix V V ℝ) - G.degMatrix ℝ).PosSemidef := by
      rw [Matrix.smul_one_eq_diagonal, SimpleGraph.degMatrix, Matrix.diagonal_sub]
      apply Matrix.PosSemidef.diagonal
      intro i
      apply sub_nonneg.mpr
      exact_mod_cast (G.degree_le_maxDegree i)
    refine csSup_le (Set.range_nonempty hQ.eigenvalues) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hxunit : dotProduct x x = 1 := by
      have hinner :
          inner ℝ (hQ.eigenvectorBasis i) (hQ.eigenvectorBasis i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hQ.eigenvectorBasis.orthonormal.1 i]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
    have ha := hC.dotProduct_mulVec_nonneg x
    have hd := hD.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hxunit, mul_one] at ha hd
    have heig : hQ.eigenvalues i =
        dotProduct x (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) x) := by
      simpa only [star_trivial, RCLike.re_to_real] using hQ.eigenvalues_eq i
    rw [Matrix.add_mulVec, dotProduct_add] at heig
    linarith

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

theorem model_bd1be5306bec4c1ad48f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) = ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    apply le_antisymm
    · obtain ⟨d, hd⟩ := h_guard
      rw [if_neg hV, hd.maxDegree_eq]
      let hQ := (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
      change sSup (Set.range hQ.eigenvalues) ≤ (2 : ℝ) * (d : ℝ)
      apply csSup_le (Set.range_nonempty _)
      rintro μ ⟨i, rfl⟩
      let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
      have hunit : dotProduct (star x) x = (1 : ℝ) := by
        change dotProduct (star ⇑(hQ.eigenvectorBasis i))
          ⇑(hQ.eigenvectorBasis i) = (1 : ℝ)
        rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
          inner_self_eq_norm_sq_to_K]
        simp
      have heig : Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) x =
          hQ.eigenvalues i • x := hQ.mulVec_eigenvectorBasis i
      have hmul : Matrix.mulVec (G.lapMatrix ℝ) x =
          ((2 : ℝ) * (d : ℝ) - hQ.eigenvalues i) • x := by
        ext v
        have hv := congrFun heig v
        simp only [Matrix.add_mulVec, Pi.add_apply,
          SimpleGraph.degMatrix_mulVec_apply, hd.degree_eq,
          Pi.smul_apply, smul_eq_mul] at hv
        simp only [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply,
          SimpleGraph.degMatrix_mulVec_apply, hd.degree_eq,
          Pi.smul_apply, smul_eq_mul]
        nlinarith [hv]
      have hnonneg := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
      rw [hmul, dotProduct_smul, hunit, smul_eq_mul, mul_one] at hnonneg
      linarith
    · exact hull3d_signless_laplacian_spectral_radius_ge_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_26c733c31f3e G h_guard
theorem model_e1bd2d98ab50c3dcff7c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ^ 2)) ≥ ((4 : ℝ) * ((((Fintype.card V : ℝ) - (1 : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)) + (((G.maxDegree : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) ^ 2))) := by
  sorry
