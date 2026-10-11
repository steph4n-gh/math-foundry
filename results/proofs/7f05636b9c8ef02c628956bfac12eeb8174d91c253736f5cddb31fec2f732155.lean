import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
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

theorem model_2cc243ec07f2570b6bd7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ (¬ ((∃ d : ℕ, G.IsRegularOfDegree d))) ∧ ((Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) < ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  classical
  letI : Nonempty V := h_guard.1.nonempty
  have hV : Fintype.card V ≠ 0 :=
    ne_of_gt (Fintype.card_pos_iff.mpr h_guard.1.nonempty)
  rw [if_neg hV]
  let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  change sSup (Set.range hQ.eigenvalues) < (2 : ℝ) * (G.maxDegree : ℝ)
  by_contra hn
  have hle : sSup (Set.range hQ.eigenvalues) ≤
      (2 : ℝ) * (G.maxDegree : ℝ) := by
    simpa only [if_neg hV] using cvetkovic_signless_laplacian_max_deg G
  have heq : sSup (Set.range hQ.eigenvalues) =
      (2 : ℝ) * (G.maxDegree : ℝ) :=
    le_antisymm hle (le_of_not_gt hn)
  obtain ⟨i, hi⟩ :=
    (Set.range_nonempty hQ.eigenvalues).csSup_mem (Set.finite_range hQ.eigenvalues)
  rw [heq] at hi
  let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
  have hx : x ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hQ.eigenvectorBasis.orthonormal.ne_zero i)
  have hxunit : dotProduct x x = (1 : ℝ) := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using
      hQ.eigenvectorBasis.inner_eq_one i
  have heig : (2 : ℝ) * (G.maxDegree : ℝ) =
      dotProduct x (Matrix.mulVec (G.degMatrix ℝ) x) +
      dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) := by
    simpa only [hi, star_trivial, RCLike.re_to_real, Matrix.add_mulVec,
      dotProduct_add] using hQ.eigenvalues_eq i
  have hD :
      ((G.maxDegree : ℝ) • (1 : Matrix V V ℝ) - G.degMatrix ℝ).PosSemidef := by
    rw [Matrix.smul_one_eq_diagonal, SimpleGraph.degMatrix, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro w
    apply sub_nonneg.mpr
    exact_mod_cast G.degree_le_maxDegree w
  have hd := hD.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    hxunit, mul_one] at hd
  have hl : (0 : ℝ) ≤ dotProduct x (Matrix.mulVec (G.lapMatrix ℝ) x) := by
    simpa only [star_trivial] using
      (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
  have hlzero : dotProduct x (Matrix.mulVec (G.lapMatrix ℝ) x) = 0 := by
    simp only [SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub] at hl ⊢
    linarith
  have hlker : Matrix.mulVec (G.lapMatrix ℝ) x = 0 :=
    (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_zero_iff.mp
      (by simpa only [star_trivial] using hlzero)
  have hconst : ∀ u v : V, G.Reachable u v → x u = x v :=
    G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hlker
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hx
  have heigvec : Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) x =
      ((2 : ℝ) * (G.maxDegree : ℝ)) • x := by
    simpa only [hi] using hQ.mulVec_eigenvectorBasis i
  apply h_guard.2.1
  refine ⟨G.maxDegree, ?_⟩
  intro w
  have hxw : x w ≠ 0 := by
    rw [hconst w v (h_guard.1 w v)]
    exact hv
  have hw := congrFun heigvec w
  have hlw := congrFun hlker w
  simp only [Matrix.add_mulVec, Pi.add_apply, G.degMatrix_mulVec_apply,
    Pi.smul_apply, smul_eq_mul] at hw
  simp only [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    G.degMatrix_mulVec_apply, Pi.zero_apply] at hlw
  have hprod : ((G.degree w : ℝ) - (G.maxDegree : ℝ)) * x w = 0 := by
    nlinarith [hw, hlw]
  have hdegree : (G.degree w : ℝ) = (G.maxDegree : ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hxw)
  exact_mod_cast hdegree
