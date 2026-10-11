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

theorem hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  rw [if_neg hV]
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
    (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  have hsym : (G.adjMatrix ℝ).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
  have heig (i : V) : (G.adjMatrix ℝ).toEuclideanLin (b i) =
      (G.isHermitian_adjMatrix ℝ).eigenvalues i • b i := by
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
      (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
  have hle (i : V) : (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ r :=
    le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
  have hq (x : EuclideanSpace ℝ V) :
      inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x ≤ r * inner ℝ x x := by
    calc
      inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
          ∑ i : V, (G.isHermitian_adjMatrix ℝ).eigenvalues i *
            (inner ℝ x (b i)) ^ 2 := by
        rw [← b.sum_inner_mul_inner ((G.adjMatrix ℝ).toEuclideanLin x) x]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym x (b i), heig i, inner_smul_right, real_inner_comm x (b i)]
        ring
      _ ≤ ∑ i : V, r * (inner ℝ x (b i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
      _ = r * inner ℝ x x := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          (∑ i : V, (inner ℝ x (b i)) ^ 2) =
              ∑ i : V, inner ℝ x (b i) * inner ℝ (b i) x := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_comm x (b i)]
            ring
          _ = inner ℝ x x := b.sum_inner_mul_inner x x
  let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have hnorm : inner ℝ x x = (Fintype.card V : ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x, dotProduct]
  have hinner : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [x, WithLp.ofLp_toLp, star_trivial]
    change (∑ v : V, (1 : ℝ) *
      Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)) v) = _
    simp only [one_mul, SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hV
  apply (div_le_iff₀ hpos).2
  simpa only [if_neg hV, hinner, hnorm] using hq x

theorem hull_spectral_radius_le_1_max_degree_0_e423c6789900 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (G.maxDegree : ℝ) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg G.maxDegree
  · rw [if_neg hV]
    letI : Nonempty V :=
      Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hV)
    let hA := G.isHermitian_adjMatrix ℝ
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        (hA.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    have hw0 : x w ≠ 0 := by
      simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V)
        (fun u => |x u|) Finset.univ_nonempty
    have hp : 0 < |x v| :=
      lt_of_lt_of_le (abs_pos.mpr hw0) (hmax w (Finset.mem_univ w))
    have heq : (∑ u ∈ G.neighborFinset v, x u) =
        hA.eigenvalues i * x v := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply,
        smul_eq_mul] using congrFun (hA.mulVec_eigenvectorBasis i) v
    have habs : |hA.eigenvalues i| * |x v| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        |hA.eigenvalues i| * |x v| =
            |∑ u ∈ G.neighborFinset v, x u| := by
          rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset v, |x u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun u _ => hmax u (Finset.mem_univ u))
        _ = (G.degree v : ℝ) * |x v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have heigen : hA.eigenvalues i ≤ (G.degree v : ℝ) :=
      (le_abs_self _).trans (le_of_mul_le_mul_right habs hp)
    have hdegree : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast (G.degree_le_maxDegree v)
    exact heigen.trans hdegree

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

theorem composed_9760f9b31100c13d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (G.maxDegree : ℝ)) := by
  refine le_trans (signless_laplacian_avg_deg_lower G) ?_
  exact signless_laplacian_spectral_plus_max_deg G

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
theorem model_c411c8365954f60ffdad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * ((G.maxDegree : ℝ) ^ 2)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ^ 2) - ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ^ 2))) := by
  sorry
