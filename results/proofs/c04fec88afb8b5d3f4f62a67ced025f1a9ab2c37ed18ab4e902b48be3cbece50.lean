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

theorem hull_spectral_radius_le_1_size_0_0f3ad4f640d7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg G.edgeFinset.card
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
    have hdegree : (G.degree v : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      exact_mod_cast (G.degree_le_card_edgeFinset v)
    exact heigen.trans hdegree

theorem hull3d_size_ge_0_1_nordhaus_gaddum_spectral_product_spectral_radius_0_is_bipartite_fd5d8dffd858 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.edgeFinset.card : ℝ) ≥ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg _
  · rw [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨i, rfl⟩
    let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨v, _, hsup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : V => |x w|)
    have hmax (w : V) : |x w| ≤ |x v| := by
      rw [← hsup]
      exact Finset.le_sup' (fun w : V => |x w|) (Finset.mem_univ w)
    have hxv : x v ≠ 0 := by
      intro hzero
      apply hx
      funext w
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa only [hzero, abs_zero] using hmax w
      · exact abs_nonneg _
    have hp : 0 < |x v| := abs_pos.mpr hxv
    have hrow : (∑ w ∈ G.neighborFinset v, x w) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i * x v := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
        using congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) v
    have hprod : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x v| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        _ = |∑ w ∈ G.neighborFinset v, x w| := by rw [hrow, abs_mul]
        _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
          Finset.abs_sum_le_sum_abs x _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun w _ => hmax w)
        _ = (G.degree v : ℝ) * |x v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have habs : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (G.degree v : ℝ) :=
      le_of_mul_le_mul_right hprod hp
    have hdeg : (G.degree v : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.degree_le_card_edgeFinset v
    exact (le_abs_self _).trans (habs.trans hdeg)

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

theorem hull_min_degree_le_1_average_degree_0_36a8fb326490 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.minDegree : ℝ) ≤ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · rw [if_neg hV]
    have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
      calc
        Fintype.card V * G.minDegree =
            Finset.univ.sum (fun _ : V => G.minDegree) := by simp
        _ ≤ Finset.univ.sum (fun v : V => G.degree v) :=
          Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hV)
    apply (le_div_iff₀ hpos).2
    calc
      (G.minDegree : ℝ) * (Fintype.card V : ℝ) =
          (Fintype.card V : ℝ) * (G.minDegree : ℝ) := mul_comm _ _
      _ ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hsum

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

theorem composed_f0d095cf27d0fbe6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.minDegree : ℝ) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) := by
  have hmin := hull_min_degree_le_1_average_degree_0_36a8fb326490 G
  exact hmin.trans (signless_laplacian_avg_deg_lower G)

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
theorem hull3d_spectral_radius_le_0_5_0_signless_laplacian_spectral_radius_clique_number_0_is_connected_616dd0147311 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ ((1 / 2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero, le_refl]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let hA : (G.adjMatrix ℝ).IsHermitian := G.isHermitian_adjMatrix ℝ
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add hA
    let r : ℝ := sSup (Set.range hQ.eigenvalues)
    change sSup (Set.range hA.eigenvalues) ≤ (1 / 2 : ℝ) * r
    have hr (i : V) : hQ.eigenvalues i ≤ r :=
      le_csSup (Set.finite_range hQ.eigenvalues).bddAbove (Set.mem_range_self i)
    have hC :
        (r • (1 : Matrix V V ℝ) - (G.degMatrix ℝ + G.adjMatrix ℝ)).PosSemidef := by
      have hp : (Matrix.diagonal (fun i : V => r - hQ.eigenvalues i)).PosSemidef :=
        Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hr i))
      have hs :
          Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hQ.eigenvectorUnitary
            (Matrix.diagonal (fun i : V => r - hQ.eigenvalues i)) =
          r • (1 : Matrix V V ℝ) - (G.degMatrix ℝ + G.adjMatrix ℝ) := by
        rw [← Matrix.diagonal_sub (fun _ : V => r) hQ.eigenvalues,
          ← Matrix.smul_one_eq_diagonal r, map_sub, map_smul, map_one]
        exact congrArg (fun M : Matrix V V ℝ => r • (1 : Matrix V V ℝ) - M)
          hQ.spectral_theorem.symm
      rw [← hs]
      simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose] using
        hp.mul_mul_conjTranspose_same (hQ.eigenvectorUnitary : Matrix V V ℝ)
    refine csSup_le (Set.range_nonempty hA.eigenvalues) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    have hxunit : dotProduct x x = 1 := by
      have hinner :
          inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
    have hupper := hC.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hxunit, mul_one] at hupper
    rw [Matrix.add_mulVec, dotProduct_add] at hupper
    have hlap := (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg x
    simp only [star_trivial, SimpleGraph.lapMatrix, Matrix.sub_mulVec,
      dotProduct_sub] at hlap
    have heig : hA.eigenvalues i =
        dotProduct x (Matrix.mulVec (G.adjMatrix ℝ) x) := by
      simpa only [star_trivial, RCLike.re_to_real] using hA.eigenvalues_eq i
    linarith
