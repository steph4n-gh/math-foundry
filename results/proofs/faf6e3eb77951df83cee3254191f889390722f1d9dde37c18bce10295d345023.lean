import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic








open scoped BigOperators

theorem graph_energy_spectral_radius_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  have hsum : (∑ v : V, f v) = 0 := by
    simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hnonneg (w : V) : 0 ≤ |f w| + f w := by
      linarith [neg_abs_le (f w)]
    have hsingle : |f v| + f v ≤ ∑ w : V, (|f w| + f w) :=
      Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
    simp only [Finset.sum_add_distrib, hsum, add_zero] at hsingle
    change 2 * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) ≤
      ∑ w : V, |f w|
    rw [if_neg hV, ← hv]
    linarith [le_abs_self (f v)]

theorem hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.minDegree : ℝ) ≤ ((1 / 2 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    have hmem : (d : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) :=
      SimpleGraph.IsRegularOfDegree.mem_spectrum_adjMatrix (R := ℝ) (G := G) hd
    rw [(G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hmem
    have hdle : (d : ℝ) ≤
        sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) :=
      le_csSup (Set.finite_range (G.isHermitian_adjMatrix ℝ).eigenvalues).bddAbove hmem
    have henergy := graph_energy_spectral_radius_lower G
    rw [if_neg hV] at henergy
    rw [SimpleGraph.IsRegularOfDegree.minDegree_eq (G := G) hd]
    linarith

theorem hull3d_graph_energy_ge_2_0_average_degree_size_0_is_regular_479d55ae89c3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
      simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
    have hsum : (Fintype.card V : ℝ) * (d : ℝ) =
        2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hsum_nat
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast hV
    have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        (Fintype.card V : ℝ) = (d : ℝ) := by
      apply (div_eq_iff hcard).2
      exact hsum.symm.trans (mul_comm _ _)
    have henergy :=
      hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939
        G ⟨d, hd⟩
    rw [hd.minDegree_eq] at henergy
    rw [if_neg hV, havg]
    linarith

theorem estrada_ge_energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  classical
  have hsum : (∑ v : V, (G.isHermitian_adjMatrix ℝ).eigenvalues v) = 0 := by
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have hpoint (x : ℝ) : |x| + x ≤ Real.exp x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hexp := Real.quadratic_le_exp_of_nonneg hx
      nlinarith [sq_nonneg (x - 1)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have hbound :
      (∑ v : V, (|(G.isHermitian_adjMatrix ℝ).eigenvalues v| +
        (G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≤
      ∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v) := by
    exact Finset.sum_le_sum (fun v _ => hpoint _)
  simpa only [Finset.sum_add_distrib, hsum, add_zero] using hbound

theorem hull3d_graph_energy_le_0_2_average_degree_size_0_is_regular_99710b2e7422 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨d, hd⟩ := h_guard
  have hbound (i : V) : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (d : ℝ) := by
    let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    obtain ⟨w, _, hw⟩ := Finset.exists_max_image Finset.univ (fun v => |x v|)
      ⟨j, Finset.mem_univ j⟩
    have hwpos : 0 < |x w| :=
      lt_of_lt_of_le (abs_pos.mpr hj) (hw j (Finset.mem_univ j))
    have heq : (∑ u ∈ G.neighborFinset w, x u) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i * x w := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) w
    have hmul : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| ≤
        (d : ℝ) * |x w| := by
      calc
        |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| =
            |∑ u ∈ G.neighborFinset w, x u| := by rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset w, |x u| :=
          Finset.abs_sum_le_sum_abs x (G.neighborFinset w)
        _ ≤ ∑ u ∈ G.neighborFinset w, |x w| :=
          Finset.sum_le_sum (fun u _ => hw u (Finset.mem_univ u))
        _ = (d : ℝ) * |x w| := by
          simp only [Finset.sum_const, G.card_neighborFinset_eq_degree,
            hd.degree_eq, nsmul_eq_mul]
    exact (mul_le_mul_iff_left₀ hwpos).mp hmul
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤
        ∑ _v : V, (d : ℝ) :=
      Finset.sum_le_sum (fun v _ => hbound v)
    _ = ∑ v : V, (G.degree v : ℝ) := by simp only [hd.degree_eq]
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem hull3d_average_degree_le_0_5_0_graph_energy_diameter_0_is_regular_634736df2435 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ ((1 / 2 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) := by
  have checked_0 := hull3d_min_degree_le_0_0_5_girth_graph_energy_0_is_regular_344494166939 G h_guard; have checked_1 := hull3d_graph_energy_ge_2_0_average_degree_size_0_is_regular_479d55ae89c3 G h_guard; have checked_2 := estrada_ge_energy G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

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
theorem model_f1abeb346d4f50c57240 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) := by
  classical
  rcases h_guard with ⟨hc, ⟨d, hd⟩, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hn : Fintype.card V ≤ 1 := by omega
    have hnr : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  have hsum_nat : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa [hd.degree_eq] using G.sum_degrees_eq_twice_card_edges
  have hsum_real : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn0
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff hcard).2
    exact hsum_real.symm.trans (mul_comm _ _)
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let N : Matrix V V ℝ := D * G.lapMatrix ℝ * Matrix.conjTranspose D
  let hN : N.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  simp only [if_neg hn0, if_pos hc, dif_pos htwo]
  change (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥
    (2 * ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) *
      (1 + max 0 (1 - hN.eigenvalues₀ j))
  rw [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hD : D = (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix V V ℝ) := by
    simp only [D, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hcoef : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hdnonneg]
  have hNsmul : N = (d : ℝ)⁻¹ • G.lapMatrix ℝ := by
    simp only [N, hD, Matrix.conjTranspose_smul, star_trivial,
      Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, hcoef]
  have hdN : (d : ℝ) • N = G.lapMatrix ℝ := by
    rw [hNsmul, smul_smul, mul_inv_cancel₀ hdne, one_smul]
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    simp only [SimpleGraph.degMatrix, hd.degree_eq, Matrix.smul_one_eq_diagonal]
  have hA : G.adjMatrix ℝ =
      (d : ℝ) • (1 : Matrix V V ℝ) - (d : ℝ) • N := by
    rw [hdN, SimpleGraph.lapMatrix, hdeg]
    abel
  let m : V → ℝ := fun v => (d : ℝ) * (1 - hN.eigenvalues v)
  let U := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hN.eigenvectorUnitary
  have hspec : N = U (Matrix.diagonal hN.eigenvalues) := by
    simpa [U] using hN.spectral_theorem
  have hdiag : Matrix.diagonal m =
      (d : ℝ) • (1 : Matrix V V ℝ) -
        (d : ℝ) • Matrix.diagonal hN.eigenvalues := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 1
    funext v
    simp only [m, Pi.smul_apply, smul_eq_mul]
    ring
  have hAconj : G.adjMatrix ℝ = U (Matrix.diagonal m) := by
    rw [hdiag]
    simpa only [map_sub, map_smul, map_one, ← hspec] using hA
  have hcp : (G.adjMatrix ℝ).charpoly = (Matrix.diagonal m).charpoly := by
    rw [hAconj]
    change (((hN.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal m) *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)).charpoly =
        (Matrix.diagonal m).charpoly
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hroots :
      (Finset.univ : Finset V).val.map (G.isHermitian_adjMatrix ℝ).eigenvalues =
        (Finset.univ : Finset V).val.map m := by
    calc
      _ = (G.adjMatrix ℝ).charpoly.roots := by
        simpa using (G.isHermitian_adjMatrix ℝ).roots_charpoly_eq_eigenvalues.symm
      _ = (Matrix.diagonal m).charpoly.roots :=
        congrArg (fun p : Polynomial ℝ => p.roots) hcp
      _ = (Finset.univ : Finset V).val.map m := by
        rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
        · simp
        · exact Finset.prod_ne_zero_iff.mpr
            (fun v _ => Polynomial.X_sub_C_ne_zero (m v))
  have hsum : (∑ v : V, m v) = 0 := by
    have h := congrArg Multiset.sum hroots
    simp only [Finset.sum_map_val] at h
    rw [← h]
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have henergy : (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) =
      ∑ v : V, |m v| := by
    have h := congrArg
      (fun s : Multiset ℝ => (s.map (fun x : ℝ => |x|)).sum) hroots
    simpa only [Multiset.map_map, Finset.sum_map_val, Function.comp_apply] using h
  have hPSD : N.PosSemidef :=
    (G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D
  have hnonneg (v : V) : 0 ≤ hN.eigenvalues v := by
    rw [hN.eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hN.eigenvectorBasis v))
  have hzero : (0 : ℝ) ∈ spectrum ℝ N := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := (1 : V → ℝ))
      ⟨Module.End.mem_genEigenspace_one.mpr ?_, by simp⟩
    simp only [Matrix.toLin'_apply, hNsmul, Matrix.smul_mulVec,
      G.lapMatrix_mulVec_one_eq_zero ℝ, smul_zero, zero_smul]
  rw [hN.spectrum_real_eq_range_eigenvalues] at hzero
  obtain ⟨z, hz⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let k : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  have heig (i : Fin (Fintype.card V)) :
      hN.eigenvalues (e i) = hN.eigenvalues₀ i := by
    simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]
  have hk0 : hN.eigenvalues₀ k = 0 := by
    have hk_nonneg : 0 ≤ hN.eigenvalues₀ k := by
      simpa only [heig] using hnonneg (e k)
    change hN.eigenvalues₀ (e.symm z) = 0 at hz
    have hzk : e.symm z ≤ k := by
      change (e.symm z).val ≤ Fintype.card V - 1
      have hzlt := (e.symm z).isLt
      omega
    exact le_antisymm ((hN.eigenvalues₀_antitone hzk).trans_eq hz) hk_nonneg
  have hmu_k : m (e k) = (d : ℝ) := by
    simp only [m, heig, hk0, sub_zero, mul_one]
  have hmu_j : m (e j) = (d : ℝ) * (1 - hN.eigenvalues₀ j) := by
    simp only [m, heig]
  have hne : e k ≠ e j := by
    intro h
    have hkj := e.injective h
    have hv := congrArg Fin.val hkj
    dsimp only [k, j] at hv
    omega
  have hpoint (v : V) : 0 ≤ |m v| + m v := by
    linarith [neg_abs_le (m v)]
  have hpair : (|m (e k)| + m (e k)) + (|m (e j)| + m (e j)) ≤
      ∑ v : V, (|m v| + m v) := by
    calc
      _ = ∑ v ∈ ({e k, e j} : Finset V), (|m v| + m v) :=
        (Finset.sum_pair hne).symm
      _ ≤ ∑ v : V, (|m v| + m v) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun v _ _ => hpoint v)
  simp only [Finset.sum_add_distrib, hsum, add_zero] at hpair
  simp only [hmu_k, hmu_j, abs_of_nonneg hdnonneg] at hpair
  rw [henergy]
  by_cases ht : 0 ≤ 1 - hN.eigenvalues₀ j
  · rw [max_eq_right ht]
    have hp : 0 ≤ (d : ℝ) * (1 - hN.eigenvalues₀ j) := mul_nonneg hdnonneg ht
    rw [abs_of_nonneg hp] at hpair
    nlinarith only [hpair]
  · have ht' : 1 - hN.eigenvalues₀ j ≤ 0 := (lt_of_not_ge ht).le
    rw [max_eq_left ht']
    have hp : (d : ℝ) * (1 - hN.eigenvalues₀ j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdnonneg ht'
    rw [abs_of_nonpos hp] at hpair
    nlinarith only [hpair]
