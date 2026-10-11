import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
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

theorem gutman_energy_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero]
    exact Finset.sum_nonneg (fun v _ => abs_nonneg _)
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
      (G.adjMatrix ℝ).toEuclideanLin
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
    let r : ℝ := sSup (Set.range f)
    have hT : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    have heig (i : V) : T (b i) = f i • b i := by
      apply WithLp.ofLp_injective 2
      change Matrix.mulVec (G.adjMatrix ℝ)
          (⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i •
          ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
      exact (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
    have hquad : inner ℝ (T x) x =
        ∑ i : V, f i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      apply Finset.sum_congr rfl
      intro i _
      rw [hT x (b i), heig i, real_inner_smul_right,
        real_inner_comm x (b i)]
      ring
    have hnorm : ‖x‖ ^ 2 = (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [x, PiLp.toLp_apply]
    have hcount : inner ℝ (T x) x = 2 * (G.edgeFinset.card : ℝ) := by
      calc
        inner ℝ (T x) x = ∑ v : V, (G.degree v : ℝ) := by
          rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
          change dotProduct
              (Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)))
              (star (fun _ : V => (1 : ℝ))) =
            ∑ v : V, (G.degree v : ℝ)
          simp [dotProduct]
        _ = 2 * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : inner ℝ (T x) x ≤ r * ‖x‖ ^ 2 := by
      rw [hquad, ← b.sum_sq_inner_right x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (le_csSup (Set.finite_range f).bddAbove ⟨i, rfl⟩)
        (sq_nonneg _)
    rw [hcount, hnorm] at hbound
    have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        (Fintype.card V : ℝ) ≤ r :=
      (div_le_iff₀ hcard).2 hbound
    have henergy : 2 * r ≤
        ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v| := by
      simpa only [r, f, if_neg hV] using graph_energy_spectral_radius_lower G
    rw [if_neg hV]
    exact (mul_le_mul_of_nonneg_left havg (by norm_num : (0 : ℝ) ≤ 2)).trans henergy

theorem gutman_energy_size_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  let b := (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  let x : V → V → ℝ := fun i v => b i v
  have hsq (v : V) : (∑ i : V, x i v ^ 2) = 1 := by
    simpa only [x, EuclideanSpace.basisFun_inner,
      (EuclideanSpace.basisFun V ℝ).orthonormal.1 v, one_pow] using
      b.sum_sq_inner_left ((EuclideanSpace.basisFun V ℝ) v)
  have heig (i : V) :
      (G.isHermitian_adjMatrix ℝ).eigenvalues i =
        ∑ u : V, ∑ v : V, if G.Adj u v then x i u * x i v else 0 := by
    simpa only [RCLike.re_to_real, dotProduct, Pi.star_apply, star_trivial,
      Matrix.mulVec_apply_eq_sum, SimpleGraph.adjMatrix_apply, ite_mul,
      one_mul, zero_mul, Finset.mul_sum, mul_ite, mul_zero, x, b] using
      (G.isHermitian_adjMatrix ℝ).eigenvalues_eq i
  have hbound (i : V) :
      |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤
        ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
    rw [heig i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun u _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases huv : G.Adj u v
    · simp only [if_pos huv, abs_mul]
      have h := two_mul_le_add_sq |x i u| |x i v|
      simp only [sq_abs] at h
      linarith only [h]
    · simp [huv]
  calc
    (∑ i : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|) ≤
        ∑ i : V, ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ u : V, ∑ v : V, ∑ i : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : G.Adj u v
      · simp only [if_pos huv]
        rw [← Finset.sum_div, Finset.sum_add_distrib, hsq u, hsq v]
        norm_num
      · simp only [if_neg huv, Finset.sum_const_zero]
    _ = ∑ u : V, (G.degree u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (G.degree_eq_sum_if_adj u).symm
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges

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

theorem hull3d_graph_energy_le_2_1_average_degree_nordhaus_gaddum_spectral_product_0_is_regular_7a6a403379a0 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    have hdnonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hmem : (d : ℝ) ∈ spectrum ℝ (G.adjMatrix ℝ) :=
      SimpleGraph.IsRegularOfDegree.mem_spectrum_adjMatrix (R := ℝ) (G := G) hd
    rw [(G.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hmem
    have hdle : (d : ℝ) ≤ sSup (Set.range f) :=
      le_csSup (Set.finite_range f).bddAbove hmem
    obtain ⟨i, hi⟩ := hmem
    change f i = (d : ℝ) at hi
    have hdlt : d < Fintype.card V := by
      simpa only [hd.degree_eq] using G.degree_lt_card_verts i
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
    have henergy : (∑ v : V, |f v|) ≤
        (d : ℝ) * ((Fintype.card V : ℝ) + 1 - (d : ℝ)) := by
      by_cases hd0 : d = 0
      · have hzero : (2 : ℝ) * (G.edgeFinset.card : ℝ) = 0 := by
          simpa [hd0] using hsum.symm
        have he :=
          hull3d_graph_energy_le_0_2_average_degree_size_0_is_regular_99710b2e7422
            G ⟨d, hd⟩
        simpa only [f, hd0, Nat.cast_zero, zero_mul] using
          he.trans (le_of_eq hzero)
      · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd0))
        have hnd : (d : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hdlt)
        have hpoly : (Fintype.card V : ℝ) - 1 ≤
            (d : ℝ) * ((Fintype.card V : ℝ) - (d : ℝ)) := by
          have hp : 0 ≤ ((d : ℝ) - 1) *
              ((Fintype.card V : ℝ) - (d : ℝ) - 1) :=
            mul_nonneg (sub_nonneg.mpr hd1) (by linarith)
          nlinarith only [hp]
        let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ)
          (G.isHermitian_adjMatrix ℝ).eigenvectorUnitary
        have hdiag : G.adjMatrix ℝ = C (Matrix.diagonal f) := by
          simpa [C, f] using (G.isHermitian_adjMatrix ℝ).spectral_theorem
        have hsq : (∑ v : V, f v ^ 2) =
            (Fintype.card V : ℝ) * (d : ℝ) := by
          calc
            (∑ v : V, f v ^ 2) =
                Matrix.trace (C (Matrix.diagonal f * Matrix.diagonal f)) := by
              dsimp only [C]
              rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
                Unitary.coe_star_mul_self, one_mul,
                Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
              simp only [pow_two]
            _ = Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) := by
              simp only [map_mul, ← hdiag]
            _ = (Fintype.card V : ℝ) * (d : ℝ) := by
              simp [Matrix.trace, Matrix.diag,
                G.adjMatrix_mul_self_apply_self, hd.degree_eq, nsmul_eq_mul]
        let s : Finset V := Finset.univ.erase i
        have hrestsq : (∑ v ∈ s, f v ^ 2) + (d : ℝ) ^ 2 =
            (Fintype.card V : ℝ) * (d : ℝ) := by
          simpa only [s, hi] using
            (Finset.sum_erase_add Finset.univ (fun v => f v ^ 2)
              (Finset.mem_univ i)).trans hsq
        have hrestabs : (∑ v ∈ s, |f v|) + (d : ℝ) =
            ∑ v : V, |f v| := by
          simpa only [s, hi, abs_of_nonneg hdnonneg] using
            (Finset.sum_erase_add Finset.univ (fun v => |f v|)
              (Finset.mem_univ i))
        have hcount_nat : s.card + 1 = Fintype.card V := by
          simpa only [s, Finset.card_univ] using
            (Finset.card_erase_add_one (Finset.mem_univ i))
        have hcount : (s.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
          exact_mod_cast hcount_nat
        have hb : (∑ v ∈ s, |f v|) ≤
            ((∑ v ∈ s, f v ^ 2) + (s.card : ℝ)) / 2 := by
          calc
            (∑ v ∈ s, |f v|) ≤ ∑ v ∈ s, (f v ^ 2 + 1) / 2 := by
              apply Finset.sum_le_sum
              intro v _
              nlinarith [sq_nonneg (|f v| - 1), sq_abs (f v)]
            _ = ((∑ v ∈ s, f v ^ 2) + (s.card : ℝ)) / 2 := by
              rw [← Finset.sum_div, Finset.sum_add_distrib]
              simp
        nlinarith only [hb, hrestsq, hrestabs, hcount, hpoly]
    let c : ℕ := Fintype.card V - 1 - d
    let fc : V → ℝ := (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues
    have hc : Gᶜ.IsRegularOfDegree c := hd.compl
    have hcmem : (c : ℝ) ∈ spectrum ℝ (Gᶜ.adjMatrix ℝ) :=
      SimpleGraph.IsRegularOfDegree.mem_spectrum_adjMatrix (R := ℝ) (G := Gᶜ) hc
    rw [(Gᶜ.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hcmem
    have hcle : (c : ℝ) ≤ sSup (Set.range fc) :=
      le_csSup (Set.finite_range fc).bddAbove hcmem
    have hprod : (d : ℝ) * (c : ℝ) ≤
        sSup (Set.range f) * sSup (Set.range fc) :=
      mul_le_mul hdle hcle (Nat.cast_nonneg c) (hdnonneg.trans hdle)
    have hdn : d ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hdlt
    have hone : 1 ≤ Fintype.card V :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hV)
    have hccast : (c : ℝ) = (Fintype.card V : ℝ) - 1 - (d : ℝ) := by
      dsimp only [c]
      rw [Nat.cast_sub hdn, Nat.cast_sub hone, Nat.cast_one]
    rw [hccast] at hprod
    simp only [if_neg hV, havg]
    change (∑ v : V, |f v|) ≤
      2 * (d : ℝ) + sSup (Set.range f) * sSup (Set.range fc)
    nlinarith only [henergy, hprod]

theorem model_081bc55d24f66b98c45d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2) ≤ ((2 : ℝ) * ((Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ))) := by
  classical
    let hA := G.isHermitian_adjMatrix ℝ
    let D : Matrix V V ℝ := Matrix.diagonal hA.eigenvalues
    let U := hA.eigenvectorUnitary
    have hspec : G.adjMatrix ℝ =
        Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U D := by
      simpa [D, U] using hA.spectral_theorem
    have htrace : Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
        ∑ v : V, hA.eigenvalues v ^ 2 := by
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U (D * D)) := by
          rw [map_mul, ← hspec]
        _ = Matrix.trace (D * D) := by
          rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, one_mul]
        _ = ∑ v : V, hA.eigenvalues v ^ 2 := by
          simp [D, Matrix.diagonal_mul_diagonal, pow_two]
    have hsquares : (∑ v : V, hA.eigenvalues v ^ 2) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      rw [← htrace]
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            ∑ v : V, (G.degree v : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply,
            G.adjMatrix_mul_self_apply_self]
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hCS : (∑ v : V, |hA.eigenvalues v|) ^ 2 ≤
        (Fintype.card V : ℝ) * ∑ v : V, hA.eigenvalues v ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, sq_abs] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ : V => (1 : ℝ)) (fun v => |hA.eigenvalues v|))
    rw [hsquares] at hCS
    calc
      _ ≤ (Fintype.card V : ℝ) * ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := hCS
      _ = _ := by ring

theorem mcclelland_graph_energy_upper {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  classical
  have hsq :
      (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2 ≤
        (2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)) := by
    calc
      _ ≤ (2 : ℝ) * ((Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ)) :=
        model_081bc55d24f66b98c45d G
      _ = _ := by ring
  calc
    _ ≤ |(∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)| :=
      le_abs_self _
    _ = Real.sqrt ((∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq
theorem hull3d_graph_energy_le__2_2_average_degree_size_2_is_regular_96b3eade117f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((((2 : ℝ) * (G.edgeFinset.card : ℝ)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (2 : ℝ)) := by
  classical
  have checked_1 := gutman_energy_size_bound G
  have checked_4 := hull3d_graph_energy_le_2_1_average_degree_nordhaus_gaddum_spectral_product_0_is_regular_7a6a403379a0 G h_guard
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, mul_zero, sub_zero]
    linarith only [checked_1]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨d, hd⟩ := h_guard
    have hspectral (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ) (hk : H.IsRegularOfDegree k) :
        sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) ≤ (k : ℝ) := by
      have hbound (i : V) : |(H.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (k : ℝ) := by
        let x : V → ℝ := ⇑((H.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
        have hx : x ≠ 0 :=
          (WithLp.ofLp_eq_zero 2).ne.2
            ((H.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
        obtain ⟨w, _, hw⟩ := Finset.exists_max_image Finset.univ (fun v => |x v|)
          ⟨j, Finset.mem_univ j⟩
        have hwpos : 0 < |x w| :=
          lt_of_lt_of_le (abs_pos.mpr hj) (hw j (Finset.mem_univ j))
        have heq : (∑ u ∈ H.neighborFinset w, x u) =
            (H.isHermitian_adjMatrix ℝ).eigenvalues i * x w := by
          simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
            congrFun ((H.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) w
        have hmul : |(H.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| ≤
            (k : ℝ) * |x w| := by
          calc
            |(H.isHermitian_adjMatrix ℝ).eigenvalues i| * |x w| =
                |∑ u ∈ H.neighborFinset w, x u| := by rw [heq, abs_mul]
            _ ≤ ∑ u ∈ H.neighborFinset w, |x u| :=
              Finset.abs_sum_le_sum_abs x (H.neighborFinset w)
            _ ≤ ∑ u ∈ H.neighborFinset w, |x w| :=
              Finset.sum_le_sum (fun u _ => hw u (Finset.mem_univ u))
            _ = (k : ℝ) * |x w| := by
              simp only [Finset.sum_const, H.card_neighborFinset_eq_degree,
                hk.degree_eq, nsmul_eq_mul]
        exact (mul_le_mul_iff_left₀ hwpos).mp hmul
      refine csSup_le (Set.range_nonempty _) ?_
      rintro t ⟨i, rfl⟩
      exact (le_abs_self _).trans (hbound i)
    have hr := hspectral G d hd
    let c : ℕ := Fintype.card V - 1 - d
    have hc : Gᶜ.IsRegularOfDegree c := hd.compl
    have hrc := hspectral Gᶜ c hc
    have hcmem : (c : ℝ) ∈ spectrum ℝ (Gᶜ.adjMatrix ℝ) :=
      SimpleGraph.IsRegularOfDegree.mem_spectrum_adjMatrix (R := ℝ) (G := Gᶜ) hc
    rw [(Gᶜ.isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hcmem
    have hrc_nonneg : 0 ≤ sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) :=
      (Nat.cast_nonneg c).trans
        (le_csSup (Set.finite_range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues).bddAbove hcmem)
    have hprod :
        sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) *
          sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) ≤
        (d : ℝ) * (c : ℝ) :=
      mul_le_mul hr hrc hrc_nonneg (Nat.cast_nonneg d)
    have hdlt : d < Fintype.card V := by
      simpa only [hd.degree_eq] using G.degree_lt_card_verts (Classical.arbitrary V)
    have hdn : d ≤ Fintype.card V - 1 := Nat.le_sub_one_of_lt hdlt
    have hone : 1 ≤ Fintype.card V :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hV)
    have hccast : (c : ℝ) = (Fintype.card V : ℝ) - 1 - (d : ℝ) := by
      dsimp only [c]
      rw [Nat.cast_sub hdn, Nat.cast_sub hone, Nat.cast_one]
    rw [hccast] at hprod
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
    have hpoly : 0 ≤ ((d : ℝ) - 1) * ((d : ℝ) - 2) := by
      by_cases hd0 : d = 0
      · norm_num [hd0]
      · by_cases hd1 : d = 1
        · norm_num [hd1]
        · have hd2 : (2 : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast (show 2 ≤ d by omega)
          exact mul_nonneg (by linarith) (by linarith)
    simp only [if_neg hV, havg] at checked_4 ⊢
    nlinarith only [checked_4, hprod, hsum, hpoly]
