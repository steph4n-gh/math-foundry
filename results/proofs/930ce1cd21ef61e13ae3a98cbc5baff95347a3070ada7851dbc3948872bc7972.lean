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

theorem spectral_spread_le_two_spectral_radius {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    change r - sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) ≤ 2 * r
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
    have hcoord (z : EuclideanSpace ℝ V) :
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin z) z =
          ∑ v : V, ∑ w ∈ G.neighborFinset v, z v * z w := by
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [WithLp.ofLp_toLp, star_trivial]
      change (∑ v : V, z v * Matrix.mulVec (G.adjMatrix ℝ) (fun w => z w) v) = _
      simp only [SimpleGraph.adjMatrix_mulVec_apply, Finset.mul_sum]
    have hlower (i : V) : -r ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
      let y : EuclideanSpace ℝ V := WithLp.toLp 2 (fun v => |b i v|)
      have hnormy : inner ℝ y y = 1 := by
        calc
          inner ℝ y y = inner ℝ (b i) (b i) := by
            simp only [EuclideanSpace.inner_eq_star_dotProduct, y,
              WithLp.ofLp_toLp, star_trivial]
            change (∑ v : V, |b i v| * |b i v|) =
              (∑ v : V, b i v * b i v)
            simp only [abs_mul_abs_self]
          _ = 1 := b.inner_eq_one i
      have heigen : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) =
          (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
        rw [heig i, real_inner_smul_left, b.inner_eq_one i, mul_one]
      have habs :
          -inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) ≤
            inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y := by
        simp only [hcoord]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro v hv
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro w hw
        change -(b i v * b i w) ≤ |b i v| * |b i w|
        rw [← abs_mul]
        exact neg_le_abs _
      have hy : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y ≤ r := by
        simpa only [hnormy, mul_one] using hq y
      have hneg := habs.trans hy
      rw [heigen] at hneg
      linarith only [hneg]
    have hmin : -r ≤ sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      exact hlower i
    linarith only [hmin]

theorem composed_e72ee9accef18103 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  exact (spectral_spread_le_two_spectral_radius G).trans (graph_energy_spectral_radius_lower G)

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

theorem koolen_moulton_order_2003 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (((Fintype.card V : ℝ) / (2 : ℝ)) * ((1 : ℝ) + (Real.sqrt (Fintype.card V : ℝ)))) := by
  classical
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let U : Matrix.unitaryGroup V ℝ := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  let s : V → ℝ := fun i => if 0 ≤ f i then 1 else -1
  let S : Matrix V V ℝ := φ (Matrix.diagonal s)
  let N : ℝ := Fintype.card V
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hs (i : V) : s i * s i = 1 := by
    by_cases hi : 0 ≤ f i <;> simp [s, hi]
  have hsabs (i : V) : f i * s i = |f i| := by
    by_cases hi : 0 ≤ f i
    · simp [s, hi, abs_of_nonneg hi]
    · simp [s, hi, abs_of_neg (lt_of_not_ge hi)]
  have htr (B : Matrix V V ℝ) : Matrix.trace (φ B) = Matrix.trace B := by
    change Matrix.trace ((U : Matrix V V ℝ) * B *
      (star U : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hSS : S * S = 1 := by
    have hd : Matrix.diagonal s * Matrix.diagonal s = (1 : Matrix V V ℝ) := by
      simp only [Matrix.diagonal_mul_diagonal, hs, Matrix.diagonal_one]
    change φ (Matrix.diagonal s) * φ (Matrix.diagonal s) = 1
    rw [← map_mul, hd, map_one]
  have hST : Matrix.transpose S = S := by
    have hstar : star S = S := by
      change star (φ (Matrix.diagonal s)) = φ (Matrix.diagonal s)
      rw [← map_star, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, star_trivial]
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hstar
  have hsym (i j : V) : S j i = S i j :=
    congrFun (congrFun hST i) j
  have henergy : Matrix.trace (A * S) = ∑ i : V, |f i| := by
    have hspec : A = φ (Matrix.diagonal f) := by
      simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
    calc
      Matrix.trace (A * S) =
          Matrix.trace (φ (Matrix.diagonal f * Matrix.diagonal s)) := by
        rw [hspec]
        change Matrix.trace (φ (Matrix.diagonal f) * φ (Matrix.diagonal s)) =
          Matrix.trace (φ (Matrix.diagonal f * Matrix.diagonal s))
        rw [map_mul]
      _ = Matrix.trace (Matrix.diagonal f * Matrix.diagonal s) := htr _
      _ = ∑ i : V, |f i| := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, hsabs]
  have hSsq : (∑ i : V, ∑ j : V, (S i j) ^ 2) = N := by
    calc
      (∑ i : V, ∑ j : V, (S i j) ^ 2) = Matrix.trace (S * S) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym i j, pow_two]
      _ = N := by simpa only [hSS, Matrix.trace_one, N]
  let r : V → ℝ := fun i => ∑ j : V, S i j
  have hr : (∑ i : V, (r i) ^ 2) = N := by
    let x : V → ℝ := fun _ => 1
    have hx : Matrix.mulVec S x = r := by
      funext i
      simp [Matrix.mulVec, dotProduct, x, r]
    calc
      (∑ i : V, (r i) ^ 2) =
          dotProduct (Matrix.mulVec S x) (Matrix.mulVec S x) := by
        rw [hx]
        simp only [dotProduct, pow_two]
      _ = dotProduct x (Matrix.mulVec (Matrix.transpose S) (Matrix.mulVec S x)) :=
        (Matrix.dotProduct_transpose_mulVec S x (Matrix.mulVec S x)).symm
      _ = dotProduct x x := by
        rw [Matrix.mulVec_mulVec, hST, hSS, Matrix.one_mulVec]
      _ = N := by simp [dotProduct, x, N]
  have hJ : (∑ i : V, r i) ≤ N := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset V) (fun _ => (1 : ℝ)) r
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, hr] at hc
    have hsq : (∑ i : V, r i) ^ 2 ≤ N ^ 2 := by
      simpa only [pow_two] using hc
    exact le_of_sq_le_sq hsq hN
  let B : Matrix V V ℝ := Matrix.of (fun i j => A i j - (1 / 2 : ℝ))
  have hBentry (i j : V) : (B i j) ^ 2 = (1 / 4 : ℝ) := by
    change (G.adjMatrix ℝ i j - (1 / 2 : ℝ)) ^ 2 = (1 / 4 : ℝ)
    rcases (G.isAdjMatrix_adjMatrix ℝ).zero_or_one i j with hij | hij
      <;> rw [hij] <;> norm_num
  have hBsqPair : (∑ p : V × V, (B p.1 p.2) ^ 2) = (N / 2) ^ 2 := by
    calc
      (∑ p : V × V, (B p.1 p.2) ^ 2) = (N * N) * (1 / 4 : ℝ) := by
        simp only [hBentry, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_prod, Nat.cast_mul, N]
      _ = (N / 2) ^ 2 := by ring
  have hSsqPair : (∑ p : V × V, (S p.1 p.2) ^ 2) = N := by
    simpa only [Fintype.sum_prod_type] using hSsq
  let C : ℝ := ∑ p : V × V, B p.1 p.2 * S p.1 p.2
  have hC : C ≤ N / 2 * Real.sqrt N := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (V × V))
      (fun p => B p.1 p.2) (fun p => S p.1 p.2)
    have hsq : C ^ 2 ≤ (N / 2 * Real.sqrt N) ^ 2 := by
      calc
        C ^ 2 ≤ (N / 2) ^ 2 * N := by
          simpa only [hBsqPair, hSsqPair] using hc
        _ = (N / 2 * Real.sqrt N) ^ 2 := by
          symm
          rw [mul_pow, Real.sq_sqrt hN]
    exact le_of_sq_le_sq hsq
      (mul_nonneg (div_nonneg hN (by norm_num)) (Real.sqrt_nonneg N))
  have hdecomp : (∑ i : V, |f i|) = C + (1 / 2 : ℝ) * (∑ i : V, r i) := by
    rw [← henergy]
    calc
      Matrix.trace (A * S) = ∑ i : V, ∑ j : V, A i j * S i j := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym i j]
      _ = (∑ i : V, ∑ j : V, B i j * S i j) +
          (1 / 2 : ℝ) * (∑ i : V, ∑ j : V, S i j) := by
        have hterm (i j : V) :
            A i j * S i j = B i j * S i j + (1 / 2 : ℝ) * S i j := by
          change A i j * S i j =
            (A i j - (1 / 2 : ℝ)) * S i j + (1 / 2 : ℝ) * S i j
          ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = C + (1 / 2 : ℝ) * (∑ i : V, r i) := by
        simp only [C, r, Fintype.sum_prod_type]
  change (∑ i : V, |f i|) ≤ N / 2 * (1 + Real.sqrt N)
  calc
    (∑ i : V, |f i|) = C + (1 / 2 : ℝ) * (∑ i : V, r i) := hdecomp
    _ ≤ N / 2 * Real.sqrt N + (1 / 2 : ℝ) * N :=
      add_le_add hC (mul_le_mul_of_nonneg_left hJ (by norm_num))
    _ = N / 2 * (1 + Real.sqrt N) := by ring

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

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

theorem composed_1f7e49d87d42f727 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) := gutman_energy_size_bound G
    _ ≤ (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := degree_sum_density_bound G
theorem model_6bde2f687ba9b3e6e8a5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ (max (((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((1 : ℝ) + (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))))) ((((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * (((Fintype.card V : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))) / (max (1 : ℝ) ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) + ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) * (max (0 : ℝ) ((1 : ℝ) - (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))))))) := by
  classical
  refine max_le (model_f1abeb346d4f50c57240 G h_guard) ?_
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
      (((Fintype.card V : ℝ) -
          (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
        ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
          max 0 (1 - hN.eigenvalues₀ j)) /
      max 1
        ((sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) -
            (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) +
          ((2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) *
            max 0 (1 - hN.eigenvalues₀ j))
  simp only [havg]
  by_cases hd0 : d = 0
  · simp only [hd0, Nat.cast_zero, mul_zero, zero_mul, zero_div]
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
  have hrange : Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues =
      Set.range m := by
    ext x
    have hx := congrArg (fun s : Multiset ℝ => x ∈ s) hroots
    simpa only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and, Set.mem_range] using (Iff.of_eq hx)
  have htr (B : Matrix V V ℝ) : Matrix.trace (U B) = Matrix.trace B := by
    change Matrix.trace ((hN.eigenvectorUnitary : Matrix V V ℝ) * B *
      (star hN.eigenvectorUnitary : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hAA : G.adjMatrix ℝ * G.adjMatrix ℝ =
      U (Matrix.diagonal m * Matrix.diagonal m) := by
    rw [map_mul, ← hAconj]
  have hsquare : (∑ v : V, m v ^ 2) =
      (Fintype.card V : ℝ) * (d : ℝ) := by
    calc
      _ = Matrix.trace (Matrix.diagonal m * Matrix.diagonal m) := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]
      _ = Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) := by
        rw [hAA, htr]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self, hd.degree_eq,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
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
  have hupper (v : V) : m v ≤ (d : ℝ) := by
    have hp := mul_nonneg hdnonneg (hnonneg v)
    dsimp only [m]
    nlinarith only [hp]
  have hmax : sSup (Set.range m) = (d : ℝ) := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty m)
      rintro x ⟨v, rfl⟩
      exact hupper v
    · rw [← hmu_k]
      exact le_csSup (Set.finite_range m).bddAbove ⟨e k, rfl⟩
  let a : ℝ := (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
  let b : ℝ := -sInf (Set.range m)
  let E : ℝ := ∑ v : V, |m v|
  have hEnonneg : 0 ≤ E := Finset.sum_nonneg (fun v _ => abs_nonneg _)
  have hlower (v : V) : -b ≤ m v := by
    simpa only [b, neg_neg] using
      (csInf_le (Set.finite_range m).bddBelow
        (show m v ∈ Set.range m from ⟨v, rfl⟩))
  have hcap (v : V) (hv : v ≠ e k) : m v ≤ a := by
    have hidx : e.symm v ≠ k := by
      intro hi
      apply hv
      simpa only [Equiv.apply_symm_apply] using congrArg e hi
    have hi : e.symm v ≤ j := by
      have hlt := (e.symm v).isLt
      have hval : (e.symm v).val ≠ Fintype.card V - 1 := by
        intro h
        exact hidx (Fin.ext h)
      change (e.symm v).val ≤ Fintype.card V - 2
      omega
    have hEigOrder := hN.eigenvalues₀_antitone hi
    change hN.eigenvalues₀ j ≤ hN.eigenvalues v at hEigOrder
    change (d : ℝ) * (1 - hN.eigenvalues v) ≤
      (d : ℝ) * max 0 (1 - hN.eigenvalues₀ j)
    exact mul_le_mul_of_nonneg_left
      ((sub_le_sub_left hEigOrder 1).trans (le_max_right _ _)) hdnonneg
  have hpoint (v : V) : m v ^ 2 ≤
      (a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
        (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0) := by
    by_cases hv : v = e k
    · rw [hv, if_pos rfl, hmu_k, abs_of_nonneg hdnonneg]
      nlinarith only []
    · rw [if_neg hv, add_zero]
      by_cases hm : 0 ≤ m v
      · rw [abs_of_nonneg hm]
        have hp := mul_nonneg (sub_nonneg.mpr (hcap v hv)) hm
        nlinarith only [hp]
      · have hm' : m v ≤ 0 := (lt_of_not_ge hm).le
        rw [abs_of_nonpos hm']
        have hp := mul_nonneg
          (show 0 ≤ m v + b by linarith only [hlower v])
          (neg_nonneg.mpr hm')
        nlinarith only [hp]
  have hquad : (Fintype.card V : ℝ) * (d : ℝ) ≤
      (a + b) * E / 2 + (d : ℝ) ^ 2 - a * (d : ℝ) := by
    calc
      _ = ∑ v : V, m v ^ 2 := hsquare.symm
      _ ≤ ∑ v : V,
          ((a * (|m v| + m v) + b * (|m v| - m v)) / 2 +
            (if v = e k then (d : ℝ) ^ 2 - a * (d : ℝ) else 0)) :=
        Finset.sum_le_sum (fun v _ => hpoint v)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_div, ← Finset.mul_sum, hsum, add_zero, sub_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, E]
        ring
  have hmono : (b + a) * E ≤ max 1 (b + a) * E :=
    mul_le_mul_of_nonneg_right (le_max_right 1 (b + a)) hEnonneg
  have hprod : (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) ≤
      E * max 1 (b + a) := by
    nlinarith only [hquad, hmono]
  have hdenpos : (0 : ℝ) < max 1 (b + a) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 (b + a))
  have hsecond :
      (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
        max 1 (b + a) ≤ E :=
    (div_le_iff₀ hdenpos).2 hprod
  rw [henergy, hrange, hmax]
  change E ≥
    (2 * (d : ℝ)) * (((Fintype.card V : ℝ) - (d : ℝ)) + a) /
      max 1 (((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a)
  have hdenexpr : ((d : ℝ) - sInf (Set.range m) - (d : ℝ)) + a = b + a := by
    dsimp only [b]
    ring
  rw [hdenexpr]
  exact hsecond
