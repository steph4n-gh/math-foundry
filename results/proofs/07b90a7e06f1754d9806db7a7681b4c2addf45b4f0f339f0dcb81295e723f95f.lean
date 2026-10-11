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

theorem model_5fd1e4b087f7c2ab56ec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    ((∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) - (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) ≥ (((Fintype.card V : ℝ) / (2 : ℝ)) * (((Real.exp (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (Real.exp (-(Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) - ((2 : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) := by
  classical
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    linarith only [h_guard.2.1]
  have hn0 : Fintype.card V ≠ 0 := by
    exact_mod_cast hnpos.ne'
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := hnpos.le
  have hnne : n ≠ 0 := hnpos.ne'
  let q : ℝ := 2 * (G.edgeFinset.card : ℝ) / n
  let r : ℝ := Real.sqrt q
  have hq : 0 ≤ q := by
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)) hn
  have hr : 0 ≤ r := Real.sqrt_nonneg q
  have hrsq : r ^ 2 = q := Real.sq_sqrt hq
  have hnq : n * q = 2 * (G.edgeFinset.card : ℝ) := by
    exact mul_div_cancel₀ _ hnne
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let U : Matrix.unitaryGroup V ℝ := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  have hspec : A = φ (Matrix.diagonal f) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
  have htr (B : Matrix V V ℝ) : Matrix.trace (φ B) = Matrix.trace B := by
    change Matrix.trace ((U : Matrix V V ℝ) * B *
      (star U : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have htrace (k : ℕ) : (∑ v : V, f v ^ k) = Matrix.trace (A ^ k) := by
    rw [hspec, ← map_pow, Matrix.diagonal_pow, htr, Matrix.trace_diagonal]
    simp only [Pi.pow_apply]
  have hentry (u v : V) : 0 ≤ A u v := by
    simp only [A, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hpow (k : ℕ) : ∀ u v : V, 0 ≤ (A ^ k) u v := by
    induction k with
    | zero =>
      intro u v
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
    | succ k ih =>
      intro u v
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (ih u w) (hentry w v))
  have hmoment (k : ℕ) : 0 ≤ ∑ v : V, f v ^ k := by
    rw [htrace k]
    exact Finset.sum_nonneg (fun v _ => hpow k v v)
  have hsquare : (∑ v : V, f v ^ 2) = n * q := by
    calc
      _ = Matrix.trace (A ^ 2) := htrace 2
      _ = ∑ v : V, (G.degree v : ℝ) := by
        simp only [A, pow_two, Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self]
      _ = 2 * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ = n * q := hnq.symm
  have hmean (k : ℕ) : n * q ^ k ≤ ∑ v : V, (f v ^ 2) ^ k := by
    calc
      n * q ^ k = ∑ v : V,
          (q ^ k + (k : ℝ) * q ^ (k - 1) * (f v ^ 2 - q)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hsquare]
        change n * q ^ k = n * q ^ k +
          (k : ℝ) * q ^ (k - 1) * (n * q - n * q)
        ring
      _ ≤ ∑ v : V, (f v ^ 2) ^ k := by
        apply Finset.sum_le_sum
        intro v _
        have hv : 0 ≤ 2 * q + (f v ^ 2 - q) := by
          nlinarith only [hq, sq_nonneg (f v)]
        simpa only [add_sub_cancel] using (pow_add_mul_le_add_pow hq hv k)
  have hE : (∑ v : V, |f v|) ≤ n * r := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset V) (fun _ => (1 : ℝ)) (fun v => |f v|)
    have hc' : (∑ v : V, |f v|) ^ 2 ≤ (n * r) ^ 2 := by
      calc
        _ ≤ n * (n * q) := by
          simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one, sq_abs, hsquare] using hc
        _ = (n * r) ^ 2 := by
          rw [mul_pow, hrsq]
          ring
    exact le_of_sq_le_sq hc' (mul_nonneg hn hr)
  have hexpseries (x : ℝ) :
      HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
    apply (Real.summable_pow_div_factorial x).hasSum_iff_tendsto_nat.mpr
    have hc : Filter.Tendsto
        (fun k : ℕ => ∑ i ∈ Finset.range k,
          (x : ℂ) ^ i / (Nat.factorial i : ℂ))
        Filter.atTop (nhds (Complex.exp (x : ℂ))) := by
      rw [Complex.exp]
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := (CauSeq.equiv_lim (Complex.exp' (x : ℂ))) ε hε
      refine ⟨N, fun k hk => ?_⟩
      rw [dist_eq_norm]
      change ‖(Complex.exp' (x : ℂ)) k - (Complex.exp' (x : ℂ)).lim‖ < ε
      exact hN k hk
    apply Filter.tendsto_ofReal_iff.mp
    simpa only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_exp] using hc
  have hcoeff (k : ℕ) :
      n / 2 * (r ^ k / (Nat.factorial k : ℝ) +
        (-r) ^ k / (Nat.factorial k : ℝ)) ≤
      (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) := by
    rcases Nat.even_or_odd k with he | ho
    · have hm : n * r ^ k ≤ ∑ v : V, f v ^ k := by
        obtain ⟨l, hl⟩ := even_iff_exists_two_mul.mp he
        simpa only [hl, pow_mul, hrsq] using hmean l
      calc
        _ = (n * r ^ k) / (Nat.factorial k : ℝ) := by
          rw [he.neg_pow]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)
    · rw [ho.neg_pow]
      have hf0 : 0 ≤ (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) :=
        div_nonneg (hmoment k) (Nat.cast_nonneg _)
      simpa only [neg_div, add_neg_cancel, mul_zero] using hf0
  have hserA :
      HasSum (fun k : ℕ => (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ))
        (∑ v : V, Real.exp (f v)) := by
    simpa only [Finset.sum_div] using
      (hasSum_sum (s := (Finset.univ : Finset V))
        (fun v _ => hexpseries (f v)))
  have hserR :
      HasSum (fun k : ℕ => n / 2 *
        (r ^ k / (Nat.factorial k : ℝ) + (-r) ^ k / (Nat.factorial k : ℝ)))
        (n / 2 * (Real.exp r + Real.exp (-r))) :=
    ((hexpseries r).add (hexpseries (-r))).mul_left (n / 2)
  have hEE : n / 2 * (Real.exp r + Real.exp (-r)) ≤
      ∑ v : V, Real.exp (f v) :=
    hasSum_le hcoeff hserR hserA
  simp only [if_neg hn0]
  change (∑ v : V, Real.exp (f v)) - (∑ v : V, |f v|) ≥
    n / 2 * (Real.exp r + Real.exp (-r) - 2 * r)
  nlinarith only [hEE, hE]

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
theorem model_be27f4e8aad2bd34983e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    ((∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) - (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) ≥ ((((Fintype.card V : ℝ) / (2 : ℝ)) * (((Real.exp (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (Real.exp (-(Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) - ((2 : ℝ) * (Real.sqrt (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))))) + ((((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * ((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (1 : ℝ))) / (16 : ℝ))) := by
  classical
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    linarith only [h_guard.2.1]
  have hn0 : Fintype.card V ≠ 0 := by
    exact_mod_cast hnpos.ne'
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := hnpos.le
  have hnne : n ≠ 0 := hnpos.ne'
  let q : ℝ := 2 * (G.edgeFinset.card : ℝ) / n
  let r : ℝ := Real.sqrt q
  have hq : 0 ≤ q := by
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _)) hn
  have hr : 0 ≤ r := Real.sqrt_nonneg q
  have hrsq : r ^ 2 = q := Real.sq_sqrt hq
  have hnq : n * q = 2 * (G.edgeFinset.card : ℝ) := by
    exact mul_div_cancel₀ _ hnne
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  simp only [if_neg hn0]
  change (∑ v : V, Real.exp (f v)) - (∑ v : V, |f v|) ≥
    n / 2 * (Real.exp r + Real.exp (-r) - 2 * r) + n * q * (q - 1) / 16
  by_cases hq1 : q ≤ 1
  · have hb := model_5fd1e4b087f7c2ab56ec G h_guard
    simp only [if_neg hn0] at hb
    change (∑ v : V, Real.exp (f v)) - (∑ v : V, |f v|) ≥
      n / 2 * (Real.exp r + Real.exp (-r) - 2 * r) at hb
    have hc : n * q * (q - 1) / 16 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hn hq)
          (sub_nonpos.mpr hq1)) (by norm_num)
    linarith only [hb, hc]
  have hqgt : 1 < q := lt_of_not_ge hq1
  have hrpos : 0 < r := by
    by_contra h
    have hz : r = 0 := le_antisymm (le_of_not_gt h) hr
    rw [hz] at hrsq
    norm_num at hrsq
    linarith only [hrsq, hqgt]
  have hmax_nat : G.maxDegree ≤ 2 := by
    by_contra h
    have hh : 3 ≤ G.maxDegree := by omega
    have hh' : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hh
    linarith only [hh', h_guard.2.2]
  have hmax : (G.maxDegree : ℝ) ≤ 2 := by exact_mod_cast hmax_nat
  have hdeg (v : V) : (G.degree v : ℝ) ≤ 2 := by
    have hh : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast G.degree_le_maxDegree v
    exact hh.trans hmax
  have hq2 : q ≤ 2 := by
    have hh : n * q ≤ n * 2 := by
      calc
        n * q = 2 * (G.edgeFinset.card : ℝ) := hnq
        _ ≤ n * (G.maxDegree : ℝ) := degree_sum_density_bound G
        _ ≤ n * 2 := mul_le_mul_of_nonneg_left hmax hn
    exact le_of_mul_le_mul_left hh hnpos
  have hrle : r ≤ 3 / 2 := by
    nlinarith only [hq2, hrsq, sq_nonneg (r - 3 / 2)]
  have hfe (i : V) : |f i| ≤ 2 := by
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    obtain ⟨w, _, hw⟩ := Finset.exists_max_image
      (Finset.univ : Finset V) (fun v => |x v|) Finset.univ_nonempty
    have hwpos : 0 < |x w| := by
      by_contra h
      have hwzero : |x w| = 0 :=
        le_antisymm (le_of_not_gt h) (abs_nonneg _)
      have hxzero : hA.eigenvectorBasis i = 0 := by
        apply WithLp.ofLp_injective 2
        funext v
        change x v = 0
        exact abs_eq_zero.mp
          (le_antisymm ((hw v (Finset.mem_univ v)).trans_eq hwzero)
            (abs_nonneg _))
      have hh : ‖hA.eigenvectorBasis i‖ = (1 : ℝ) :=
        hA.eigenvectorBasis.norm_eq_one i
      rw [hxzero, norm_zero] at hh
      norm_num at hh
    have he := congrFun (hA.mulVec_eigenvectorBasis i) w
    have he' : (∑ u ∈ G.neighborFinset w, x u) = f i * x w := by
      simpa only [A, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul, x, f] using he
    have hh : |f i| * |x w| ≤ 2 * |x w| := by
      calc
        _ = |∑ u ∈ G.neighborFinset w, x u| := by rw [he', abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset w, |x u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset w, |x w| :=
          Finset.sum_le_sum (fun u _ => hw u (Finset.mem_univ u))
        _ = (G.degree w : ℝ) * |x w| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ 2 * |x w| :=
          mul_le_mul_of_nonneg_right (hdeg w) (abs_nonneg _)
    exact le_of_mul_le_mul_right hh hwpos
  let U : Matrix.unitaryGroup V ℝ := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U
  have hspec : A = φ (Matrix.diagonal f) := by
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using hA.spectral_theorem
  have htr (B : Matrix V V ℝ) : Matrix.trace (φ B) = Matrix.trace B := by
    change Matrix.trace ((U : Matrix V V ℝ) * B *
      (star U : Matrix V V ℝ)) = Matrix.trace B
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
  have htrace (k : ℕ) : (∑ v : V, f v ^ k) = Matrix.trace (A ^ k) := by
    rw [hspec, ← map_pow, Matrix.diagonal_pow, htr, Matrix.trace_diagonal]
    simp only [Pi.pow_apply]
  have hentry (u v : V) : 0 ≤ A u v := by
    simp only [A, SimpleGraph.adjMatrix_apply]
    split <;> norm_num
  have hpow (k : ℕ) : ∀ u v : V, 0 ≤ (A ^ k) u v := by
    induction k with
    | zero =>
      intro u v
      simp only [pow_zero, Matrix.one_apply]
      split <;> norm_num
    | succ k ih =>
      intro u v
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun w _ => mul_nonneg (ih u w) (hentry w v))
  have hmoment (k : ℕ) : 0 ≤ ∑ v : V, f v ^ k := by
    rw [htrace k]
    exact Finset.sum_nonneg (fun v _ => hpow k v v)
  have hsumdeg : (∑ v : V, (G.degree v : ℝ)) = n * q := by
    calc
      _ = 2 * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      _ = n * q := hnq.symm
  have hsquare : (∑ v : V, f v ^ 2) = n * q := by
    calc
      _ = Matrix.trace (A ^ 2) := htrace 2
      _ = ∑ v : V, (G.degree v : ℝ) := by
        simp only [A, pow_two, Matrix.trace, Matrix.diag_apply,
          SimpleGraph.adjMatrix_mul_self_apply_self]
      _ = n * q := hsumdeg
  have hmean (k : ℕ) : n * q ^ k ≤ ∑ v : V, (f v ^ 2) ^ k := by
    calc
      n * q ^ k = ∑ v : V,
          (q ^ k + (k : ℝ) * q ^ (k - 1) * (f v ^ 2 - q)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hsquare]
        change n * q ^ k = n * q ^ k +
          (k : ℝ) * q ^ (k - 1) * (n * q - n * q)
        ring
      _ ≤ ∑ v : V, (f v ^ 2) ^ k := by
        apply Finset.sum_le_sum
        intro v _
        have hv : 0 ≤ 2 * q + (f v ^ 2 - q) := by
          nlinarith only [hq, sq_nonneg (f v)]
        simpa only [add_sub_cancel] using (pow_add_mul_le_add_pow hq hv k)
  have hrow (v : V) : (∑ w : V, A v w) = (G.degree v : ℝ) := by
    simpa only [A, SimpleGraph.adjMatrix_apply] using
      (G.degree_eq_sum_if_adj (R := ℝ) v).symm
  have hcol (v : V) : (∑ w : V, A w v) = (G.degree v : ℝ) := by
    calc
      _ = ∑ w : V, A v w := by
        apply Finset.sum_congr rfl
        intro w _
        exact (G.isSymm_adjMatrix (α := ℝ)).apply v w
      _ = (G.degree v : ℝ) := hrow v
  have hBsum : (∑ u : V, ∑ v : V, (A ^ 2) u v) =
      ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    calc
      _ = ∑ u : V, ∑ v : V, ∑ w : V, A u w * A w v := by
        simp only [pow_two, Matrix.mul_apply]
      _ = ∑ u : V, ∑ w : V, A u w * (∑ v : V, A w v) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ = ∑ w : V, (∑ u : V, A u w) * (G.degree w : ℝ) := by
        simp only [hrow]
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = ∑ v : V, (G.degree v : ℝ) ^ 2 := by
        simp only [hcol, pow_two]
  have hBdiag (u : V) : (A ^ 2) u u = (G.degree u : ℝ) := by
    simpa only [A, pow_two] using
      (G.adjMatrix_mul_self_apply_self (α := ℝ) u)
  have hBint (u v : V) : (A ^ 2) u v ≤ ((A ^ 2) u v) ^ 2 := by
    change (G.adjMatrix ℝ ^ 2) u v ≤ ((G.adjMatrix ℝ ^ 2) u v) ^ 2
    rw [G.adjMatrix_pow_apply_eq_card_walk 2 u v]
    let c : ℕ := Fintype.card {p : G.Walk u v | p.length = 2}
    change (c : ℝ) ≤ (c : ℝ) ^ 2
    have hc : c ≤ c ^ 2 := by
      by_cases hc0 : c = 0
      · simp [hc0]
      · have hc1 : 1 ≤ c := by omega
        simpa only [mul_one, pow_two] using Nat.mul_le_mul_left c hc1
    exact_mod_cast hc
  have hBsym : (A ^ 2).IsSymm := (G.isSymm_adjMatrix (α := ℝ)).pow 2
  have hfour_eq : (∑ v : V, f v ^ 4) =
      ∑ u : V, ∑ v : V, ((A ^ 2) u v) ^ 2 := by
    rw [htrace 4]
    have hp : A ^ 4 = A ^ 2 * A ^ 2 := pow_add A 2 2
    rw [hp]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hBsym.apply u v]
    exact (pow_two ((A ^ 2) u v)).symm
  have hfour : 2 * (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ≤
      ∑ v : V, f v ^ 4 := by
    calc
      _ = ∑ u : V, ∑ v : V,
          ((A ^ 2) u v +
            if u = v then (G.degree u : ℝ) ^ 2 - (G.degree u : ℝ) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
          Finset.mem_univ, ite_true]
        rw [hBsum, Finset.sum_sub_distrib, hsumdeg]
        ring
      _ ≤ ∑ u : V, ∑ v : V, ((A ^ 2) u v) ^ 2 := by
        apply Finset.sum_le_sum
        intro u _
        apply Finset.sum_le_sum
        intro v _
        by_cases huv : u = v
        · subst v
          rw [if_pos rfl, hBdiag u]
          nlinarith only []
        · rw [if_neg huv, add_zero]
          exact hBint u v
      _ = ∑ v : V, f v ^ 4 := hfour_eq.symm
  have hdsq : n * q ^ 2 ≤ ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    have hh : 0 ≤ ∑ v : V, ((G.degree v : ℝ) - q) ^ 2 :=
      Finset.sum_nonneg (fun v _ => sq_nonneg _)
    have heq : (∑ v : V, ((G.degree v : ℝ) - q) ^ 2) =
        (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ^ 2 := by
      have hp (v : V) : ((G.degree v : ℝ) - q) ^ 2 =
          (G.degree v : ℝ) ^ 2 - (2 * q) * (G.degree v : ℝ) + q ^ 2 := by ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (∑ v : V, (G.degree v : ℝ) ^ 2) -
        (2 * q) * (∑ v : V, (G.degree v : ℝ)) + n * q ^ 2 =
          (∑ v : V, (G.degree v : ℝ) ^ 2) - n * q ^ 2
      rw [hsumdeg]
      ring
    rw [heq] at hh
    linarith only [hh]
  let T : ℝ := ∑ v : V, (f v ^ 2 - q) ^ 2
  have hTid : T = (∑ v : V, f v ^ 4) - n * q ^ 2 := by
    dsimp only [T]
    have hp (v : V) : (f v ^ 2 - q) ^ 2 =
        f v ^ 4 - (2 * q) * (f v ^ 2) + q ^ 2 := by ring
    simp_rw [hp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ v : V, f v ^ 4) - (2 * q) * (∑ v : V, f v ^ 2) + n * q ^ 2 =
      (∑ v : V, f v ^ 4) - n * q ^ 2
    rw [hsquare]
    ring
  have hTlower : n * q * (q - 1) ≤ T := by
    rw [hTid]
    nlinarith only [hfour, hdsq]
  have hpoint (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
      t + (t ^ 2 - q) ^ 2 / 48 ≤ r + (t ^ 2 - q) / (2 * r) := by
    rw [← hrsq]
    have hsumsq : (t + r) ^ 2 ≤ 16 := by
      calc
        _ ≤ (4 : ℝ) ^ 2 := pow_le_pow_left₀ (add_nonneg ht0 hr)
          (by linarith only [ht2, hrle]) 2
        _ = 16 := by norm_num
    have hcap : r * (t + r) ^ 2 ≤ 24 := by
      calc
        _ ≤ r * 16 := mul_le_mul_of_nonneg_left hsumsq hr
        _ ≤ 24 := by linarith only [hrle]
    have hp : 0 ≤ (t - r) ^ 2 * (24 - r * (t + r) ^ 2) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hcap)
    have hh : t + (t ^ 2 - r ^ 2) ^ 2 / 48 - r ≤
        (t ^ 2 - r ^ 2) / (2 * r) := by
      apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrpos)).2
      nlinarith only [hp]
    linarith only [hh]
  have hE : (∑ v : V, |f v|) + T / 48 ≤ n * r := by
    have hh : (∑ v : V, (|f v| + (f v ^ 2 - q) ^ 2 / 48)) ≤
        ∑ v : V, (r + (f v ^ 2 - q) / (2 * r)) := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [sq_abs] using hpoint |f v| (abs_nonneg _) (hfe v)
    simp only [Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    change (∑ v : V, |f v|) + T / 48 ≤
      n * r + ((∑ v : V, f v ^ 2) - n * q) / (2 * r) at hh
    rw [hsquare, sub_self, zero_div, add_zero] at hh
    exact hh
  have hexpseries (x : ℝ) :
      HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
    apply (Real.summable_pow_div_factorial x).hasSum_iff_tendsto_nat.mpr
    have hc : Filter.Tendsto
        (fun k : ℕ => ∑ i ∈ Finset.range k,
          (x : ℂ) ^ i / (Nat.factorial i : ℂ))
        Filter.atTop (nhds (Complex.exp (x : ℂ))) := by
      rw [Complex.exp]
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := (CauSeq.equiv_lim (Complex.exp' (x : ℂ))) ε hε
      refine ⟨N, fun k hk => ?_⟩
      rw [dist_eq_norm]
      change ‖(Complex.exp' (x : ℂ)) k - (Complex.exp' (x : ℂ)).lim‖ < ε
      exact hN k hk
    apply Filter.tendsto_ofReal_iff.mp
    simpa only [Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_exp] using hc
  have hcoeff (k : ℕ) :
      n / 2 * (r ^ k / (Nat.factorial k : ℝ) +
        (-r) ^ k / (Nat.factorial k : ℝ)) ≤
      (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) := by
    rcases Nat.even_or_odd k with he | ho
    · have hm : n * r ^ k ≤ ∑ v : V, f v ^ k := by
        obtain ⟨l, hl⟩ := even_iff_exists_two_mul.mp he
        simpa only [hl, pow_mul, hrsq] using hmean l
      calc
        _ = (n * r ^ k) / (Nat.factorial k : ℝ) := by
          rw [he.neg_pow]
          ring
        _ ≤ _ := div_le_div_of_nonneg_right hm (Nat.cast_nonneg _)
    · rw [ho.neg_pow]
      have hf0 : 0 ≤ (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) :=
        div_nonneg (hmoment k) (Nat.cast_nonneg _)
      simpa only [neg_div, add_neg_cancel, mul_zero] using hf0
  have hcoeff' (k : ℕ) :
      n / 2 * (r ^ k / (Nat.factorial k : ℝ) +
        (-r) ^ k / (Nat.factorial k : ℝ)) +
        (if k = 4 then T / 24 else 0) ≤
      (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ) := by
    by_cases hk : k = 4
    · subst k
      apply le_of_eq
      rw [if_pos rfl]
      have hr4 : r ^ 4 = q ^ 2 := by
        calc
          _ = (r ^ 2) ^ 2 := by ring
          _ = q ^ 2 := by rw [hrsq]
      have hneg4 : (-r) ^ 4 = r ^ 4 := by ring
      rw [hneg4, hr4, hTid]
      norm_num [Nat.factorial] <;> ring
    · rw [if_neg hk, add_zero]
      exact hcoeff k
  have hserA :
      HasSum (fun k : ℕ => (∑ v : V, f v ^ k) / (Nat.factorial k : ℝ))
        (∑ v : V, Real.exp (f v)) := by
    simpa only [Finset.sum_div] using
      (hasSum_sum (s := (Finset.univ : Finset V))
        (fun v _ => hexpseries (f v)))
  have hserR :
      HasSum (fun k : ℕ => n / 2 *
        (r ^ k / (Nat.factorial k : ℝ) + (-r) ^ k / (Nat.factorial k : ℝ)))
        (n / 2 * (Real.exp r + Real.exp (-r))) :=
    ((hexpseries r).add (hexpseries (-r))).mul_left (n / 2)
  have hserR' :
      HasSum (fun k : ℕ => n / 2 *
        (r ^ k / (Nat.factorial k : ℝ) + (-r) ^ k / (Nat.factorial k : ℝ)) +
        (if k = 4 then T / 24 else 0))
        (n / 2 * (Real.exp r + Real.exp (-r)) + T / 24) :=
    hserR.add (hasSum_ite_eq (4 : ℕ) (T / 24))
  have hEE : n / 2 * (Real.exp r + Real.exp (-r)) + T / 24 ≤
      ∑ v : V, Real.exp (f v) :=
    hasSum_le hcoeff' hserR' hserA
  nlinarith only [hEE, hE, hTlower]
