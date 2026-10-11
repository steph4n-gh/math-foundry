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

theorem composed_b9a7629301cf0891 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  calc
    _ ≤ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) :=
      graph_energy_spectral_radius_lower G
    _ ≤ _ := mcclelland_graph_energy_upper G

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

theorem composed_a8305e0fa5e3ee71 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (Real.sqrt ((2 : ℝ) * ((G.edgeFinset.card : ℝ) * (Fintype.card V : ℝ)))) := by
  exact le_trans (spectral_spread_le_two_spectral_radius G) (composed_b9a7629301cf0891 G)

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

theorem composed_35ca49dcc0267544 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) := by
  exact le_trans (graph_energy_spectral_radius_lower G) (estrada_ge_energy G)

theorem composed_845382c1cbed672e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) := by
  apply le_trans (spectral_spread_le_two_spectral_radius G)
  exact composed_35ca49dcc0267544 G

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

theorem composed_5087f3d5606bb1bb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (((Fintype.card V : ℝ) / (2 : ℝ)) * ((1 : ℝ) + (Real.sqrt (Fintype.card V : ℝ)))) := by
  calc
    (2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))
        ≤ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) :=
      graph_energy_spectral_radius_lower G
    _ ≤ ((Fintype.card V : ℝ) / (2 : ℝ)) * (1 + Real.sqrt (Fintype.card V : ℝ)) :=
      koolen_moulton_order_2003 G

theorem composed_c07d062305bdb36b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (((Fintype.card V : ℝ) / (2 : ℝ)) * ((1 : ℝ) + (Real.sqrt (Fintype.card V : ℝ)))) := by
  exact le_trans (spectral_spread_le_two_spectral_radius G) (composed_5087f3d5606bb1bb G)

theorem composed_e72ee9accef18103 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  exact (spectral_spread_le_two_spectral_radius G).trans (graph_energy_spectral_radius_lower G)

theorem hull_normalized_laplacian_spectral_radius_le_0_complement_spectral_radius_2_b7beb0d09a33 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues))) ≤ (((0 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (2 : ℝ)) := by
  classical
  simp only [zero_mul, zero_add]
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let hA := Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  change (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range hA.eigenvalues)) ≤ 2
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    norm_num
  · rw [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    have hD : Matrix.conjTranspose D = D := by
      apply Matrix.IsHermitian.eq
      exact Matrix.isHermitian_diagonal_iff.mpr (fun i => IsSelfAdjoint.all _)
    have hL (y : V → ℝ) :
        dotProduct y (Matrix.mulVec (G.lapMatrix ℝ) y) ≤
          2 * ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
      have hr :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y a) ^ 2 else 0) =
            ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [G.degree_eq_sum_if_adj (R := ℝ) a]
        simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      have hc :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y b) ^ 2 else 0) =
            ∑ a : V, (G.degree a : ℝ) * (y a) ^ 2 := by
        rw [Finset.sum_comm]
        calc
          (∑ b : V, ∑ a : V, if G.Adj a b then (y b) ^ 2 else 0) =
              ∑ b : V, ∑ a : V, if G.Adj b a then (y b) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro a _
            simp only [G.adj_comm a b]
          _ = _ := hr
      have hb :
          (∑ a : V, ∑ b : V, if G.Adj a b then (y a - y b) ^ 2 else 0) ≤
            2 * (∑ a : V, ∑ b : V, if G.Adj a b then (y a) ^ 2 else 0) +
            2 * (∑ a : V, ∑ b : V, if G.Adj a b then (y b) ^ 2 else 0) := by
        simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        by_cases hab : G.Adj a b
        · simp only [if_pos hab]
          nlinarith only [sq_nonneg (y a + y b)]
        · simp only [if_neg hab, mul_zero, add_zero, le_refl]
      rw [hr, hc] at hb
      rw [← Matrix.toLinearMap₂'_apply', G.lapMatrix_toLinearMap₂' ℝ y]
      linarith only [hb]
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let x : EuclideanSpace ℝ V := hA.eigenvectorBasis i
    have hn : (∑ v : V, (x v) ^ 2) = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq x]
      simp only [x, OrthonormalBasis.norm_eq_one, one_pow]
    have hleft : Matrix.vecMul (⇑x) D = Matrix.mulVec D (⇑x) := by
      ext v
      simp only [D, Matrix.vecMul_diagonal, Matrix.mulVec_diagonal]
      exact mul_comm _ _
    have heig : hA.eigenvalues i =
        dotProduct (Matrix.mulVec D (⇑x))
          (Matrix.mulVec (G.lapMatrix ℝ) (Matrix.mulVec D (⇑x))) := by
      calc
        hA.eigenvalues i =
            dotProduct (⇑x)
              (Matrix.mulVec (D * G.lapMatrix ℝ * Matrix.conjTranspose D) (⇑x)) := by
          simpa only [x, star_trivial, RCLike.re_to_real] using hA.eigenvalues_eq i
        _ = _ := by
          rw [hD, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            Matrix.dotProduct_mulVec, hleft]
    have hweight :
        (∑ v : V, (G.degree v : ℝ) * ((Matrix.mulVec D (⇑x)) v) ^ 2) ≤ 1 := by
      calc
        _ ≤ ∑ v : V, (x v) ^ 2 := by
          apply Finset.sum_le_sum
          intro v _
          simp only [D, Matrix.mulVec_diagonal]
          by_cases hv : G.degree v = 0
          · simpa only [hv, Nat.cast_zero, zero_mul] using sq_nonneg (x v)
          · have hd : (G.degree v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hv
            have hs : (Real.sqrt (G.degree v : ℝ)) ^ 2 = (G.degree v : ℝ) :=
              Real.sq_sqrt (Nat.cast_nonneg (G.degree v))
            simp only [mul_pow, ← mul_assoc, inv_pow, hs,
              mul_inv_cancel₀ hd, one_mul, le_refl]
        _ = 1 := hn
    have hquad := hL (Matrix.mulVec D (⇑x))
    rw [← heig] at hquad
    linarith only [hquad, hweight]

theorem hull_normalized_laplacian_spectral_radius_le_1_spectral_spread_0_fd06095fa69d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues))) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let hL := Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  let r : ℝ := sSup (Set.range f)
  let l : ℝ := sInf (Set.range f)
  change (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range hL.eigenvalues)) ≤
    (if Fintype.card V = 0 then (0 : ℝ) else r) -
      (if Fintype.card V = 0 then (0 : ℝ) else l)
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · simp only [if_neg hn]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    by_cases hG : G = ⊥
    · have hAdj : A = 0 := by
        subst G
        ext i j
        simp [A, SimpleGraph.adjMatrix]
      have hLap : D * G.lapMatrix ℝ * Matrix.conjTranspose D = 0 := by
        subst G
        have hdeg : (⊥ : SimpleGraph V).degMatrix ℝ = 0 := by
          simp only [SimpleGraph.degMatrix, SimpleGraph.degree,
            SimpleGraph.neighborFinset_bot, Finset.card_empty,
            Nat.cast_zero, Matrix.diagonal_zero]
        change D * ((⊥ : SimpleGraph V).degMatrix ℝ - A) *
          Matrix.conjTranspose D = 0
        rw [hdeg, hAdj, sub_self, Matrix.mul_zero, Matrix.zero_mul]
      have hf : f = 0 := hA.eigenvalues_eq_zero_iff.mpr hAdj
      have hfL : hL.eigenvalues = 0 := hL.eigenvalues_eq_zero_iff.mpr hLap
      simp [r, l, hf, hfL, Pi.zero_def, Set.range_const]
    · obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
      let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
      have hspec : C (Matrix.diagonal f) = A := by
        simpa only [f, RCLike.ofReal_real_eq_id, Function.id_comp] using
          hA.spectral_theorem.symm
      have hpos (c d : ℝ) (hcd : ∀ i : V, 0 ≤ c * f i + d) :
          (c • A + d • (1 : Matrix V V ℝ)).PosSemidef := by
        have hd : (c • Matrix.diagonal f + d • (1 : Matrix V V ℝ)).PosSemidef := by
          rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul,
            ← Matrix.diagonal_smul, Matrix.diagonal_add]
          apply Matrix.PosSemidef.diagonal
          intro i
          simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
            smul_eq_mul, mul_one] using hcd i
        have heq : c • A + d • (1 : Matrix V V ℝ) =
            C (c • Matrix.diagonal f + d • (1 : Matrix V V ℝ)) := by
          rw [map_add, map_smul, map_smul, map_one, hspec]
        rw [heq]
        change ((hA.eigenvectorUnitary : Matrix V V ℝ) *
          (c • Matrix.diagonal f + d • (1 : Matrix V V ℝ)) *
          Matrix.conjTranspose (hA.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
        exact hd.mul_mul_conjTranspose_same _
      have hupper : ((-1 : ℝ) • A + r • (1 : Matrix V V ℝ)).PosSemidef := by
        apply hpos
        intro i
        have hi : f i ≤ r :=
          le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self i)
        linarith only [hi]
      have hlower : ((1 : ℝ) • A + (-l) • (1 : Matrix V V ℝ)).PosSemidef := by
        apply hpos
        intro i
        have hi : l ≤ f i :=
          csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self i)
        linarith only [hi]
      let p : V → ℝ := Pi.single u 1 + Pi.single v 1
      let q : V → ℝ := Pi.single u 1 - Pi.single v 1
      have hp : dotProduct p p = 2 := by
        norm_num [p, Pi.single_apply, huv.ne, huv.ne']
      have hq : dotProduct q q = 2 := by
        norm_num [q, Pi.single_apply, huv.ne, huv.ne']
      have hAp : dotProduct p (Matrix.mulVec A p) = 2 := by
        dsimp only [p]
        rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
        norm_num [Matrix.col_apply, A, huv, huv.symm]
      have hAq : dotProduct q (Matrix.mulVec A q) = -2 := by
        dsimp only [q]
        rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one]
        norm_num [Matrix.col_apply, A, huv, huv.symm]
      have hr := hupper.dotProduct_mulVec_nonneg p
      simp only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
        hAp, hp, smul_eq_mul] at hr
      have hl := hlower.dotProduct_mulVec_nonneg q
      simp only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
        hAq, hq, smul_eq_mul] at hl
      have hnorm : sSup (Set.range hL.eigenvalues) ≤ 2 := by
        simpa only [if_neg hn, zero_mul, zero_add] using
          hull_normalized_laplacian_spectral_radius_le_0_complement_spectral_radius_2_b7beb0d09a33 G
      linarith only [hnorm, hr, hl]

theorem hull_spectral_spread_le_1_nordhaus_gaddum_spectral_sum_1_1136dbf5ed1c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · simp only [if_neg hn]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let B : Matrix V V ℝ := Gᶜ.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let hB : B.IsHermitian := Gᶜ.isHermitian_adjMatrix ℝ
    let b : ℝ := sSup (Set.range hB.eigenvalues)
    have hb : ∀ i, hB.eigenvalues i ≤ b := by
      intro i
      exact le_csSup (Set.finite_range hB.eigenvalues).bddAbove (Set.mem_range_self i)
    have hd : (b • (1 : Matrix V V ℝ) -
        Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)).PosSemidef := by
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
      apply Matrix.PosSemidef.diagonal
      intro i
      simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        mul_one, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
        using sub_nonneg.mpr (hb i)
    let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hB.eigenvectorUnitary
    have hC : C (Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) = B :=
      hB.spectral_theorem.symm
    have heq : b • (1 : Matrix V V ℝ) - B =
        C (b • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) := by
      rw [map_sub, map_smul, map_one, hC]
    have hBbound : (b • (1 : Matrix V V ℝ) - B).PosSemidef := by
      rw [heq]
      change ((hB.eigenvectorUnitary : Matrix V V ℝ) *
        (b • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues)) *
        Matrix.conjTranspose (hB.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
      exact hd.mul_mul_conjTranspose_same _
    have hJ : (Matrix.of 1 : Matrix V V ℝ).PosSemidef := by
      have heqJ : (Matrix.of 1 : Matrix V V ℝ) =
          Matrix.vecMulVec (fun _ : V => (1 : ℝ))
            (star (fun _ : V => (1 : ℝ))) := by
        ext i j
        simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.one_apply,
          star_trivial, mul_one]
      rw [heqJ]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : V => (1 : ℝ))
    have hsum : (1 : Matrix V V ℝ) + A + B = Matrix.of 1 := by
      simpa only [A, B, G.compl_adjMatrix_eq_adjMatrix_compl ℝ] using
        G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    have hs : (A + (b + 1) • (1 : Matrix V V ℝ)).PosSemidef := by
      have heq' : A + (b + 1) • (1 : Matrix V V ℝ) =
          Matrix.of 1 + (b • (1 : Matrix V V ℝ) - B) := by
        rw [← hsum, add_smul, one_smul]
        abel
      rw [heq']
      exact hJ.add hBbound
    have hlower : ∀ i : V, -(b + 1) ≤ hA.eigenvalues i := by
      intro i
      let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
      have hx : dotProduct x x = 1 := by
        have h := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i i
        rw [if_pos rfl] at h
        simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using h
      have heig : Matrix.mulVec A x = hA.eigenvalues i • x :=
        hA.mulVec_eigenvectorBasis i
      have hnonneg : 0 ≤ hA.eigenvalues i + (b + 1) := by
        simpa only [star_trivial, Matrix.add_mulVec, Matrix.smul_mulVec,
          Matrix.one_mulVec, heig, dotProduct_add, dotProduct_smul,
          hx, smul_eq_mul, mul_one] using hs.dotProduct_mulVec_nonneg x
      linarith
    have hmin : -(b + 1) ≤ sInf (Set.range hA.eigenvalues) := by
      apply le_csInf (Set.range_nonempty hA.eigenvalues)
      rintro y ⟨i, rfl⟩
      exact hlower i
    change -(sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) + 1) ≤
      sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) at hmin
    linarith
theorem hull_spectral_spread_le_2_sqrt_size_0_fe80d135635b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * (Real.sqrt (G.edgeFinset.card : ℝ))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let hA := G.isHermitian_adjMatrix ℝ
    let f : V → ℝ := hA.eigenvalues
    let D : Matrix V V ℝ := Matrix.diagonal f
    let U := hA.eigenvectorUnitary
    have hspec : G.adjMatrix ℝ =
        Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U D := by
      simpa [D, U, f] using hA.spectral_theorem
    have htrace : Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
        ∑ v : V, f v ^ 2 := by
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U (D * D)) := by
          rw [map_mul, ← hspec]
        _ = Matrix.trace (D * D) := by
          rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, one_mul]
        _ = ∑ v : V, f v ^ 2 := by
          simp [D, Matrix.diagonal_mul_diagonal, pow_two]
    have hsquares : (∑ v : V, f v ^ 2) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      rw [← htrace]
      calc
        Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
            ∑ v : V, (G.degree v : ℝ) := by
          simp only [Matrix.trace, Matrix.diag_apply,
            G.adjMatrix_mul_self_apply_self]
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    obtain ⟨u, hu⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csInf_mem (Set.finite_range f)
    change sSup (Set.range f) - sInf (Set.range f) ≤
      2 * Real.sqrt (G.edgeFinset.card : ℝ)
    rw [← hu, ← hv]
    by_cases huv : u = v
    · subst v
      simpa only [sub_self] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Real.sqrt_nonneg (G.edgeFinset.card : ℝ))
    · have hpair : f u ^ 2 + f v ^ 2 ≤ ∑ w : V, f w ^ 2 := by
        calc
          f u ^ 2 + f v ^ 2 = ∑ w ∈ ({u, v} : Finset V), f w ^ 2 := by
            simp [huv]
          _ ≤ ∑ w : V, f w ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun w _ _ => sq_nonneg (f w))
      rw [hsquares] at hpair
      have hsqrt : (Real.sqrt (G.edgeFinset.card : ℝ)) ^ 2 =
          (G.edgeFinset.card : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      have hbound : (f u - f v) ^ 2 ≤
          (2 * Real.sqrt (G.edgeFinset.card : ℝ)) ^ 2 := by
        nlinarith only [hpair, hsqrt, sq_nonneg (f u + f v)]
      exact le_of_sq_le_sq hbound
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (Real.sqrt_nonneg (G.edgeFinset.card : ℝ)))
