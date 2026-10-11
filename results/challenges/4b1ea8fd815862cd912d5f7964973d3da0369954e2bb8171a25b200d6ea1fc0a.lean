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
  sorry
