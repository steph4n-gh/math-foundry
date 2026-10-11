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

theorem model_c71b19aef6e373b1bdc9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.edgeFinset.card : ℝ) ≥ (9999999 / 10000000 : ℝ))) :
    (((2 : ℝ) * (G.edgeFinset.card : ℝ)) - (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|)) ≥ (((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) - (2 : ℝ)) ^ 2) / (2 : ℝ)) := by
  classical
  let hA := G.isHermitian_adjMatrix ℝ
  let f : V → ℝ := hA.eigenvalues
  have hsum : (∑ i : V, f i) = 0 := by
    simpa [f, hA] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  let D : Matrix V V ℝ := Matrix.diagonal f
  let U := hA.eigenvectorUnitary
  have hspec : G.adjMatrix ℝ =
      Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U D := by
    simpa [D, U, f] using hA.spectral_theorem
  have htrace : Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
      ∑ i : V, f i ^ 2 := by
    calc
      Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
          Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) U (D * D)) := by
        rw [map_mul, ← hspec]
      _ = Matrix.trace (D * D) := by
        rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self, one_mul]
      _ = ∑ i : V, f i ^ 2 := by
        simp [D, Matrix.diagonal_mul_diagonal, pow_two]
  have hsquares : (∑ i : V, f i ^ 2) =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    rw [← htrace]
    calc
      Matrix.trace (G.adjMatrix ℝ * G.adjMatrix ℝ) =
          ∑ i : V, (G.degree i : ℝ) := by
        simp only [Matrix.trace, Matrix.diag_apply,
          G.adjMatrix_mul_self_apply_self]
      _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hmpos : (0 : ℝ) < (G.edgeFinset.card : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < (9999999 / 10000000 : ℝ)) h_guard
  have hnotall : ¬ (∀ i : V, f i = 0) := by
    intro hz
    have hzsq : (∑ i : V, f i ^ 2) = 0 := by simp [hz]
    rw [hzsq] at hsquares
    linarith only [hsquares, hmpos]
  have hV : Fintype.card V ≠ 0 := by
    intro h
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp h
    apply hnotall
    intro i
    exact isEmptyElim i
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  let S : Finset V := Finset.univ.filter (fun i => f i ≠ 0)
  let T : Finset V := Finset.univ.filter (fun i => f i = 0)
  let P : Polynomial ℝ := ∏ i ∈ S, (Polynomial.X - Polynomial.C (f i))
  have hfactor : (G.adjMatrix ℝ).charpoly = P * Polynomial.X ^ T.card := by
    calc
      (G.adjMatrix ℝ).charpoly =
          ∏ i : V, (Polynomial.X - Polynomial.C (f i)) := by
        simpa [f] using hA.charpoly_eq
      _ = P * (∏ i ∈ T, (Polynomial.X - Polynomial.C (f i))) := by
        simpa only [P, S, T, not_not] using
          (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset V)
            (fun i => f i ≠ 0)
            (fun i => (Polynomial.X - Polynomial.C (f i) : Polynomial ℝ))).symm
      _ = P * Polynomial.X ^ T.card := by
        congr 1
        calc
          (∏ i ∈ T, (Polynomial.X - Polynomial.C (f i))) =
              ∏ _i ∈ T, (Polynomial.X : Polynomial ℝ) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hz : f i = 0 := (Finset.mem_filter.mp hi).2
            simp [hz]
          _ = Polynomial.X ^ T.card := Finset.prod_const _
  have hmat : (G.adjMatrix ℤ).map (Int.castRingHom ℝ) = G.adjMatrix ℝ := by
    ext i j
    simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> simp
  have hmap : (G.adjMatrix ℝ).charpoly =
      (G.adjMatrix ℤ).charpoly.map (Int.castRingHom ℝ) := by
    simpa only [hmat] using
      Matrix.charpoly_map (G.adjMatrix ℤ) (Int.castRingHom ℝ)
  let z : ℤ := (G.adjMatrix ℤ).charpoly.coeff T.card
  have hz : (z : ℝ) = ∏ i ∈ S, -f i := by
    calc
      (z : ℝ) = (G.adjMatrix ℝ).charpoly.coeff T.card := by
        rw [hmap, Polynomial.coeff_map]
        rfl
      _ = P.coeff 0 := by
        rw [hfactor]
        simpa only [Nat.zero_add] using Polynomial.coeff_mul_X_pow P T.card 0
      _ = ∏ i ∈ S, -f i := by
        simp [P, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hprod_ne : (∏ i ∈ S, -f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi =>
      neg_ne_zero.mpr ((Finset.mem_filter.mp hi).2))
  have hz_ne : z ≠ 0 := by
    intro hz0
    apply hprod_ne
    calc
      (∏ i ∈ S, -f i) = (z : ℝ) := hz.symm
      _ = 0 := by simp [hz0]
  have habs : |(z : ℝ)| = ∏ i ∈ S, |f i| := by
    rw [hz, Finset.abs_prod]
    simp only [abs_neg]
  have hprod_one : (1 : ℝ) ≤ ∏ i ∈ S, |f i| := by
    rw [← habs]
    exact_mod_cast Int.one_le_abs hz_ne
  have hsum_abs : (∑ i ∈ S, |f i|) = ∑ i : V, |f i| := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hz0 : f i = 0 := by simpa [S] using hnot
    simp [hz0]
  have hsum_sq : (∑ i ∈ S, f i ^ 2) = ∑ i : V, f i ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hz0 : f i = 0 := by simpa [S] using hnot
    simp [hz0]
  have hexp : (1 : ℝ) ≤ Real.exp (∑ i ∈ S, (|f i| - 1)) := by
    calc
      (1 : ℝ) ≤ ∏ i ∈ S, |f i| := hprod_one
      _ ≤ ∏ i ∈ S, Real.exp (|f i| - 1) :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg (f i))
          (fun i _ => by simpa using Real.add_one_le_exp (|f i| - 1))
      _ = Real.exp (∑ i ∈ S, (|f i| - 1)) :=
        (Real.exp_sum S (fun i => |f i| - 1)).symm
  have henergy_rank : (S.card : ℝ) ≤ ∑ i : V, |f i| := by
    have h := Real.one_le_exp_iff.mp hexp
    rw [Finset.sum_sub_distrib] at h
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hsum_abs] at h
    linarith only [h]
  have hdev : (∑ i ∈ S, (|f i| - 1) ^ 2) ≤
      (2 : ℝ) * (G.edgeFinset.card : ℝ) - (∑ i : V, |f i|) := by
    calc
      (∑ i ∈ S, (|f i| - 1) ^ 2) =
          ∑ i ∈ S, (f i ^ 2 - 2 * |f i| + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [sub_sq, sq_abs, mul_one, one_pow]
      _ = (∑ i ∈ S, f i ^ 2) - 2 * (∑ i ∈ S, |f i|) + (S.card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) -
          2 * (∑ i : V, |f i|) + (S.card : ℝ) := by
        rw [hsum_sq, hsquares, hsum_abs]
      _ ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) - (∑ i : V, |f i|) := by
        linarith only [henergy_rank]
  obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
  obtain ⟨w, hw⟩ := (Set.range_nonempty f).csInf_mem (Set.finite_range f)
  have hmax (i : V) : f i ≤ f v := by
    rw [hv]
    exact le_csSup (Set.finite_range f).bddAbove ⟨i, rfl⟩
  have hmin (i : V) : f w ≤ f i := by
    rw [hw]
    exact csInf_le (Set.finite_range f).bddBelow ⟨i, rfl⟩
  have hpos : 0 < f v := by
    by_contra hv0
    have hnonpos (i : V) : f i ≤ 0 := (hmax i).trans (le_of_not_gt hv0)
    apply hnotall
    intro i
    have hsingle : -f i ≤ ∑ j : V, -f j :=
      Finset.single_le_sum (fun j _ => neg_nonneg.mpr (hnonpos j))
        (Finset.mem_univ i)
    rw [Finset.sum_neg_distrib, hsum, neg_zero] at hsingle
    linarith only [hsingle, hnonpos i]
  have hneg : f w < 0 := by
    by_contra hw0
    have hnonneg (i : V) : 0 ≤ f i := (le_of_not_gt hw0).trans (hmin i)
    apply hnotall
    intro i
    have hsingle : f i ≤ ∑ j : V, f j :=
      Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    rw [hsum] at hsingle
    linarith only [hsingle, hnonneg i]
  have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ v, ne_of_gt hpos⟩
  have hwS : w ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ w, ne_of_lt hneg⟩
  have hvw : v ≠ w := by
    intro h
    rw [h] at hpos
    linarith only [hpos, hneg]
  have hpair : (|f v| - 1) ^ 2 + (|f w| - 1) ^ 2 ≤
      ∑ i ∈ S, (|f i| - 1) ^ 2 := by
    calc
      (|f v| - 1) ^ 2 + (|f w| - 1) ^ 2 =
          ∑ i ∈ ({v, w} : Finset V), (|f i| - 1) ^ 2 := by
        rw [Finset.sum_pair hvw]
      _ ≤ ∑ i ∈ S, (|f i| - 1) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by
            simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
            exact ⟨hvS, hwS⟩)
          (fun i _ _ => sq_nonneg (|f i| - 1))
  rw [abs_of_pos hpos, abs_of_neg hneg] at hpair
  change (2 : ℝ) * (G.edgeFinset.card : ℝ) - (∑ i : V, |f i|) ≥
    (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) -
      (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range f))) - 2) ^ 2 / 2
  simp only [if_neg hV]
  rw [← hv, ← hw]
  nlinarith only [hpair.trans hdev, sq_nonneg (f v + f w)]
