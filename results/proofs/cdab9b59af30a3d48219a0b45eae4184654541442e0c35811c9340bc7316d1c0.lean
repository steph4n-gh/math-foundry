import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic








open scoped BigOperators

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

theorem hull3d_min_degree_le_0_00892857_0_875_size_spectral_spread_0_is_connected_c66b5dc137e5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.minDegree : ℝ) ≤ (((892857142857183 / 100000000000000000 : ℝ) * (G.edgeFinset.card : ℝ)) + ((7 / 8 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let n : ℝ := Fintype.card V
    let d : ℝ := G.minDegree
    let m : ℝ := G.edgeFinset.card
    let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
    let l : ℝ := sInf (Set.range f)
    let u : ℝ := sSup (Set.range f)
    change d ≤ (892857142857183 / 100000000000000000 : ℝ) * m + (7 / 8 : ℝ) * (u - l)
    have hnpos : 0 < n := by
      dsimp [n]
      exact_mod_cast Nat.pos_of_ne_zero hV
    have hdnonneg : 0 ≤ d := Nat.cast_nonneg _
    have hmnonneg : 0 ≤ m := Nat.cast_nonneg _
    have hsize : d * n ≤ 2 * m := by
      have havg := hull_min_degree_le_1_average_degree_0_36a8fb326490 G
      rw [if_neg hV] at havg
      exact (le_div_iff₀ hnpos).mp havg
    have hlower (w : V) : l ≤ f w :=
      csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self w)
    have hupper (w : V) : f w ≤ u :=
      le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self w)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hspread : 0 ≤ u - l :=
      sub_nonneg.mpr ((hlower v).trans (hupper v))
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
      Matrix.toEuclideanLin (G.adjMatrix ℝ)
    have hsymm : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    have heig (w : V) : T (b w) = f w • b w := by
      apply (WithLp.ofLp_injective 2)
      change Matrix.mulVec (G.adjMatrix ℝ) (⇑(b w)) = f w • (⇑(b w))
      exact (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis w
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
    have hdiag : inner ℝ x (T x) =
        ∑ w : V, f w * (inner ℝ (b w) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner x (T x)]
      apply Finset.sum_congr rfl
      intro w _
      rw [← hsymm (b w) x, heig w, real_inner_smul_left,
        real_inner_comm x (b w)]
      ring
    have hquad : inner ℝ x (T x) ≤ u * ‖x‖ ^ 2 := by
      calc
        inner ℝ x (T x) = ∑ w : V, f w * (inner ℝ (b w) x) ^ 2 := hdiag
        _ ≤ ∑ w : V, u * (inner ℝ (b w) x) ^ 2 :=
          Finset.sum_le_sum (fun w _ =>
            mul_le_mul_of_nonneg_right (hupper w) (sq_nonneg _))
        _ = u * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum, b.sum_sq_inner_right x]
    have hxnorm : ‖x‖ ^ 2 = n := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [x, n]
    have hxquad : inner ℝ x (T x) = 2 * m := by
      calc
        inner ℝ x (T x) = ∑ w : V, (G.degree w : ℝ) := by
          change dotProduct
            (Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)))
            (star (fun _ : V => (1 : ℝ))) = _
          simp [dotProduct]
        _ = 2 * m := by
          dsimp [m]
          exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hrho : d ≤ u := by
      apply (mul_le_mul_iff_of_pos_right hnpos).mp
      calc
        d * n ≤ 2 * m := hsize
        _ = inner ℝ x (T x) := hxquad.symm
        _ ≤ u * ‖x‖ ^ 2 := hquad
        _ = u * n := by rw [hxnorm]
    have htrace : (∑ w : V, f w) = 0 := by
      simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
    have hext : u - l ≤ -(n * l) := by
      have hsingle : f v - l ≤ ∑ w : V, (f w - l) :=
        Finset.single_le_sum (fun w _ => sub_nonneg.mpr (hlower w))
          (Finset.mem_univ v)
      calc
        u - l = f v - l := by rw [hv]
        _ ≤ ∑ w : V, (f w - l) := hsingle
        _ = -(n * l) := by
          rw [Finset.sum_sub_distrib, htrace]
          simp [n]
    have hspread_mul : n * d ≤ (n - 1) * (u - l) := by
      have hnd := mul_le_mul_of_nonneg_left hrho hnpos.le
      nlinarith only [hext, hnd]
    by_cases hd0 : G.minDegree = 0
    · have hd : d = 0 := by simp [d, hd0]
      rw [hd]
      nlinarith only [hmnonneg, hspread]
    · have hcard : 1 < Fintype.card V := by
        have hdegpos := Nat.pos_of_ne_zero hd0
        have hdeglt := G.minDegree_lt_card
        omega
      have hcardR : (1 : ℝ) < n := by
        dsimp [n]
        exact_mod_cast hcard
      have hn1 : 0 < n - 1 := sub_pos.mpr hcardR
      have hpoly : n - 1 ≤ n * (n - 1) / 224 + (7 / 8 : ℝ) * n := by
        nlinarith only [sq_nonneg (2 * n - 29)]
      have hpolyD := mul_le_mul_of_nonneg_left hpoly hdnonneg
      have hsize_mul := mul_le_mul_of_nonneg_right hsize hn1.le
      have hscaled : d * (n - 1) ≤
          (m / 112 + (7 / 8 : ℝ) * (u - l)) * (n - 1) := by
        nlinarith only [hpolyD, hsize_mul, hspread_mul]
      have hbound : d ≤ m / 112 + (7 / 8 : ℝ) * (u - l) :=
        (mul_le_mul_iff_of_pos_right hn1).mp hscaled
      have hc : (1 / 112 : ℝ) ≤
          (892857142857183 / 100000000000000000 : ℝ) := by
        norm_num
      have hcm := mul_le_mul_of_nonneg_right hc hmnonneg
      calc
        d ≤ m / 112 + (7 / 8 : ℝ) * (u - l) := hbound
        _ ≤ (892857142857183 / 100000000000000000 : ℝ) * m +
            (7 / 8 : ℝ) * (u - l) := by
          nlinarith only [hcm]
