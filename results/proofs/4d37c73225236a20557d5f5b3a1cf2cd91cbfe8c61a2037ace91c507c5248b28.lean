import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic








open scoped BigOperators

theorem hull3d_min_degree_le_0_0357143_0_75_size_spectral_spread_0_is_connected_01b2dc2cdaf3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.minDegree : ℝ) ≤ (((8928571428571619 / 250000000000000000 : ℝ) * (G.edgeFinset.card : ℝ)) + ((3 / 4 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · letI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let f : V → ℝ := hA.eigenvalues
    let a : ℝ := sInf (Set.range f)
    let z : ℝ := sSup (Set.range f)
    let c : ℝ := 8928571428571619 / 250000000000000000
    change (G.minDegree : ℝ) ≤ c * (G.edgeFinset.card : ℝ) + (3 / 4 : ℝ) * (z - a)
    have hm : 0 ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
    have hspread : 0 ≤ z - a :=
      sub_nonneg.mpr (csInf_le_csSup (Set.range_nonempty f)
        (Set.finite_range f).bddBelow (Set.finite_range f).bddAbove)
    by_cases hd : G.minDegree = 0
    · rw [hd, Nat.cast_zero]
      have hc0 : 0 ≤ c := by norm_num [c]
      exact add_nonneg (mul_nonneg hc0 hm) (mul_nonneg (by norm_num) hspread)
    · let b := hA.eigenvectorBasis
      let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V := A.toEuclideanLin
      have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
      have hTb (v : V) : T (b v) = f v • b v := by
        apply PiLp.ext
        intro w
        change (Matrix.mulVec A (fun i => (b v) i)) w = f v * (b v) w
        exact congrFun (hA.mulVec_eigenvectorBasis v) w
      have hcoord (x : EuclideanSpace ℝ V) (v : V) :
          inner ℝ (b v) (T x) = f v * inner ℝ (b v) x := by
        rw [← hT (b v) x, hTb v, real_inner_smul_left]
      have hdiag (x : EuclideanSpace ℝ V) :
          inner ℝ x (T x) = ∑ v : V, f v * (inner ℝ (b v) x) ^ 2 := by
        rw [← b.sum_inner_mul_inner x (T x)]
        apply Finset.sum_congr rfl
        intro v _
        rw [hcoord x v, real_inner_comm (b v) x]
        ring
      have hself (x : EuclideanSpace ℝ V) :
          inner ℝ x x = ∑ v : V, (inner ℝ (b v) x) ^ 2 := by
        rw [← b.sum_inner_mul_inner x x]
        apply Finset.sum_congr rfl
        intro v _
        rw [real_inner_comm (b v) x]
        ring
      have hquad (y : V → ℝ) :
          a * dotProduct y y ≤ dotProduct y (Matrix.mulVec A y) ∧
          dotProduct y (Matrix.mulVec A y) ≤ z * dotProduct y y := by
        let x : EuclideanSpace ℝ V := WithLp.toLp 2 y
        have hxx : inner ℝ x x = dotProduct y y := by
          change dotProduct y (star y) = dotProduct y y
          rw [star_trivial]
        have hxT : inner ℝ x (T x) = dotProduct y (Matrix.mulVec A y) := by
          change dotProduct (Matrix.mulVec A y) (star y) = dotProduct y (Matrix.mulVec A y)
          rw [star_trivial]
          exact dotProduct_comm _ _
        constructor
        · rw [← hxx, ← hxT, hself x, hdiag x, Finset.mul_sum]
          exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right
            (csInf_le (Set.finite_range f).bddBelow (Set.mem_range_self v))
            (sq_nonneg (inner ℝ (b v) x)))
        · rw [← hxx, ← hxT, hself x, hdiag x, Finset.mul_sum]
          exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right
            (le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v))
            (sq_nonneg (inner ℝ (b v) x)))
      have hsum : Fintype.card V * G.minDegree ≤ 2 * G.edgeFinset.card := by
        calc
          Fintype.card V * G.minDegree = ∑ _ : V, G.minDegree := by simp
          _ ≤ ∑ v : V, G.degree v :=
            Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
          _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      have hone2 : dotProduct (1 : V → ℝ) (1 : V → ℝ) = (Fintype.card V : ℝ) := by
        simp
      have honeA : dotProduct (1 : V → ℝ) (Matrix.mulVec A (1 : V → ℝ)) =
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        calc
          _ = ∑ v : V, (G.degree v : ℝ) := by simp [A, dotProduct]
          _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
            exact_mod_cast G.sum_degrees_eq_twice_card_edges
      have hz := (hquad (1 : V → ℝ)).2
      rw [hone2, honeA] at hz
      have hsumr : (Fintype.card V : ℝ) * (G.minDegree : ℝ) ≤
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hsum
      have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hV
      have hbig : (G.minDegree : ℝ) ≤ z := by
        by_contra h
        have hp : 0 < (Fintype.card V : ℝ) * ((G.minDegree : ℝ) - z) :=
          mul_pos hnpos (sub_pos.mpr (lt_of_not_ge h))
        nlinarith only [hsumr, hz, hp]
      have hnebot : G ≠ ⊥ := by
        intro he
        apply hd
        simp [he]
      obtain ⟨u, v, huv⟩ : ∃ u v : V, G.Adj u v := by
        by_contra! h
        exact hnebot (SimpleGraph.eq_bot_iff_forall_not_adj.mpr h)
      let y : V → ℝ := Pi.single u 1 - Pi.single v 1
      have hy2 : dotProduct y y = 2 := by
        simp only [y, sub_dotProduct, dotProduct_sub, single_dotProduct, one_mul,
          Pi.single_eq_same, Pi.single_eq_of_ne huv.ne, Pi.single_eq_of_ne huv.ne']
        norm_num
      have hyA : dotProduct y (Matrix.mulVec A y) = -2 := by
        simp only [y, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
          Matrix.mulVec_single_one, single_dotProduct, one_mul]
        norm_num [A, Matrix.col, huv, huv.symm]
      have hsmall : a ≤ -1 := by
        have hb := (hquad y).1
        rw [hy2, hyA] at hb
        linarith
      have hdn : G.minDegree + 1 ≤ Fintype.card V :=
        Nat.succ_le_of_lt G.minDegree_lt_card
      have hdmNat : G.minDegree * (G.minDegree + 1) ≤ 2 * G.edgeFinset.card := by
        calc
          G.minDegree * (G.minDegree + 1) = (G.minDegree + 1) * G.minDegree :=
            Nat.mul_comm _ _
          _ ≤ Fintype.card V * G.minDegree := Nat.mul_le_mul_right _ hdn
          _ ≤ 2 * G.edgeFinset.card := hsum
      have hdm : (G.minDegree : ℝ) * ((G.minDegree : ℝ) + 1) ≤
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        exact_mod_cast hdmNat
      have hprod : 0 ≤ ((G.minDegree : ℝ) - 6) * ((G.minDegree : ℝ) - 7) := by
        by_cases hd6 : G.minDegree ≤ 6
        · have h6 : (G.minDegree : ℝ) ≤ 6 := by exact_mod_cast hd6
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
        · have h7 : (7 : ℝ) ≤ (G.minDegree : ℝ) := by
            exact_mod_cast (show 7 ≤ G.minDegree by omega)
          exact mul_nonneg (by linarith) (by linarith)
      have hc : (1 / 28 : ℝ) ≤ c := by norm_num [c]
      have hcprod := mul_le_mul_of_nonneg_right hc hm
      nlinarith only [hdm, hprod, hbig, hsmall, hcprod]
