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

theorem hull3d_max_degree_le_0_125_1_125_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_ef5c51f5edcb {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (G.maxDegree : ℝ) ≤ (((1 / 8 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)))) + ((9 / 8 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|))) := by
  classical
  letI : Nonempty V := h_guard.connected.nonempty
  let n : ℝ := Fintype.card V
  let d : ℝ := G.maxDegree
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let q : ℝ := sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)
  let E : ℝ := ∑ w : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues w|
  have hcard : Fintype.card V ≠ 0 := Nat.ne_of_gt Fintype.card_pos
  simp only [if_neg hcard]
  change d ≤ (1 / 8 : ℝ) * (r * q) + (9 / 8 : ℝ) * E
  have hnpos : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hd : 0 ≤ d := Nat.cast_nonneg G.maxDegree
  have hupper (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) :
      dotProduct x (Matrix.mulVec (H.adjMatrix ℝ) x) ≤
        sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) * dotProduct x x := by
    let B : Matrix V V ℝ := H.adjMatrix ℝ
    let hB : B.IsHermitian := H.isHermitian_adjMatrix ℝ
    let t : ℝ := sSup (Set.range hB.eigenvalues)
    let U : Matrix V V ℝ := hB.eigenvectorUnitary
    have hD : (Matrix.diagonal (fun w : V => t - hB.eigenvalues w)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro w
      exact sub_nonneg.mpr
        (le_csSup (Set.finite_range hB.eigenvalues).bddAbove ⟨w, rfl⟩)
    have hdiag : Matrix.diagonal (fun w : V => t - hB.eigenvalues w) =
        t • (1 : Matrix V V ℝ) - Matrix.diagonal hB.eigenvalues := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal, Matrix.one_apply, hij, smul_eq_mul]
    have hunit : U * Matrix.conjTranspose U = 1 := by
      simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hB.eigenvectorUnitary
    have hspec : B = U * Matrix.diagonal hB.eigenvalues * Matrix.conjTranspose U := by
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hB.spectral_theorem
    have hP : (t • (1 : Matrix V V ℝ) - B).PosSemidef := by
      have hp := hD.mul_mul_conjTranspose_same U
      rw [hdiag, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hunit, ← hspec] at hp
      exact hp
    have hp := hP.dotProduct_mulVec_nonneg x
    have hp' : 0 ≤ t * dotProduct x x - dotProduct x (B.mulVec x) := by
      simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using hp
    exact sub_nonneg.mp hp'
  have havg (H : SimpleGraph V) [DecidableRel H.Adj] :
      (∑ w : V, (H.degree w : ℝ)) ≤
        n * sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) := by
    simpa [dotProduct, n, mul_comm] using hupper H (fun _ : V => (1 : ℝ))
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hr0 : 0 ≤ r := by
    simpa [r] using hupper G (Pi.single v (1 : ℝ))
  have hq0 : 0 ≤ q := by
    simpa [q] using hupper Gᶜ (Pi.single v (1 : ℝ))
  have hE0 : 0 ≤ E := Finset.sum_nonneg (fun w _ => abs_nonneg _)
  have henergy : 2 * r ≤ E := by
    simpa only [if_neg hcard] using graph_energy_spectral_radius_lower G
  by_cases hd0 : d = 0
  · rw [hd0]
    exact add_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg hr0 hq0))
      (mul_nonneg (by norm_num) hE0)
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hn : d + 1 ≤ n := by
      change (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ)
      exact_mod_cast (Nat.succ_le_of_lt G.maxDegree_lt_card_verts)
    have hm : (G.edgeFinset.card : ℝ) + 1 = n := by
      change (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ)
      exact_mod_cast h_guard.card_edgeFinset
    have hsum : (∑ w : V, (G.degree w : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hdeg (w : V) : (G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1 = n := by
      have hnat : G.degree w + Gᶜ.degree w + 1 = Fintype.card V := by
        rw [G.degree_compl w]
        have hw := G.degree_lt_card_verts w
        omega
      change (G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1 = (Fintype.card V : ℝ)
      exact_mod_cast hnat
    have htotal : (∑ w : V, (G.degree w : ℝ)) +
        (∑ w : V, (Gᶜ.degree w : ℝ)) + n = n * n := by
      calc
        _ = ∑ w : V, ((G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1) := by
          simp [Finset.sum_add_distrib, n]
        _ = ∑ _w : V, n := by
          apply Finset.sum_congr rfl
          intro w hw
          exact hdeg w
        _ = n * n := by simp [n, nsmul_eq_mul]
    have hcomp : n * (n - 3) ≤ ∑ w : V, (Gᶜ.degree w : ℝ) := by
      nlinarith only [htotal, hm, hsum]
    have hqlo : n - 3 ≤ q :=
      le_of_mul_le_mul_left (hcomp.trans (havg Gᶜ)) hnpos
    have hqdegree : d - 2 ≤ q := by
      linarith only [hn, hqlo]
    have hsingle : d ≤ ∑ w : V, (G.degree w : ℝ) := by
      have hs : (G.degree v : ℝ) ≤ ∑ w : V, (G.degree w : ℝ) :=
        Finset.single_le_sum (fun w _ => Nat.cast_nonneg (G.degree w))
          (Finset.mem_univ v)
      simpa only [d, hv] using hs
    have hrpos : 0 < r :=
      pos_of_mul_pos_right
        (lt_of_lt_of_le hdpos (hsingle.trans (havg G))) (le_of_lt hnpos)
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let e : V → ℝ := Pi.single v 1
    let y : V → ℝ := A.mulVec e
    have hsymm : A.IsSymm := G.isSymm_adjMatrix
    have hee : dotProduct e e = 1 := by simp [e]
    have hey : dotProduct e y = 0 := by simp [e, y, A]
    have hye : dotProduct y e = 0 := by
      rw [dotProduct_comm]
      exact hey
    have heAy : dotProduct e (A.mulVec y) = d := by
      change dotProduct (Pi.single v 1)
        (A.mulVec (A.mulVec (Pi.single v 1))) = d
      rw [Matrix.mulVec_mulVec, single_one_dotProduct,
        Matrix.mulVec_single_one, Matrix.col_apply]
      change (G.adjMatrix ℝ * G.adjMatrix ℝ) v v = (G.maxDegree : ℝ)
      rw [G.adjMatrix_mul_self_apply_self, hv]
    have hyy : dotProduct y y = d := by
      calc
        dotProduct y y = dotProduct y (A.mulVec e) := rfl
        _ = dotProduct e (A.mulVec y) := hsymm.dotProduct_mulVec_comm
        _ = d := heAy
    have heAe : dotProduct e (A.mulVec e) = 0 := hey
    have hyAe : dotProduct y (A.mulVec e) = d := hyy
    have hA0 (w u : V) : 0 ≤ A w u := by
      by_cases h : G.Adj w u <;> simp [A, h]
    have hy0 (w : V) : 0 ≤ y w := by
      simpa only [y, e, Matrix.mulVec_single_one, Matrix.col_apply] using hA0 w v
    have hAy0 (w : V) : 0 ≤ A.mulVec y w := by
      change 0 ≤ ∑ u : V, A w u * y u
      exact Finset.sum_nonneg (fun u _ => mul_nonneg (hA0 w u) (hy0 u))
    have hYYA : 0 ≤ dotProduct y (A.mulVec y) :=
      Finset.sum_nonneg (fun w _ => mul_nonneg (hy0 w) (hAy0 w))
    have hnorm : dotProduct (r • e + y) (r • e + y) = r ^ 2 + d := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hee, hey, hye, hyy]
      ring
    have hquad : dotProduct (r • e + y) (A.mulVec (r • e + y)) =
        2 * r * d + dotProduct y (A.mulVec y) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        heAe, heAy, hyAe]
      ring
    have hxbound := hupper G (r • e + y)
    change dotProduct (r • e + y) (A.mulVec (r • e + y)) ≤
      r * dotProduct (r • e + y) (r • e + y) at hxbound
    rw [hquad, hnorm] at hxbound
    have hrd : r * d ≤ r * r ^ 2 := by
      nlinarith only [hxbound, hYYA]
    have hsq : d ≤ r ^ 2 := le_of_mul_le_mul_left hrd hrpos
    have hmain : 8 * d ≤ r * (d + 16) := by
      by_cases h8 : (8 : ℝ) ≤ r
      · have hp := mul_nonneg (sub_nonneg.mpr h8) hd
        nlinarith only [hp, hr0]
      · have hp := mul_le_mul_of_nonneg_left hsq
          (show 0 ≤ (8 : ℝ) - r by linarith only [h8])
        have hs := mul_nonneg hr0 (sq_nonneg (r - 4))
        nlinarith only [hp, hs]
    have hprod : r * (d - 2) ≤ r * q :=
      mul_le_mul_of_nonneg_left hqdegree hr0
    nlinarith only [hmain, hprod, henergy]
