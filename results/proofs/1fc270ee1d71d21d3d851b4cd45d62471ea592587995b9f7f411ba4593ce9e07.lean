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

theorem hull3d_max_degree_le_0_1_1_7_nordhaus_gaddum_spectral_product_graph_energy_0_is_tree_72e0a77a8d94 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (G.maxDegree : ℝ) ≤ (((1 / 10 : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)))) + ((17 / 10 : ℝ) * (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|))) := by
  classical
  letI : Nonempty V := h_guard.connected.nonempty
  have hV : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  simp only [if_neg hV]
  let n : ℝ := Fintype.card V
  let d : ℝ := G.maxDegree
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let c : ℝ := sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)
  let E : ℝ := ∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|
  change d ≤ (1 / 10 : ℝ) * (r * c) + (17 / 10 : ℝ) * E
  have hpsd (H : SimpleGraph V) [DecidableRel H.Adj] :
      ((sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues)) •
        (1 : Matrix V V ℝ) - H.adjMatrix ℝ).PosSemidef := by
    let hB : (H.adjMatrix ℝ).IsHermitian := H.isHermitian_adjMatrix ℝ
    let s : ℝ := sSup (Set.range hB.eigenvalues)
    let U : Matrix V V ℝ := hB.eigenvectorUnitary
    have hD : (Matrix.diagonal (fun w : V => s - hB.eigenvalues w)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro w
      exact sub_nonneg.mpr
        (le_csSup (Set.finite_range hB.eigenvalues).bddAbove ⟨w, rfl⟩)
    have hdiag : Matrix.diagonal (fun w : V => s - hB.eigenvalues w) =
        s • (1 : Matrix V V ℝ) - Matrix.diagonal hB.eigenvalues := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal, Matrix.one_apply, hij, smul_eq_mul]
    have hunit : U * Matrix.conjTranspose U = 1 := by
      simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hB.eigenvectorUnitary
    have hspec : H.adjMatrix ℝ =
        U * Matrix.diagonal hB.eigenvalues * Matrix.conjTranspose U := by
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hB.spectral_theorem
    change (s • (1 : Matrix V V ℝ) - H.adjMatrix ℝ).PosSemidef
    have hp := hD.mul_mul_conjTranspose_same U
    rw [hdiag, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hunit, ← hspec] at hp
    exact hp
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let z : V → ℝ := Pi.single v 1
  let y : V → ℝ := Matrix.mulVec A z
  have hAz : Matrix.mulVec A z = y := rfl
  have hzz : dotProduct z z = 1 := by simp [z]
  have hzy : dotProduct z y = 0 := by
    change dotProduct (Pi.single v (1 : ℝ))
      (Matrix.mulVec A (Pi.single v 1)) = 0
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    change G.adjMatrix ℝ v v = 0
    simp
  have hyz : dotProduct y z = 0 := by
    rw [dotProduct_comm]
    exact hzy
  have hzAy : dotProduct z (Matrix.mulVec A y) = d := by
    change dotProduct (Pi.single v (1 : ℝ))
      (Matrix.mulVec A (Matrix.mulVec A (Pi.single v 1))) = d
    rw [single_dotProduct, one_mul, Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one]
    change (G.adjMatrix ℝ * G.adjMatrix ℝ) v v = (G.maxDegree : ℝ)
    rw [G.adjMatrix_mul_self_apply_self, ← hv]
  have hyy : dotProduct y y = d := by
    calc
      dotProduct y y = dotProduct z (Matrix.mulVec A y) := by
        simpa only [star_trivial] using hA.star_dotProduct_mulVec_comm y z
      _ = d := hzAy
  have hAnonneg (w u : V) : 0 ≤ A w u := by
    change 0 ≤ (if G.Adj w u then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  have hypos (w : V) : 0 ≤ y w := by
    change 0 ≤ (Matrix.mulVec A (Pi.single v (1 : ℝ))) w
    rw [Matrix.mulVec_single_one]
    exact hAnonneg w v
  have hq : 0 ≤ dotProduct y (Matrix.mulVec A y) := by
    change 0 ≤ ∑ w : V, y w * (∑ u : V, A w u * y u)
    exact Finset.sum_nonneg (fun w _ => mul_nonneg (hypos w)
      (Finset.sum_nonneg (fun u _ => mul_nonneg (hAnonneg w u) (hypos u))))
  have hr : 0 ≤ r := by
    have h : 0 ≤ (r • (1 : Matrix V V ℝ) - A) v v := (hpsd G).diag_nonneg
    simpa [A, Matrix.one_apply, smul_eq_mul] using h
  have hnorm (t : ℝ) : dotProduct (t • z + y) (t • z + y) = t ^ 2 + d := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      hzz, hzy, hyz, hyy, smul_eq_mul]
    ring
  have hform (t : ℝ) :
      dotProduct (t • z + y) (Matrix.mulVec A (t • z + y)) =
        2 * t * d + dotProduct y (Matrix.mulVec A y) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, hAz, hzy, hyy,
      hzAy, smul_eq_mul]
    ring
  have hquad (t : ℝ) :
      0 ≤ r * (t ^ 2 + d) - 2 * t * d - dotProduct y (Matrix.mulVec A y) := by
    have h0 : 0 ≤ dotProduct (t • z + y)
        (Matrix.mulVec (r • (1 : Matrix V V ℝ) - A) (t • z + y)) := by
      simpa only [star_trivial] using
        (hpsd G).dotProduct_mulVec_nonneg (t • z + y)
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hnorm, hform] at h0
    nlinarith only [h0]
  have hsq : d ≤ r ^ 2 := by
    by_cases hr0 : r = 0
    · have h := hquad 1
      rw [hr0] at h ⊢
      nlinarith only [h, hq]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hp : 0 ≤ r * (r ^ 2 - d) := by
        nlinarith only [hquad r, hq]
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp hrpos)
  have henergy : 2 * r ≤ E := by
    simpa only [if_neg hV] using graph_energy_spectral_radius_lower G
  have hnpos : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card V)
  have hedge : (G.edgeFinset.card : ℝ) + 1 = n := by
    change (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ)
    exact_mod_cast h_guard.card_edgeFinset
  have hsum : (∑ w : V, (G.degree w : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hdegrees (w : V) : (G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1 = n := by
    have h : G.degree w + Gᶜ.degree w + 1 = Fintype.card V := by
      rw [G.degree_compl w]
      have hw := G.degree_lt_card_verts w
      omega
    change (G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1 = (Fintype.card V : ℝ)
    exact_mod_cast h
  have htotal : (∑ w : V, (G.degree w : ℝ)) +
      (∑ w : V, (Gᶜ.degree w : ℝ)) + n = n * n := by
    calc
      (∑ w : V, (G.degree w : ℝ)) + (∑ w : V, (Gᶜ.degree w : ℝ)) + n =
          ∑ w : V, ((G.degree w : ℝ) + (Gᶜ.degree w : ℝ) + 1) := by
            simp [n, Finset.sum_add_distrib]
      _ = ∑ _w : V, n := Finset.sum_congr rfl (fun w _ => hdegrees w)
      _ = n * n := by simp [n, nsmul_eq_mul]
  have hcomp : (∑ w : V, (Gᶜ.degree w : ℝ)) = n * (n - 3) + 2 := by
    nlinarith only [htotal, hsum, hedge]
  have hcupper : (∑ w : V, (Gᶜ.degree w : ℝ)) ≤ n * c := by
    apply sub_nonneg.mp
    have hMx : Matrix.mulVec
        (c • (1 : Matrix V V ℝ) - Gᶜ.adjMatrix ℝ)
        (fun _ : V => (1 : ℝ)) = fun w => c - (Gᶜ.degree w : ℝ) := by
      ext w
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
    have hq := (hpsd Gᶜ).dotProduct_mulVec_nonneg (fun _ : V => (1 : ℝ))
    rw [hMx] at hq
    simpa [dotProduct, Finset.sum_sub_distrib, nsmul_eq_mul, n] using hq
  have hclower : n - 3 ≤ c := by
    have hp : n * (n - 3) ≤ n * c := by
      nlinarith only [hcupper, hcomp]
    exact le_of_mul_le_mul_left hp hnpos
  have hdn : d + 1 ≤ n := by
    change (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ)
    exact_mod_cast (Nat.succ_le_of_lt G.maxDegree_lt_card_verts)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hcross : 0 ≤ r * (c - d + 2) :=
    mul_nonneg hr (by linarith only [hclower, hdn])
  by_cases hr10 : r ≤ 10
  · have hfac : 0 ≤ (10 - r) * (r ^ 2 - d) :=
      mul_nonneg (sub_nonneg.mpr hr10) (sub_nonneg.mpr hsq)
    have hpoly : 0 ≤ r * ((r - 5) ^ 2 + 7) :=
      mul_nonneg hr (by positivity)
    nlinarith only [hfac, hpoly, hcross, henergy]
  · have hfac : 0 ≤ (r - 10) * d :=
      mul_nonneg (by linarith only [hr10]) hd
    nlinarith only [hfac, hcross, henergy, hr]
