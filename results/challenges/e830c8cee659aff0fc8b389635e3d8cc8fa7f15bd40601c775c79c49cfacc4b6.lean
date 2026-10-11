import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic








open scoped BigOperators

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem hull_clique_number_le_0_5_signless_laplacian_spectral_radius_1_fe853c08d6ab {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (((1 / 2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) + (1 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · have hz : (G.cliqueNum : ℝ) ≤ 0 := by
      simpa only [hn, Nat.cast_zero] using composed_2cd2dd810fbb9720 G
    simpa only [if_pos hn, mul_zero, zero_add] using
      hz.trans (by norm_num : (0 : ℝ) ≤ 1)
  haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
  rw [if_neg hn]
  let Q : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
  let hQ : Q.IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  let q : ℝ := sSup (Set.range hQ.eigenvalues)
  change (G.cliqueNum : ℝ) ≤ (1 / 2 : ℝ) * q + 1
  have hbdd : BddAbove (Set.range hQ.eigenvalues) :=
    (Set.finite_range hQ.eigenvalues).bddAbove
  have hsym : Q.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  have heig (i : V) :
      Q.toEuclideanLin (hQ.eigenvectorBasis i) =
        hQ.eigenvalues i • hQ.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    simpa only [Matrix.toLpLin_apply, PiLp.toLp_apply, PiLp.smul_apply,
      Pi.smul_apply, smul_eq_mul] using
      congrFun (hQ.mulVec_eigenvectorBasis i) j
  have hinner (z : EuclideanSpace ℝ V) :
      inner ℝ z (Q.toEuclideanLin z) ≤ q * inner ℝ z z := by
    calc
      inner ℝ z (Q.toEuclideanLin z) =
          ∑ i : V, hQ.eigenvalues i *
            (inner ℝ (hQ.eigenvectorBasis i) z) ^ 2 := by
        rw [← hQ.eigenvectorBasis.sum_inner_mul_inner z (Q.toEuclideanLin z)]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hsym (hQ.eigenvectorBasis i) z, heig i,
          real_inner_smul_left, real_inner_comm z (hQ.eigenvectorBasis i)]
        ring
      _ ≤ ∑ i : V, q * (inner ℝ (hQ.eigenvectorBasis i) z) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (le_csSup hbdd ⟨i, rfl⟩) (sq_nonneg _)
      _ = q * inner ℝ z z := by
        rw [← Finset.mul_sum]
        congr 1
        simpa only [real_inner_comm z, pow_two] using
          hQ.eigenvectorBasis.sum_inner_mul_inner z z
  have hupper (f : V → ℝ) :
      dotProduct f (Matrix.mulVec Q f) ≤ q * dotProduct f f := by
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] using
      hinner (WithLp.toLp 2 f)
  have hk : 0 < G.cliqueNum :=
    Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
  have hkR : 0 < (G.cliqueNum : ℝ) := by exact_mod_cast hk
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  let x : V → ℝ := fun v => if v ∈ s then 1 else 0
  have hx (v : V) : 0 ≤ x v := by
    by_cases hv : v ∈ s <;> simp [x, hv]
  have hlocal (v : V) (hv : v ∈ s) :
      2 * ((G.cliqueNum : ℝ) - 1) ≤ Matrix.mulVec Q x v := by
    have hsubset : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [G.mem_neighborFinset]
      exact hs.isClique hv (Finset.mem_erase.mp hw).2
        (Finset.mem_erase.mp hw).1.symm
    have hnat : (s.erase v).card + 1 = G.cliqueNum := by
      rw [Finset.card_erase_of_mem hv, hs.card_eq]
      omega
    have hreal : ((s.erase v).card : ℝ) + 1 = (G.cliqueNum : ℝ) := by
      exact_mod_cast hnat
    have herase : ((s.erase v).card : ℝ) = (G.cliqueNum : ℝ) - 1 := by
      linarith only [hreal]
    have hcard := Finset.card_le_card hsubset
    rw [G.card_neighborFinset_eq_degree] at hcard
    have hdeg : ((s.erase v).card : ℝ) ≤ (G.degree v : ℝ) := by
      exact_mod_cast hcard
    rw [herase] at hdeg
    have hsum : (∑ w ∈ s.erase v, x w) ≤
        ∑ w ∈ G.neighborFinset v, x w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun w _ _ => hx w)
    have hsx : (∑ w ∈ s.erase v, x w) = ((s.erase v).card : ℝ) := by
      calc
        (∑ w ∈ s.erase v, x w) = ∑ _w ∈ s.erase v, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro w hw
          simp only [x, if_pos (Finset.mem_of_mem_erase hw)]
        _ = ((s.erase v).card : ℝ) := by simp
    rw [hsx, herase] at hsum
    have hQx : Matrix.mulVec Q x v =
        (G.degree v : ℝ) + ∑ w ∈ G.neighborFinset v, x w := by
      simp only [Q, Matrix.add_mulVec, Pi.add_apply,
        G.degMatrix_mulVec_apply, G.adjMatrix_mulVec_apply,
        x, if_pos hv, mul_one]
    rw [hQx]
    linarith only [hdeg, hsum]
  have hxx : dotProduct x x = (G.cliqueNum : ℝ) := by
    calc
      dotProduct x x = ∑ v : V, if v ∈ s then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hvu
        by_cases hv : v ∈ s <;> simp [x, hv]
      _ = (s.card : ℝ) := by
        simp only [Finset.sum_ite_mem_eq, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      _ = (G.cliqueNum : ℝ) := by rw [hs.card_eq]
  have hlower :
      2 * (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) ≤
        dotProduct x (Matrix.mulVec Q x) := by
    calc
      2 * (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) =
          ∑ _v ∈ s, 2 * ((G.cliqueNum : ℝ) - 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hs.card_eq]
        ring
      _ ≤ ∑ v ∈ s, Matrix.mulVec Q x v :=
        Finset.sum_le_sum (fun v hv => hlocal v hv)
      _ = dotProduct x (Matrix.mulVec Q x) := by
        symm
        calc
          dotProduct x (Matrix.mulVec Q x) =
              ∑ v : V, if v ∈ s then Matrix.mulVec Q x v else 0 := by
            apply Finset.sum_congr rfl
            intro v hvu
            by_cases hv : v ∈ s <;> simp [x, hv]
          _ = ∑ v ∈ s, Matrix.mulVec Q x v :=
            Finset.sum_ite_mem_eq s _
  have hu := hupper x
  rw [hxx] at hu
  have hmul : (G.cliqueNum : ℝ) * (2 * ((G.cliqueNum : ℝ) - 1)) ≤
      (G.cliqueNum : ℝ) * q := by
    calc
      (G.cliqueNum : ℝ) * (2 * ((G.cliqueNum : ℝ) - 1)) =
          2 * (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) := by ring
      _ ≤ dotProduct x (Matrix.mulVec Q x) := hlower
      _ ≤ q * (G.cliqueNum : ℝ) := hu
      _ = (G.cliqueNum : ℝ) * q := mul_comm _ _
  have hq : 2 * ((G.cliqueNum : ℝ) - 1) ≤ q := by
    by_contra h
    have hpos : 0 < (G.cliqueNum : ℝ) *
        (2 * ((G.cliqueNum : ℝ) - 1) - q) :=
      mul_pos hkR (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hmul, hpos]
  linarith only [hq]

theorem hull3d_order_ge_0_0_5_laplacian_spectral_radius_signless_laplacian_spectral_radius_1_is_connected_d400e6f639cf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Fintype.card V : ℝ) ≥ (((1 / 2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) + (1 : ℝ)) := by
  classical
  letI : Nonempty V := h_guard.nonempty
  have hcard : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  let Q : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
  let hQ : Q.IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  have hbound : ∀ i : V,
      hQ.eigenvalues i ≤ 2 * ((Fintype.card V : ℝ) - 1) := by
    intro i
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hQ.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun w : V => |x w|)
        Finset.univ_nonempty
    have hm : 0 < |x v| := by
      obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
      exact (abs_pos.mpr hw).trans_le (hmax w (Finset.mem_univ w))
    have heig : Matrix.mulVec Q x = (hQ.eigenvalues i) • x :=
      hQ.mulVec_eigenvectorBasis i
    have hrow :
        (G.degree v : ℝ) * x v + (∑ w ∈ G.neighborFinset v, x w) =
          hQ.eigenvalues i * x v := by
      simpa only [Q, Matrix.add_mulVec, Pi.add_apply,
        SimpleGraph.degMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.smul_apply, smul_eq_mul] using congrFun heig v
    have hsum : |∑ w ∈ G.neighborFinset v, x w| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
          Finset.abs_sum_le_sum_abs x (G.neighborFinset v)
        _ ≤ ∑ w ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun w _ => hmax w (Finset.mem_univ w))
        _ = _ := by simp [nsmul_eq_mul]
    have hmul : |hQ.eigenvalues i| * |x v| ≤
        (2 : ℝ) * (G.degree v : ℝ) * |x v| := by
      calc
        _ = |hQ.eigenvalues i * x v| := (abs_mul _ _).symm
        _ = |(G.degree v : ℝ) * x v + (∑ w ∈ G.neighborFinset v, x w)| :=
          congrArg abs hrow.symm
        _ ≤ |(G.degree v : ℝ) * x v| + |∑ w ∈ G.neighborFinset v, x w| :=
          abs_add_le _ _
        _ ≤ (G.degree v : ℝ) * |x v| + (G.degree v : ℝ) * |x v| := by
          rw [abs_mul, abs_of_nonneg
            (show (0 : ℝ) ≤ (G.degree v : ℝ) from Nat.cast_nonneg _)]
          exact add_le_add le_rfl hsum
        _ = _ := by ring
    have hlambda : |hQ.eigenvalues i| ≤ (2 : ℝ) * (G.degree v : ℝ) :=
      le_of_mul_le_mul_right hmul hm
    have hdNat : G.degree v + 1 ≤ Fintype.card V :=
      Nat.succ_le_of_lt (G.degree_lt_card_verts v)
    have hd : (G.degree v : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hdNat
    calc
      hQ.eigenvalues i ≤ |hQ.eigenvalues i| := le_abs_self _
      _ ≤ (2 : ℝ) * (G.degree v : ℝ) := hlambda
      _ ≤ 2 * ((Fintype.card V : ℝ) - 1) := by linarith only [hd]
  have hs : sSup (Set.range hQ.eigenvalues) ≤
      2 * ((Fintype.card V : ℝ) - 1) := by
    apply csSup_le (Set.range_nonempty hQ.eigenvalues)
    rintro _ ⟨i, rfl⟩
    exact hbound i
  change (1 / 2 : ℝ) *
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range hQ.eigenvalues)) + 1 ≤
      (Fintype.card V : ℝ)
  simp only [if_neg hcard]
  linarith only [hs]

theorem model_ad89177ba7a4bf76dbff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (39999999 / 10000000 : ℝ)))) :
    (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) - (((2 : ℝ) * (G.cliqueNum : ℝ)) * ((G.cliqueNum : ℝ) - (1 : ℝ))))) := by
  sorry
