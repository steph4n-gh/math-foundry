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
  classical
  have hn3R : (3 : ℝ) < (Fintype.card V : ℝ) := by
    linarith only [h_guard.2]
  have hn3 : 3 < Fintype.card V := by exact_mod_cast hn3R
  have hn2 : 2 ≤ Fintype.card V := by omega
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := h_guard.1.nonempty
  let n : ℝ := Fintype.card V
  let k : ℝ := G.cliqueNum
  let c : ℝ := 2 * (k - 1)
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  let Q : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
  let hQ : Q.IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  let q : ℝ := sSup (Set.range hQ.eigenvalues)
  let j₂ : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let a : ℝ := hL.eigenvalues₀ j₂
  simp only [if_neg hn0, if_pos h_guard.1, dif_pos hn2]
  change n * q * (q - c) ≥ a * (n * q - 2 * k * (k - 1))
  have hc_rewrite : 2 * k * (k - 1) = c * k := by
    dsimp only [c]
    ring
  rw [hc_rewrite]
  have hnpos : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < Fintype.card V from by omega)
  have hkNat : 0 < G.cliqueNum :=
    Nat.pos_of_ne_zero G.cliqueNum_ne_zero_of_finite
  have hkpos : 0 < k := by
    dsimp only [k]
    exact_mod_cast hkNat
  have hkn : k ≤ n := composed_2cd2dd810fbb9720 G
  have hqmin : c ≤ q := by
    have hh := hull_clique_number_le_0_5_signless_laplacian_spectral_radius_1_fe853c08d6ab G
    simp only [if_neg hn0] at hh
    change k ≤ (1 / 2 : ℝ) * q + 1 at hh
    dsimp only [c]
    linarith only [hh]
  by_cases hkn_eq : k = n
  · have hh := hull3d_order_ge_0_0_5_laplacian_spectral_radius_signless_laplacian_spectral_radius_1_is_connected_d400e6f639cf G h_guard.1
    simp only [if_neg hn0] at hh
    change (1 / 2 : ℝ) * q + 1 ≤ n at hh
    have hqe : q = c := by
      dsimp only [c] at hqmin ⊢
      linarith only [hh, hqmin, hkn_eq]
    rw [hqe, hkn_eq]
    nlinarith only []
  have hklt : k < n := lt_of_le_of_ne hkn hkn_eq
  have hdiag (M : Matrix V V ℝ) (hM : M.IsHermitian) (f : V → ℝ) :
      dotProduct f (Matrix.mulVec M f) =
        ∑ i : V, hM.eigenvalues i *
          (inner ℝ (hM.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2 := by
    let z : EuclideanSpace ℝ V := WithLp.toLp 2 f
    have hsym : M.toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
    have heig (i : V) :
        M.toEuclideanLin (hM.eigenvectorBasis i) =
          hM.eigenvalues i • hM.eigenvectorBasis i := by
      apply PiLp.ext
      intro j
      simpa only [Matrix.toLpLin_apply, PiLp.toLp_apply, PiLp.smul_apply,
        Pi.smul_apply, smul_eq_mul] using
        congrFun (hM.mulVec_eigenvectorBasis i) j
    have hh : inner ℝ z (M.toEuclideanLin z) =
        ∑ i : V, hM.eigenvalues i *
          (inner ℝ (hM.eigenvectorBasis i) z) ^ 2 := by
      rw [← hM.eigenvectorBasis.sum_inner_mul_inner z (M.toEuclideanLin z)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hsym (hM.eigenvectorBasis i) z, heig i,
        real_inner_smul_left, real_inner_comm z (hM.eigenvectorBasis i)]
      ring
    simpa only [z, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] using hh
  have hmass (M : Matrix V V ℝ) (hM : M.IsHermitian) (f : V → ℝ) :
      (∑ i : V,
        (inner ℝ (hM.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2) =
        dotProduct f f := by
    let z : EuclideanSpace ℝ V := WithLp.toLp 2 f
    change (∑ i : V, (inner ℝ (hM.eigenvectorBasis i) z) ^ 2) =
      dotProduct f f
    calc
      _ = inner ℝ z z := by
        simpa only [real_inner_comm z, pow_two] using
          hM.eigenvectorBasis.sum_inner_mul_inner z z
      _ = dotProduct f f := by
        simp only [z, EuclideanSpace.inner_toLp_toLp, star_trivial]
  have hupper (f : V → ℝ) :
      dotProduct f (Matrix.mulVec Q f) ≤ q * dotProduct f f := by
    calc
      _ = ∑ i : V, hQ.eigenvalues i *
          (inner ℝ (hQ.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2 :=
        hdiag Q hQ f
      _ ≤ ∑ i : V, q *
          (inner ℝ (hQ.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (le_csSup (Set.finite_range hQ.eigenvalues).bddAbove ⟨i, rfl⟩)
          (sq_nonneg _)
      _ = q * dotProduct f f := by
        rw [← Finset.mul_sum, hmass Q hQ f]
  have hLnonneg (v : V) : 0 ≤ hL.eigenvalues v := by
    rw [hL.eigenvalues_eq v]
    simpa using (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg
      (⇑(hL.eigenvectorBasis v))
  have hzero : 0 ∈ Set.range hL.eigenvalues := by
    rw [← hL.spectrum_real_eq_range_eigenvalues]
    exact G.zero_mem_spectrum_lapMatrix ℝ
  obtain ⟨w, hw⟩ := hzero
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let v₀ : V := e last
  have hvalue (v : V) : hL.eigenvalues v = hL.eigenvalues₀ (e.symm v) := rfl
  have hv₀ : e.symm v₀ = last := e.symm_apply_apply last
  have hlastzero : hL.eigenvalues v₀ = 0 := by
    apply le_antisymm
    · calc
        hL.eigenvalues v₀ = hL.eigenvalues₀ last := by
          rw [hvalue v₀, hv₀]
        _ ≤ hL.eigenvalues₀ (e.symm w) := by
          apply hL.eigenvalues₀_antitone
          change (e.symm w).val ≤ Fintype.card V - 1
          omega
        _ = 0 := by rw [← hvalue w, hw]
    · exact hLnonneg v₀
  have hker : Matrix.mulVec L (⇑(hL.eigenvectorBasis v₀)) = 0 := by
    rw [hL.mulVec_eigenvectorBasis v₀, hlastzero, zero_smul]
  have hconst (v : V) :
      (hL.eigenvectorBasis v₀) v = (hL.eigenvectorBasis v₀) v₀ :=
    (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hker)
      v v₀ (h_guard.1 v v₀)
  have horth (f : V → ℝ) (hf : (∑ v : V, f v) = 0) :
      inner ℝ (hL.eigenvectorBasis v₀) (WithLp.toLp 2 f) = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ v : V, f v * (hL.eigenvectorBasis v₀) v) = 0
    simp only [hconst, ← Finset.sum_mul, hf, zero_mul]
  have hlower (f : V → ℝ) (hf : (∑ v : V, f v) = 0) :
      a * dotProduct f f ≤ dotProduct f (Matrix.mulVec L f) := by
    calc
      a * dotProduct f f = ∑ i : V, a *
          (inner ℝ (hL.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2 := by
        rw [← hmass L hL f, Finset.mul_sum]
      _ ≤ ∑ i : V, hL.eigenvalues i *
          (inner ℝ (hL.eigenvectorBasis i) (WithLp.toLp 2 f)) ^ 2 := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hi : e.symm v = last
        · have hv' : v = v₀ := e.symm.injective (hi.trans hv₀.symm)
          subst v
          simp [horth f hf]
        · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          rw [hvalue v]
          change hL.eigenvalues₀ j₂ ≤ hL.eigenvalues₀ (e.symm v)
          apply hL.eigenvalues₀_antitone
          change (e.symm v).val ≤ Fintype.card V - 2
          have hne : (e.symm v).val ≠ Fintype.card V - 1 := by
            intro hh
            apply hi
            apply Fin.ext
            exact hh
          omega
      _ = dotProduct f (Matrix.mulVec L f) := (hdiag L hL f).symm
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  let y : V → ℝ := fun v => if v ∈ s then 1 else 0
  let z : V → ℝ := 1 - y
  have hysum : (∑ v : V, y v) = k := by
    simp only [y, Finset.sum_ite_mem_eq, Finset.sum_const,
      nsmul_eq_mul, mul_one, hs.card_eq, k]
  have hyy : dotProduct y y = k := by
    calc
      _ = ∑ v : V, y v := by
        apply Finset.sum_congr rfl
        intro v hvu
        by_cases hv : v ∈ s <;> simp [y, hv]
      _ = k := hysum
  have hyone : dotProduct y (1 : V → ℝ) = k := by
    simpa only [dotProduct, Pi.one_apply, mul_one] using hysum
  have h1y : dotProduct (1 : V → ℝ) y = k :=
    (dotProduct_comm _ _).trans hyone
  have h11 : dotProduct (1 : V → ℝ) (1 : V → ℝ) = n := by
    simp [dotProduct, n]
  have hyz : dotProduct y z = 0 := by
    change dotProduct y ((1 : V → ℝ) - y) = 0
    rw [dotProduct_sub, hyone, hyy, sub_self]
  have hzy : dotProduct z y = 0 := (dotProduct_comm _ _).trans hyz
  have hzz : dotProduct z z = n - k := by
    simp only [z, sub_dotProduct, dotProduct_sub, hyy, hyone, h1y, h11] <;> ring
  have hznonneg (v : V) : 0 ≤ z v := by
    by_cases hv : v ∈ s <;> simp [z, y, hv]
  have hAy (v : V) (hv : v ∈ s) :
      Matrix.mulVec (G.adjMatrix ℝ) y v = k - 1 := by
    change (∑ w : V, (G.adjMatrix ℝ) v w * y w) = k - 1
    calc
      _ = ∑ w ∈ s.erase v, (G.adjMatrix ℝ) v w * y w := by
        symm
        apply Finset.sum_subset (Finset.subset_univ (s.erase v))
        intro w hwu hw
        by_cases hws : w ∈ s
        · have hwv : w = v := by
            by_contra hne
            exact hw (Finset.mem_erase.mpr ⟨hne, hws⟩)
          subst w
          simp
        · simp [y, hws]
      _ = ∑ _w ∈ s.erase v, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hw' := Finset.mem_erase.mp hw
        have hadj : G.Adj v w := hs.isClique hv hw'.2 hw'.1.symm
        simp [y, hw'.2, hadj]
      _ = k - 1 := by
        have hcardNat : (s.erase v).card + 1 = G.cliqueNum := by
          rw [Finset.card_erase_of_mem hv, hs.card_eq]
          omega
        have hcardReal : ((s.erase v).card : ℝ) + 1 = k := by
          dsimp only [k]
          exact_mod_cast hcardNat
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        linarith only [hcardReal]
  have hAyy : dotProduct y (Matrix.mulVec (G.adjMatrix ℝ) y) = k * (k - 1) := by
    calc
      _ = ∑ v : V, if v ∈ s then Matrix.mulVec (G.adjMatrix ℝ) y v else 0 := by
        apply Finset.sum_congr rfl
        intro v hvu
        by_cases hv : v ∈ s <;> simp [y, hv]
      _ = ∑ v ∈ s, Matrix.mulVec (G.adjMatrix ℝ) y v :=
        Finset.sum_ite_mem_eq s _
      _ = ∑ _v ∈ s, (k - 1) :=
        Finset.sum_congr rfl (fun v hv => hAy v hv)
      _ = k * (k - 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hs.card_eq, k]
  let b : ℝ := dotProduct y (Matrix.mulVec L y)
  let az : ℝ := dotProduct z (Matrix.mulVec (G.adjMatrix ℝ) z)
  have haz : 0 ≤ az := by
    dsimp only [az]
    rw [G.dotProduct_mulVec_adjMatrix]
    apply Finset.sum_nonneg
    intro v hv
    apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact mul_nonneg (hznonneg v) (hznonneg w)
    · exact le_rfl
  have hLone : Matrix.mulVec L (1 : V → ℝ) = 0 :=
    G.lapMatrix_mulVec_one_eq_zero ℝ
  have hLz : Matrix.mulVec L z = -(Matrix.mulVec L y) := by
    change Matrix.mulVec L ((1 : V → ℝ) - y) = -(Matrix.mulVec L y)
    rw [Matrix.mulVec_sub, hLone, zero_sub]
  have h1Ly : dotProduct (1 : V → ℝ) (Matrix.mulVec L y) = 0 := by
    calc
      _ = dotProduct y (Matrix.mulVec L (1 : V → ℝ)) :=
        (G.isSymm_lapMatrix ℝ).dotProduct_mulVec_comm
      _ = 0 := by rw [hLone] <;> simp
  have hLyz : dotProduct y (Matrix.mulVec L z) = -b := by
    rw [hLz, dotProduct_neg]
  have hLzz : dotProduct z (Matrix.mulVec L z) = b := by
    change dotProduct ((1 : V → ℝ) - y) (Matrix.mulVec L z) = b
    rw [hLz, dotProduct_neg, sub_dotProduct, h1Ly]
    change -(0 - b) = b
    ring
  have hDyz : dotProduct y (Matrix.mulVec (G.degMatrix ℝ) z) = 0 := by
    change (∑ v : V, y v * (Matrix.mulVec (G.degMatrix ℝ) z) v) = 0
    simp only [G.degMatrix_mulVec_apply]
    apply Finset.sum_eq_zero
    intro v hvu
    by_cases hv : v ∈ s <;> simp [z, y, hv]
  have hQ1 : Q = (2 : ℝ) • G.degMatrix ℝ - L := by
    ext v w
    simp only [Q, L, SimpleGraph.lapMatrix, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  have hQ2 : Q = L + (2 : ℝ) • G.adjMatrix ℝ := by
    ext v w
    simp only [Q, L, SimpleGraph.lapMatrix, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;> ring
  have hQyy : dotProduct y (Matrix.mulVec Q y) = b + c * k := by
    rw [hQ2, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, hAyy]
    change b + 2 * (k * (k - 1)) = b + c * k
    dsimp only [c]
    ring
  have hQyz : dotProduct y (Matrix.mulVec Q z) = b := by
    rw [hQ1, Matrix.sub_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, hDyz, hLyz] <;> ring
  have hQsym : Q.IsSymm := (G.isSymm_degMatrix ℝ).add G.isSymm_adjMatrix
  have hQzy : dotProduct z (Matrix.mulVec Q y) = b := by
    calc
      _ = dotProduct y (Matrix.mulVec Q z) := hQsym.dotProduct_mulVec_comm
      _ = b := hQyz
  have hQzz : dotProduct z (Matrix.mulVec Q z) = b + 2 * az := by
    simp only [hQ2, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, hLzz, az]
  let f : V → ℝ := n • y - k • (1 : V → ℝ)
  have hfsum : (∑ v : V, f v) = 0 := by
    simp only [f, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hysum, n] <;> ring
  have hfnorm : dotProduct f f = n * k * (n - k) := by
    simp only [f, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hyy, hyone, h1y, h11] <;> ring
  have hfvalue : dotProduct f (Matrix.mulVec L f) = n ^ 2 * b := by
    simp only [f, Matrix.mulVec_sub, Matrix.mulVec_smul, hLone,
      smul_zero, sub_zero, sub_dotProduct, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, h1Ly, b] <;> ring
  have hcut : a * k * (n - k) ≤ n * b := by
    have hh := hlower f hfsum
    rw [hfnorm, hfvalue] at hh
    have hh' : n * (a * k * (n - k)) ≤ n * (n * b) := by
      convert hh using 1 <;> ring
    exact le_of_mul_le_mul_left hh' hnpos
  have hpoly (r t : ℝ) :
      n * c * k * r ^ 2 + a * k * (n - k) * (r + t) ^ 2 ≤
        n * q * (k * r ^ 2 + (n - k) * t ^ 2) := by
    let x : V → ℝ := r • y + t • z
    have hxx : dotProduct x x = k * r ^ 2 + (n - k) * t ^ 2 := by
      simp only [x, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hyy, hyz, hzy, hzz] <;> ring
    have hxQ : dotProduct x (Matrix.mulVec Q x) =
        (b + c * k) * r ^ 2 + 2 * b * r * t + (b + 2 * az) * t ^ 2 := by
      simp only [x, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hQyy, hQyz, hQzy, hQzz] <;> ring
    have hh := hupper x
    rw [hxx, hxQ] at hh
    have hscl := mul_le_mul_of_nonneg_left hh hnpos.le
    have hccl := mul_le_mul_of_nonneg_right hcut (sq_nonneg (r + t))
    have hextra : 0 ≤ n * (2 * az * t ^ 2) :=
      mul_nonneg hnpos.le
        (mul_nonneg (mul_nonneg (by norm_num) haz) (sq_nonneg t))
    nlinarith only [hscl, hccl, hextra]
  let p11 : ℝ := k * (n * (q - c) - a * (n - k))
  let p22 : ℝ := (n - k) * (n * q - a * k)
  let p12 : ℝ := a * k * (n - k)
  have hquadratic (t : ℝ) :
      0 ≤ p22 * (t * t) + (-2 * p12) * t + p11 := by
    have hh := hpoly 1 t
    dsimp only [p11, p22, p12]
    nlinarith only [hh]
  have hdisc := discrim_le_zero hquadratic
  change (-2 * p12) ^ 2 - 4 * p22 * p11 ≤ 0 at hdisc
  have hdet : 0 ≤ p11 * p22 - p12 ^ 2 := by
    nlinarith only [hdisc]
  have hfactor : p11 * p22 - p12 ^ 2 =
      n * k * (n - k) * (n * q * (q - c) - a * (n * q - c * k)) := by
    dsimp only [p11, p22, p12]
    ring
  rw [hfactor] at hdet
  have hprodpos : 0 < n * k * (n - k) :=
    mul_pos (mul_pos hnpos hkpos) (sub_pos.mpr hklt)
  have hgap : 0 ≤ n * q * (q - c) - a * (n * q - c * k) := by
    by_contra hh
    have hnegative := mul_neg_of_pos_of_neg hprodpos (lt_of_not_ge hh)
    exact (not_lt_of_ge hdet) hnegative
  exact sub_nonneg.mp hgap
