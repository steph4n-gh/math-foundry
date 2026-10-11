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

theorem hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  rw [if_neg hV]
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
    (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
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
  let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have hnorm : inner ℝ x x = (Fintype.card V : ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x, dotProduct]
  have hinner : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [x, WithLp.ofLp_toLp, star_trivial]
    change (∑ v : V, (1 : ℝ) *
      Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)) v) = _
    simp only [one_mul, SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hV
  apply (div_le_iff₀ hpos).2
  simpa only [if_neg hV, hinner, hnorm] using hq x

theorem hull_spectral_radius_le_1_max_degree_0_e423c6789900 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (G.maxDegree : ℝ) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg G.maxDegree
  · rw [if_neg hV]
    letI : Nonempty V :=
      Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hV)
    let hA := G.isHermitian_adjMatrix ℝ
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        (hA.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    have hw0 : x w ≠ 0 := by
      simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V)
        (fun u => |x u|) Finset.univ_nonempty
    have hp : 0 < |x v| :=
      lt_of_lt_of_le (abs_pos.mpr hw0) (hmax w (Finset.mem_univ w))
    have heq : (∑ u ∈ G.neighborFinset v, x u) =
        hA.eigenvalues i * x v := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply,
        smul_eq_mul] using congrFun (hA.mulVec_eigenvectorBasis i) v
    have habs : |hA.eigenvalues i| * |x v| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        |hA.eigenvalues i| * |x v| =
            |∑ u ∈ G.neighborFinset v, x u| := by
          rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset v, |x u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun u _ => hmax u (Finset.mem_univ u))
        _ = (G.degree v : ℝ) * |x v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have heigen : hA.eigenvalues i ≤ (G.degree v : ℝ) :=
      (le_abs_self _).trans (le_of_mul_le_mul_right habs hp)
    have hdegree : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast (G.degree_le_maxDegree v)
    exact heigen.trans hdegree

theorem model_6915c570cfc511f1f88f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (G.maxDegree : ℝ))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) := by
  classical
  rcases h_guard with ⟨hconn, horder, hdegree_guard⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hle' : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [horder, hle']
  have hV : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  simp only [if_neg hV, if_pos hconn, dif_pos htwo]
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let Q : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let hQ : Q.IsHermitian := (G.isHermitian_degMatrix ℝ).add hA
  let hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  let r : ℝ := sSup (Set.range hA.eigenvalues)
  let q : ℝ := sSup (Set.range hQ.eigenvalues)
  let δ : ℝ := G.maxDegree
  let n : ℝ := Fintype.card V
  let d : ℝ := (2 : ℝ) * (G.edgeFinset.card : ℝ) / n
  let second : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let a : ℝ := hL.eigenvalues₀ second
  change a * (r - d) ≤ (q - 2 * r) * (r + δ)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero hV
  have hquad (M : Matrix V V ℝ) (hM : M.IsHermitian)
      (z : EuclideanSpace ℝ V) :
      inner ℝ (M.toEuclideanLin z) z =
        ∑ j : V, hM.eigenvalues j * (inner ℝ z (hM.eigenvectorBasis j)) ^ 2 := by
    have hsym : M.toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
    have he (j : V) : M.toEuclideanLin (hM.eigenvectorBasis j) =
        hM.eigenvalues j • hM.eigenvectorBasis j := by
      apply WithLp.ofLp_injective 2
      simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
        hM.mulVec_eigenvectorBasis j
    rw [← (hM.eigenvectorBasis).sum_inner_mul_inner (M.toEuclideanLin z) z]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym z (hM.eigenvectorBasis j), he j, inner_smul_right,
      real_inner_comm z (hM.eigenvectorBasis j)]
    ring
  have hparseval (b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V))
      (z : EuclideanSpace ℝ V) :
      (∑ j : V, (inner ℝ z (b j)) ^ 2) = inner ℝ z z := by
    calc
      (∑ j : V, (inner ℝ z (b j)) ^ 2) =
          ∑ j : V, inner ℝ z (b j) * inner ℝ (b j) z := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [real_inner_comm z (b j)]
        ring
      _ = inner ℝ z z := b.sum_inner_mul_inner z z
  have hupper (M : Matrix V V ℝ) (hM : M.IsHermitian)
      (z : EuclideanSpace ℝ V) :
      inner ℝ (M.toEuclideanLin z) z ≤
        sSup (Set.range hM.eigenvalues) * inner ℝ z z := by
    calc
      inner ℝ (M.toEuclideanLin z) z =
          ∑ j : V, hM.eigenvalues j * (inner ℝ z (hM.eigenvectorBasis j)) ^ 2 :=
        hquad M hM z
      _ ≤ ∑ j : V, sSup (Set.range hM.eigenvalues) *
          (inner ℝ z (hM.eigenvectorBasis j)) ^ 2 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
          (le_csSup (Set.finite_range hM.eigenvalues).bddAbove (Set.mem_range_self j))
          (sq_nonneg _))
      _ = sSup (Set.range hM.eigenvalues) * inner ℝ z z := by
        rw [← Finset.mul_sum, hparseval hM.eigenvectorBasis z]
  have hAlow (j : V) : -δ ≤ hA.eigenvalues j := by
    let xx : V → ℝ := ⇑(hA.eigenvectorBasis j)
    have hxx : xx ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hxx
    have hw0 : xx w ≠ 0 := by simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
      (fun u => |xx u|) Finset.univ_nonempty
    have hv : 0 < |xx v| :=
      lt_of_lt_of_le (abs_pos.mpr hw0) (hmax w (Finset.mem_univ w))
    have heq : (∑ u ∈ G.neighborFinset v, xx u) = hA.eigenvalues j * xx v := by
      simpa only [A, SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis j) v
    have habs : |hA.eigenvalues j| * |xx v| ≤ (G.degree v : ℝ) * |xx v| := by
      calc
        |hA.eigenvalues j| * |xx v| = |∑ u ∈ G.neighborFinset v, xx u| := by
          rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset v, |xx u| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |xx v| :=
          Finset.sum_le_sum (fun u _ => hmax u (Finset.mem_univ u))
        _ = (G.degree v : ℝ) * |xx v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have hdeg : (G.degree v : ℝ) ≤ δ := by
      dsimp only [δ]
      exact_mod_cast G.degree_le_maxDegree v
    have habs_eig : |hA.eigenvalues j| ≤ δ :=
      (le_of_mul_le_mul_right habs hv).trans hdeg
    have hneg : -hA.eigenvalues j ≤ |hA.eigenvalues j| := by
      simpa only [abs_neg] using le_abs_self (-hA.eigenvalues j)
    linarith only [hneg, habs_eig]
  have hlower (z : EuclideanSpace ℝ V) :
      -δ * inner ℝ z z ≤ inner ℝ (A.toEuclideanLin z) z := by
    rw [hquad A hA z, ← hparseval hA.eigenvectorBasis z, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (hAlow j) (sq_nonneg _))
  let e : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have he : inner ℝ e e = n := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [e, n, dotProduct]
  let s : ℝ := Real.sqrt n
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hss : s ^ 2 = n := Real.sq_sqrt hn.le
  let u : EuclideanSpace ℝ V := s⁻¹ • e
  have hu : inner ℝ u u = 1 := by
    dsimp only [u]
    rw [real_inner_smul_left, real_inner_smul_right, he, ← hss]
    field_simp [hs] <;> ring
  have hAe : inner ℝ (A.toEuclideanLin e) e =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    dsimp only [A]
    rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [e, WithLp.ofLp_toLp, star_trivial]
    change (∑ v : V, (1 : ℝ) *
      Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)) v) = _
    simp only [one_mul, SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hAu : inner ℝ (A.toEuclideanLin u) u = d := by
    simp only [u, map_smul, real_inner_smul_left, real_inner_smul_right, hAe]
    dsimp only [d]
    rw [← hss]
    field_simp [hs] <;> ring
  have hLe : L.toEuclideanLin e = 0 := by
    apply WithLp.ofLp_injective 2
    simpa only [L, Matrix.toLpLin_apply, e, WithLp.ofLp_toLp, WithLp.ofLp_zero,
      Pi.one_def] using G.lapMatrix_mulVec_one_eq_zero ℝ
  have hLu : L.toEuclideanLin u = 0 := by
    simp only [u, map_smul, hLe, smul_zero]
  have hLnonneg (j : V) : 0 ≤ hL.eigenvalues j := by
    have heq : hL.eigenvalues j = dotProduct (⇑(hL.eigenvectorBasis j))
        (Matrix.mulVec L (⇑(hL.eigenvectorBasis j))) := by
      simpa only [star_trivial, RCLike.re_to_real] using hL.eigenvalues_eq j
    rw [heq]
    simpa only [star_trivial] using
      (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg (⇑(hL.eigenvectorBasis j))
  let idx : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
  have hindex (j : Fin (Fintype.card V)) :
      hL.eigenvalues (idx j) = hL.eigenvalues₀ j := by
    simp only [Matrix.IsHermitian.eigenvalues, idx, Equiv.symm_apply_apply]
  have ha : 0 ≤ a := by
    change 0 ≤ hL.eigenvalues₀ second
    rw [← hindex second]
    exact hLnonneg (idx second)
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let w : V := idx last
  obtain ⟨k, hk⟩ : ∃ k : V, hL.eigenvalues k = 0 := by
    have hz := G.zero_mem_spectrum_lapMatrix ℝ
    rw [hL.spectrum_real_eq_range_eigenvalues] at hz
    exact hz
  have hwzero : hL.eigenvalues w = 0 := by
    apply le_antisymm ?_ (hLnonneg w)
    calc
      hL.eigenvalues w = hL.eigenvalues₀ last := hindex last
      _ ≤ hL.eigenvalues₀ (idx.symm k) := by
        apply hL.eigenvalues₀_antitone
        change (idx.symm k).val ≤ Fintype.card V - 1
        have hlt := (idx.symm k).isLt
        omega
      _ = hL.eigenvalues k := rfl
      _ = 0 := hk
  let v₀ : V := Classical.choice (inferInstance : Nonempty V)
  let c : ℝ := (hL.eigenvectorBasis w) v₀
  have hbw : hL.eigenvectorBasis w = c • e := by
    have hv : Matrix.mulVec L (⇑(hL.eigenvectorBasis w)) = 0 := by
      rw [hL.mulVec_eigenvectorBasis w, hwzero, zero_smul]
    have hc := G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hv
    apply WithLp.ofLp_injective 2
    funext v
    change (hL.eigenvectorBasis w) v = c * 1
    rw [mul_one]
    exact hc v v₀ (hconn.preconnected v v₀)
  have hbw' : hL.eigenvectorBasis w = (c * s) • u := by
    rw [hbw]
    simp only [u, smul_smul, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  have hP (z : EuclideanSpace ℝ V) (hz : inner ℝ z u = 0) :
      a * inner ℝ z z ≤ inner ℝ (L.toEuclideanLin z) z := by
    calc
      a * inner ℝ z z =
          ∑ j : V, a * (inner ℝ z (hL.eigenvectorBasis j)) ^ 2 := by
        rw [← hparseval hL.eigenvectorBasis z, Finset.mul_sum]
      _ ≤ ∑ j : V, hL.eigenvalues j * (inner ℝ z (hL.eigenvectorBasis j)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hjw : j = w
        · subst j
          simp [hbw', real_inner_smul_right, hz]
        · have hneq : idx.symm j ≠ last := by
            intro hh
            apply hjw
            simpa only [Equiv.apply_symm_apply, w] using congrArg idx hh
          have hm : idx.symm j ≤ second := by
            change (idx.symm j).val ≤ Fintype.card V - 2
            have hlt := (idx.symm j).isLt
            have hvne : (idx.symm j).val ≠ Fintype.card V - 1 := by
              intro hh
              apply hneq
              apply Fin.ext
              exact hh
            omega
          have hle : a ≤ hL.eigenvalues j := by
            change hL.eigenvalues₀ second ≤ hL.eigenvalues₀ (idx.symm j)
            exact hL.eigenvalues₀_antitone hm
          exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = inner ℝ (L.toEuclideanLin z) z := (hquad L hL z).symm
  obtain ⟨i, _, himax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    hA.eigenvalues Finset.univ_nonempty
  have hi : hA.eigenvalues i = r := by
    apply le_antisymm
    · exact le_csSup (Set.finite_range hA.eigenvalues).bddAbove (Set.mem_range_self i)
    · apply csSup_le (Set.range_nonempty hA.eigenvalues)
      rintro _ ⟨j, rfl⟩
      exact himax j (Finset.mem_univ j)
  let x : EuclideanSpace ℝ V := hA.eigenvectorBasis i
  have hxunit : inner ℝ x x = 1 := by
    change inner ℝ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = 1
    rw [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have hAx : A.toEuclideanLin x = r • x := by
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, x, hi] using
      hA.mulVec_eigenvectorBasis i
  have hAsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hLsym : L.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hL
  have hmat : Q = L + (2 : ℝ) • A := by
    ext v w
    simp only [Q, L, A, SimpleGraph.lapMatrix, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hQx : inner ℝ (Q.toEuclideanLin x) x =
      inner ℝ (L.toEuclideanLin x) x + 2 * r := by
    rw [hmat]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      inner_add_left, real_inner_smul_left, hAx, hxunit, mul_one]
  have hqb := hupper Q hQ x
  rw [hQx, hxunit, mul_one] at hqb
  have hEnergy : inner ℝ (L.toEuclideanLin x) x ≤ q - 2 * r := by
    change inner ℝ (L.toEuclideanLin x) x + 2 * r ≤ q at hqb
    linarith only [hqb]
  let t : ℝ := inner ℝ x u
  have htxu : inner ℝ x u = t := rfl
  have htux : inner ℝ u x = t := real_inner_comm x u
  let z : EuclideanSpace ℝ V := x - t • u
  have hzorth : inner ℝ z u = 0 := by
    simp only [z, inner_sub_left, real_inner_smul_left, htxu, hu, mul_one, sub_self]
  have hzNorm : inner ℝ z z = 1 - t ^ 2 := by
    simp only [z, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxunit, hu, htxu, htux]
    ring
  have hLxu : inner ℝ (L.toEuclideanLin x) u = 0 := by
    rw [hLsym x u, hLu, inner_zero_right]
  have hzEnergy : inner ℝ (L.toEuclideanLin z) z =
      inner ℝ (L.toEuclideanLin x) x := by
    simp only [z, map_sub, map_smul, hLu, smul_zero, sub_zero,
      inner_sub_right, real_inner_smul_right, hLxu, mul_zero]
  have hgapQ : a * (1 - t ^ 2) ≤ q - 2 * r := by
    have hp := hP z hzorth
    rw [hzNorm, hzEnergy] at hp
    exact hp.trans hEnergy
  let y : EuclideanSpace ℝ V := u - t • x
  have hyNorm : inner ℝ y y = 1 - t ^ 2 := by
    simp only [y, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxunit, hu, htxu, htux]
    ring
  have hAxu : inner ℝ (A.toEuclideanLin x) u = r * t := by
    rw [hAx, real_inner_smul_left, htxu]
  have hAux : inner ℝ (A.toEuclideanLin u) x = r * t := by
    rw [hAsym u x, hAx, real_inner_smul_right, htux]
  have hAxx : inner ℝ (A.toEuclideanLin x) x = r := by
    rw [hAx, real_inner_smul_left, hxunit, mul_one]
  have hyEnergy : inner ℝ (A.toEuclideanLin y) y = d - r * t ^ 2 := by
    simp only [y, map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hAu, hAux, hAxu, hAxx]
    ring
  have hgapA : r - d ≤ (r + δ) * (1 - t ^ 2) := by
    have hl := hlower y
    rw [hyNorm, hyEnergy] at hl
    nlinarith only [hl]
  have hdnonneg : 0 ≤ d := by
    change 0 ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) / n
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
  have hdr : d ≤ r := by
    simpa only [if_neg hV] using hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 G
  have hδ : 0 ≤ δ := Nat.cast_nonneg _
  have hrd : 0 ≤ r + δ := add_nonneg (hdnonneg.trans hdr) hδ
  calc
    a * (r - d) ≤ a * ((r + δ) * (1 - t ^ 2)) :=
      mul_le_mul_of_nonneg_left hgapA ha
    _ = (a * (1 - t ^ 2)) * (r + δ) := by ring
    _ ≤ (q - 2 * r) * (r + δ) :=
      mul_le_mul_of_nonneg_right hgapQ hrd

theorem model_480476520e017d731b8e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (((2 : ℝ) * (G.maxDegree : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) := by
  classical
  rcases h_guard with ⟨hconn, horder⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hle' : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [horder, hle']
  have hV : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  simp only [if_neg hV, if_pos hconn, dif_pos htwo]
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let q : ℝ := sSup (Set.range ((G.isHermitian_degMatrix ℝ).add
    (G.isHermitian_adjMatrix ℝ)).eigenvalues)
  let δ : ℝ := G.maxDegree
  let d : ℝ := (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)
  let a : ℝ := (G.isHermitian_lapMatrix ℝ).eigenvalues₀
    ⟨Fintype.card V - 2, by omega⟩
  change a * (r - d) ≤ (2 * δ) * (q - 2 * r)
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hV
  have hd : 0 ≤ d := by
    dsimp only [d]
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
  have hdr : d ≤ r := by
    simpa only [if_neg hV] using
      hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 G
  have hrδ : r ≤ δ := by
    simpa only [if_neg hV] using
      hull_spectral_radius_le_1_max_degree_0_e423c6789900 G
  by_cases hzero : G.maxDegree = 0
  · have hδzero : δ = 0 := by
      simp only [δ, hzero, Nat.cast_zero]
    have hrzero : r = 0 := by
      linarith only [hd, hdr, hrδ, hδzero]
    have hdzero : d = 0 := by
      linarith only [hd, hdr, hrzero]
    simp only [hδzero, hrzero, hdzero, sub_self, mul_zero, zero_mul, le_refl]
  · have hδone_nat : 1 ≤ G.maxDegree := by omega
    have hδone : (1 : ℝ) ≤ δ := by
      dsimp only [δ]
      exact_mod_cast hδone_nat
    have hdegree_guard : (G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ) := by
      change (9999999 / 10000000 : ℝ) ≤ δ
      linarith only [hδone]
    have hbase := model_6915c570cfc511f1f88f G
      ⟨hconn, horder, hdegree_guard⟩
    simp only [if_neg hV, if_pos hconn, dif_pos htwo] at hbase
    change a * (r - d) ≤ (q - 2 * r) * (r + δ) at hbase
    have ha : 0 ≤ a := by
      let hL := G.isHermitian_lapMatrix ℝ
      let idx : Fin (Fintype.card V) ≃ V :=
        Fintype.equivOfCardEq (Fintype.card_fin _)
      let second : Fin (Fintype.card V) :=
        ⟨Fintype.card V - 2, by omega⟩
      have hindex : hL.eigenvalues (idx second) = a := by
        change hL.eigenvalues (idx second) = hL.eigenvalues₀ second
        simp only [Matrix.IsHermitian.eigenvalues, idx, Equiv.symm_apply_apply]
      rw [← hindex]
      have heq : hL.eigenvalues (idx second) =
          dotProduct (⇑(hL.eigenvectorBasis (idx second)))
            (Matrix.mulVec (G.lapMatrix ℝ)
              (⇑(hL.eigenvectorBasis (idx second)))) := by
        simpa only [star_trivial, RCLike.re_to_real] using
          hL.eigenvalues_eq (idx second)
      rw [heq]
      simpa only [star_trivial] using
        (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg
          (⇑(hL.eigenvectorBasis (idx second)))
    have hprod : 0 ≤ (q - 2 * r) * (r + δ) :=
      (mul_nonneg ha (sub_nonneg.mpr hdr)).trans hbase
    have hfactor : 0 < r + δ := by
      linarith only [hd, hdr, hδone]
    have hgap : 0 ≤ q - 2 * r :=
      le_of_mul_le_mul_right
        (show (0 : ℝ) * (r + δ) ≤ (q - 2 * r) * (r + δ) by
          simpa only [zero_mul] using hprod)
        hfactor
    have hfactor_le : r + δ ≤ 2 * δ := by
      linarith only [hrδ]
    calc
      a * (r - d) ≤ (q - 2 * r) * (r + δ) := hbase
      _ ≤ (q - 2 * r) * (2 * δ) :=
        mul_le_mul_of_nonneg_left hfactor_le hgap
      _ = (2 * δ) * (q - 2 * r) := mul_comm _ _

theorem model_bde7d8e48dd145e3a003 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) * ((((8 : ℝ) * (Fintype.card V : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) + (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2))) ≥ ((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2)) := by
  classical
  rcases h_guard with ⟨hconn, horder, hdegree_guard⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hle' : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [horder, hle']
  have hV : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  simp only [if_neg hV, if_pos hconn, dif_pos htwo]
  let A : Matrix V V ℝ := G.adjMatrix ℝ
  let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
  let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) := hA.eigenvectorBasis
  let r : ℝ := sSup (Set.range hA.eigenvalues)
  let q : ℝ := sSup (Set.range ((G.isHermitian_degMatrix ℝ).add
    (G.isHermitian_adjMatrix ℝ)).eigenvalues)
  let D : ℝ := G.maxDegree
  let m : ℝ := G.minDegree
  let n : ℝ := Fintype.card V
  let d : ℝ := (2 : ℝ) * (G.edgeFinset.card : ℝ) / n
  let a : ℝ := (G.isHermitian_lapMatrix ℝ).eigenvalues₀
    ⟨Fintype.card V - 2, by omega⟩
  change a * (D - m) ^ 2 ≤ (q - 2 * r) * (8 * n * D ^ 2 + (D - m) ^ 2)
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast Nat.pos_of_ne_zero hV
  have hD : 0 < D := by
    change 0 < (G.maxDegree : ℝ)
    linarith only [hdegree_guard]
  have hd : 0 ≤ d := by
    change 0 ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) / n
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hn.le
  have hdr : d ≤ r := by
    simpa only [if_neg hV] using
      hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 G
  have hrD : r ≤ D := by
    simpa only [if_neg hV] using
      hull_spectral_radius_le_1_max_degree_0_e423c6789900 G
  have hdD : d ≤ D := hdr.trans hrD
  have ha : 0 ≤ a := by
    let hL := G.isHermitian_lapMatrix ℝ
    let idx : Fin (Fintype.card V) ≃ V :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    let second : Fin (Fintype.card V) :=
      ⟨Fintype.card V - 2, by omega⟩
    have hindex : hL.eigenvalues (idx second) = a := by
      change hL.eigenvalues (idx second) = hL.eigenvalues₀ second
      simp only [Matrix.IsHermitian.eigenvalues, idx, Equiv.symm_apply_apply]
    rw [← hindex]
    have heq : hL.eigenvalues (idx second) =
        dotProduct (⇑(hL.eigenvectorBasis (idx second)))
          (Matrix.mulVec (G.lapMatrix ℝ)
            (⇑(hL.eigenvectorBasis (idx second)))) := by
      simpa only [star_trivial, RCLike.re_to_real] using
        hL.eigenvalues_eq (idx second)
    rw [heq]
    simpa only [star_trivial] using
      (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg
        (⇑(hL.eigenvectorBasis (idx second)))
  have hbase := model_480476520e017d731b8e G ⟨hconn, horder⟩
  simp only [if_neg hV, if_pos hconn, dif_pos htwo] at hbase
  change a * (r - d) ≤ (2 * D) * (q - 2 * r) at hbase
  have hgap : 0 ≤ q - 2 * r := by
    have hp : 0 ≤ (2 * D) * (q - 2 * r) :=
      (mul_nonneg ha (sub_nonneg.mpr hdr)).trans hbase
    exact le_of_mul_le_mul_left
      (show (2 * D) * (0 : ℝ) ≤ (2 * D) * (q - 2 * r) by
        simpa only [mul_zero] using hp)
      (by linarith only [hD])
  have hsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have heig (j : V) : A.toEuclideanLin (b j) = hA.eigenvalues j • b j := by
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
      hA.mulVec_eigenvectorBasis j
  have hAlow (j : V) : -D ≤ hA.eigenvalues j := by
    let xx : V → ℝ := ⇑(hA.eigenvectorBasis j)
    have hxx : xx ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero j)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hxx
    have hw0 : xx w ≠ 0 := by simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset V)
      (fun u => |xx u|) Finset.univ_nonempty
    have hv : 0 < |xx v| :=
      lt_of_lt_of_le (abs_pos.mpr hw0) (hmax w (Finset.mem_univ w))
    have heq : (∑ u ∈ G.neighborFinset v, xx u) = hA.eigenvalues j * xx v := by
      simpa only [A, SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using
        congrFun (hA.mulVec_eigenvectorBasis j) v
    have habs : |hA.eigenvalues j| * |xx v| ≤ (G.degree v : ℝ) * |xx v| := by
      calc
        |hA.eigenvalues j| * |xx v| = |∑ u ∈ G.neighborFinset v, xx u| := by
          rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset v, |xx u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |xx v| :=
          Finset.sum_le_sum (fun u _ => hmax u (Finset.mem_univ u))
        _ = (G.degree v : ℝ) * |xx v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have hdeg : (G.degree v : ℝ) ≤ D := by
      dsimp only [D]
      exact_mod_cast G.degree_le_maxDegree v
    have habs_eig : |hA.eigenvalues j| ≤ D :=
      (le_of_mul_le_mul_right habs hv).trans hdeg
    have hneg : -hA.eigenvalues j ≤ |hA.eigenvalues j| := by
      simpa only [abs_neg] using le_abs_self (-hA.eigenvalues j)
    linarith only [hneg, habs_eig]
  have hAhigh (j : V) : hA.eigenvalues j ≤ r :=
    le_csSup (Set.finite_range hA.eigenvalues).bddAbove (Set.mem_range_self j)
  have hpoly (j : V) : (hA.eigenvalues j) ^ 2 ≤
      (r - D) * hA.eigenvalues j + r * D := by
    have hp := mul_nonneg (sub_nonneg.mpr (hAhigh j))
      (show 0 ≤ hA.eigenvalues j + D by linarith only [hAlow j])
    nlinarith only [hp]
  let e : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have he : inner ℝ e e = n := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [e, n, dotProduct]
  have hAevec : A.toEuclideanLin e =
      WithLp.toLp 2 (fun v : V => (G.degree v : ℝ)) := by
    apply WithLp.ofLp_injective 2
    funext v
    simp only [A, e, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const, nsmul_eq_mul,
      mul_one, SimpleGraph.card_neighborFinset_eq_degree]
  have hsum : (∑ v : V, (G.degree v : ℝ)) = n * d := by
    have hs : (∑ v : V, (G.degree v : ℝ)) =
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hs]
    dsimp only [d]
    field_simp [ne_of_gt hn] <;> ring
  have hfirst : inner ℝ (A.toEuclideanLin e) e = n * d := by
    rw [hAevec, EuclideanSpace.inner_eq_star_dotProduct]
    simpa [e, dotProduct] using hsum
  have hsecond : inner ℝ (A.toEuclideanLin e) (A.toEuclideanLin e) =
      ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    simp only [hAevec, EuclideanSpace.inner_eq_star_dotProduct,
      WithLp.ofLp_toLp, star_trivial, dotProduct, pow_two]
  have hparseval (bb : OrthonormalBasis V ℝ (EuclideanSpace ℝ V))
      (z : EuclideanSpace ℝ V) :
      (∑ j : V, (inner ℝ z (bb j)) ^ 2) = inner ℝ z z := by
    calc
      (∑ j : V, (inner ℝ z (bb j)) ^ 2) =
          ∑ j : V, inner ℝ z (bb j) * inner ℝ (bb j) z := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [real_inner_comm z (bb j)]
        ring
      _ = inner ℝ z z := bb.sum_inner_mul_inner z z
  have hcoeff (j : V) : inner ℝ (A.toEuclideanLin e) (b j) =
      hA.eigenvalues j * inner ℝ e (b j) := by
    rw [hsym e (b j), heig j, real_inner_smul_right]
  let c : V → ℝ := fun j => (inner ℝ e (b j)) ^ 2
  have hc : (∑ j : V, c j) = n := by
    change (∑ j : V, (inner ℝ e (b j)) ^ 2) = n
    rw [hparseval b e, he]
  have hf : (∑ j : V, hA.eigenvalues j * c j) = n * d := by
    calc
      (∑ j : V, hA.eigenvalues j * c j) =
          ∑ j : V, inner ℝ (A.toEuclideanLin e) (b j) * inner ℝ (b j) e := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff j, real_inner_comm e (b j)]
        dsimp only [c]
        ring
      _ = inner ℝ (A.toEuclideanLin e) e :=
        b.sum_inner_mul_inner (A.toEuclideanLin e) e
      _ = n * d := hfirst
  have hf2 : (∑ j : V, (hA.eigenvalues j) ^ 2 * c j) =
      ∑ v : V, (G.degree v : ℝ) ^ 2 := by
    calc
      (∑ j : V, (hA.eigenvalues j) ^ 2 * c j) =
          ∑ j : V, (inner ℝ (A.toEuclideanLin e) (b j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff j]
        dsimp only [c]
        ring
      _ = inner ℝ (A.toEuclideanLin e) (A.toEuclideanLin e) :=
        hparseval b (A.toEuclideanLin e)
      _ = ∑ v : V, (G.degree v : ℝ) ^ 2 := hsecond
  have hmoment : (∑ v : V, (G.degree v : ℝ) ^ 2) ≤
      (r - D) * (n * d) + r * D * n := by
    calc
      (∑ v : V, (G.degree v : ℝ) ^ 2) =
          ∑ j : V, (hA.eigenvalues j) ^ 2 * c j := hf2.symm
      _ ≤ ∑ j : V, ((r - D) * hA.eigenvalues j + r * D) * c j :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hpoly j) (sq_nonneg _))
      _ = (r - D) * (∑ j : V, hA.eigenvalues j * c j) +
          r * D * (∑ j : V, c j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (r - D) * (n * d) + r * D * n := by rw [hf, hc]
  let T : ℝ := ∑ v : V, ((G.degree v : ℝ) - d) ^ 2
  have hTformula : T = (∑ v : V, (G.degree v : ℝ) ^ 2) - n * d ^ 2 := by
    calc
      T = ∑ v : V, ((G.degree v : ℝ) ^ 2 -
          (2 * d) * (G.degree v : ℝ) + d ^ 2) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = (∑ v : V, (G.degree v : ℝ) ^ 2) -
          (2 * d) * (∑ v : V, (G.degree v : ℝ)) + n * d ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, n]
      _ = (∑ v : V, (G.degree v : ℝ) ^ 2) - n * d ^ 2 := by
        rw [hsum]
        ring
  have hTupper : T ≤ n * (r - d) * (d + D) := by
    rw [hTformula]
    nlinarith only [hmoment]
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hRange : (D - m) ^ 2 ≤ 2 * T := by
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    obtain ⟨w, hw⟩ := G.exists_minimal_degree_vertex
    have hv' : (G.degree v : ℝ) = D := by
      dsimp only [D]
      exact_mod_cast hv.symm
    have hw' : (G.degree w : ℝ) = m := by
      dsimp only [m]
      exact_mod_cast hw.symm
    by_cases hvw : v = w
    · have hDm : D = m := by rw [← hv', ← hw', hvw]
      rw [hDm, sub_self, zero_pow (by decide)]
      exact mul_nonneg (by norm_num) hTnonneg
    · have hpair : (D - d) ^ 2 + (m - d) ^ 2 ≤ T := by
        have hs : (∑ k ∈ ({v, w} : Finset V), ((G.degree k : ℝ) - d) ^ 2) ≤
            ∑ k : V, ((G.degree k : ℝ) - d) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => sq_nonneg _)
        simpa only [Finset.sum_pair hvw, hv', hw'] using hs
      nlinarith only [hpair, sq_nonneg (D + m - 2 * d)]
  have hRangeGap : (D - m) ^ 2 ≤ 4 * n * D * (r - d) := by
    calc
      (D - m) ^ 2 ≤ 2 * T := hRange
      _ ≤ 2 * (n * (r - d) * (d + D)) :=
        mul_le_mul_of_nonneg_left hTupper (by norm_num)
      _ = (2 * n * (r - d)) * (d + D) := by ring
      _ ≤ (2 * n * (r - d)) * (2 * D) :=
        mul_le_mul_of_nonneg_left
          (show d + D ≤ 2 * D by linarith only [hdD])
          (mul_nonneg (mul_nonneg (by norm_num) hn.le) (sub_nonneg.mpr hdr))
      _ = 4 * n * D * (r - d) := by ring
  have hscale : 0 ≤ 4 * n * D :=
    mul_nonneg (mul_nonneg (by norm_num) hn.le) hD.le
  calc
    a * (D - m) ^ 2 ≤ a * (4 * n * D * (r - d)) :=
      mul_le_mul_of_nonneg_left hRangeGap ha
    _ = (4 * n * D) * (a * (r - d)) := by ring
    _ ≤ (4 * n * D) * ((2 * D) * (q - 2 * r)) :=
      mul_le_mul_of_nonneg_left hbase hscale
    _ = (q - 2 * r) * (8 * n * D ^ 2) := by ring
    _ ≤ (q - 2 * r) * (8 * n * D ^ 2 + (D - m) ^ 2) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg (D - m))) hgap

theorem model_05bc265566a122307820 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)))) ≥ ((((G.minDegree : ℝ) * (let D : Matrix V V ℝ := Matrix.diagonal (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹); (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (Matrix.isHermitian_mul_mul_conjTranspose D (G.isHermitian_lapMatrix ℝ)).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2)) / ((((8 : ℝ) * (Fintype.card V : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) + (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2))) := by
  classical
  rcases h_guard with ⟨hconn, horder, hdegree⟩
  have htwo : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hle' : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [horder, hle']
  have hV : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  simp only [if_neg hV, if_pos hconn, dif_pos htwo]
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let D : Matrix V V ℝ := Matrix.diagonal
    (fun v => (Real.sqrt (G.degree v : ℝ))⁻¹)
  let B : Matrix V V ℝ := D * L * Matrix.conjTranspose D
  let hL : L.IsHermitian := G.isHermitian_lapMatrix ℝ
  let hB : B.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose D hL
  let idx : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let second : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let a : ℝ := hL.eigenvalues₀ second
  let g : ℝ := hB.eigenvalues₀ second
  let m : ℝ := G.minDegree
  let delta : ℝ := G.maxDegree
  let n : ℝ := Fintype.card V
  let gap : ℝ :=
    sSup (Set.range ((G.isHermitian_degMatrix ℝ).add
      (G.isHermitian_adjMatrix ℝ)).eigenvalues) -
    2 * sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  let K : ℝ := 8 * n * delta ^ 2 + (delta - m) ^ 2
  change (m * g) * (delta - m) ^ 2 / K ≤ gap
  have hindex (M : Matrix V V ℝ) (hM : M.IsHermitian)
      (j : Fin (Fintype.card V)) :
      hM.eigenvalues (idx j) = hM.eigenvalues₀ j := by
    simp only [Matrix.IsHermitian.eigenvalues, idx, Equiv.symm_apply_apply]
  have hnonneg (M : Matrix V V ℝ) (hM : M.IsHermitian)
      (hPSD : M.PosSemidef) (j : V) : 0 ≤ hM.eigenvalues j := by
    rw [hM.eigenvalues_eq]
    simpa only [star_trivial, RCLike.re_to_real] using
      hPSD.dotProduct_mulVec_nonneg (⇑(hM.eigenvectorBasis j))
  have ha : 0 ≤ a := by
    change 0 ≤ hL.eigenvalues₀ second
    rw [← hindex L hL second]
    exact hnonneg L hL (G.posSemidef_lapMatrix ℝ) (idx second)
  have hg : 0 ≤ g := by
    change 0 ≤ hB.eigenvalues₀ second
    rw [← hindex B hB second]
    exact hnonneg B hB
      ((G.posSemidef_lapMatrix ℝ).mul_mul_conjTranspose_same D) (idx second)
  have hcomp : m * g ≤ a := by
    by_cases hm : m = 0
    · simpa only [hm, zero_mul] using ha
    · have hmpos : 0 < m :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hm)
      have hdegmin (v : V) : m ≤ (G.degree v : ℝ) := by
        change (G.minDegree : ℝ) ≤ (G.degree v : ℝ)
        exact_mod_cast G.minDegree_le_degree v
      have heigen (M : Matrix V V ℝ) (hM : M.IsHermitian) (j : V) :
          M.toEuclideanLin (hM.eigenvectorBasis j) =
            hM.eigenvalues j • hM.eigenvectorBasis j := by
        apply WithLp.ofLp_injective 2
        simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp,
          WithLp.ofLp_smul] using hM.mulVec_eigenvectorBasis j
      have hquad (M : Matrix V V ℝ) (hM : M.IsHermitian)
          (z : EuclideanSpace ℝ V) :
          inner ℝ (M.toEuclideanLin z) z =
            ∑ j : V, hM.eigenvalues j *
              (inner ℝ z (hM.eigenvectorBasis j)) ^ 2 := by
        have hsym : M.toEuclideanLin.IsSymmetric :=
          Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
        rw [← hM.eigenvectorBasis.sum_inner_mul_inner (M.toEuclideanLin z) z]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsym z (hM.eigenvectorBasis j), heigen M hM j,
          inner_smul_right, real_inner_comm z (hM.eigenvectorBasis j)]
        ring
      have hparseval (b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V))
          (z : EuclideanSpace ℝ V) :
          (∑ j : V, (inner ℝ z (b j)) ^ 2) = inner ℝ z z :=
        (b.sum_sq_inner_left z).trans (real_inner_self_eq_norm_sq z).symm
      let w : V → ℝ := fun v => Real.sqrt (G.degree v : ℝ)
      let S : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
        (Matrix.diagonal w).toEuclideanLin
      have hw (v : V) : w v ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (hmpos.trans_le (hdegmin v)))
      have hS_apply (z : EuclideanSpace ℝ V) (v : V) :
          (S z) v = w v * z v := by
        change Matrix.mulVec (Matrix.diagonal w) (⇑z) v = w v * z v
        exact Matrix.mulVec_diagonal _ _ _
      have hDS (z : EuclideanSpace ℝ V) : D.toEuclideanLin (S z) = z := by
        apply WithLp.ofLp_injective 2
        funext v
        change Matrix.mulVec D (⇑(S z)) v = z v
        simp only [D, Matrix.mulVec_diagonal]
        change (w v)⁻¹ * (S z) v = z v
        rw [hS_apply, ← mul_assoc, inv_mul_cancel₀ (hw v), one_mul]
      have hDadj : Matrix.conjTranspose D = D := by
        simp only [D, Matrix.diagonal_conjTranspose, star_trivial]
      have hDsym : D.toEuclideanLin.IsSymmetric :=
        Matrix.isSymmetric_toEuclideanLin_iff.mpr
          (show D.IsHermitian from hDadj)
      have hEnergy (z : EuclideanSpace ℝ V) :
          inner ℝ (B.toEuclideanLin (S z)) (S z) =
            inner ℝ (L.toEuclideanLin z) z := by
        simp only [B, hDadj, Matrix.toLpLin_mul_same,
          LinearMap.comp_apply, hDS]
        rw [hDsym (L.toEuclideanLin z) (S z), hDS]
      have hnorm (z : EuclideanSpace ℝ V) :
          inner ℝ z z = ∑ v : V, (z v) ^ 2 := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
        apply Finset.sum_congr rfl
        intro v hv
        change z v * z v = (z v) ^ 2
        ring
      have hSnorm (z : EuclideanSpace ℝ V) :
          m * inner ℝ z z ≤ inner ℝ (S z) (S z) := by
        calc
          m * inner ℝ z z = ∑ v : V, m * (z v) ^ 2 := by
            rw [hnorm, Finset.mul_sum]
          _ ≤ ∑ v : V, (G.degree v : ℝ) * (z v) ^ 2 :=
            Finset.sum_le_sum (fun v _ =>
              mul_le_mul_of_nonneg_right (hdegmin v) (sq_nonneg _))
          _ = inner ℝ (S z) (S z) := by
            rw [hnorm]
            apply Finset.sum_congr rfl
            intro v hv
            rw [hS_apply, mul_pow]
            have hw2 : (w v) ^ 2 = (G.degree v : ℝ) :=
              Real.sq_sqrt (Nat.cast_nonneg _)
            rw [hw2]
      let p : EuclideanSpace ℝ V := hL.eigenvectorBasis (idx second)
      let t : EuclideanSpace ℝ V := hL.eigenvectorBasis (idx last)
      let k : EuclideanSpace ℝ V := hB.eigenvectorBasis (idx last)
      let ell : ℝ := hL.eigenvalues₀ last
      have hRay (z : EuclideanSpace ℝ V) (hz : inner ℝ z k = 0) :
          g * inner ℝ z z ≤ inner ℝ (B.toEuclideanLin z) z := by
        calc
          g * inner ℝ z z =
              ∑ j : V, g * (inner ℝ z (hB.eigenvectorBasis j)) ^ 2 := by
            rw [← hparseval hB.eigenvectorBasis z, Finset.mul_sum]
          _ ≤ ∑ j : V, hB.eigenvalues j *
              (inner ℝ z (hB.eigenvectorBasis j)) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hjlast : j = idx last
            · subst j
              change g * (inner ℝ z k) ^ 2 ≤
                hB.eigenvalues (idx last) * (inner ℝ z k) ^ 2
              simp [hz]
            · have hneq : idx.symm j ≠ last := by
                intro hh
                apply hjlast
                calc
                  j = idx (idx.symm j) := (idx.apply_symm_apply j).symm
                  _ = idx last := congrArg idx hh
              have hvalne : (idx.symm j).val ≠ Fintype.card V - 1 := by
                intro hh
                apply hneq
                apply Fin.ext
                exact hh
              have hle : idx.symm j ≤ second := by
                change (idx.symm j).val ≤ Fintype.card V - 2
                have hlt := (idx.symm j).isLt
                omega
              have he : g ≤ hB.eigenvalues j := by
                change hB.eigenvalues₀ second ≤ hB.eigenvalues₀ (idx.symm j)
                exact hB.eigenvalues₀_antitone hle
              exact mul_le_mul_of_nonneg_right he (sq_nonneg _)
          _ = inner ℝ (B.toEuclideanLin z) z := (hquad B hB z).symm
      have hpunit : inner ℝ p p = 1 :=
        hL.eigenvectorBasis.inner_eq_one (idx second)
      have htunit : inner ℝ t t = 1 :=
        hL.eigenvectorBasis.inner_eq_one (idx last)
      have hpt : inner ℝ p t = 0 := by
        apply hL.eigenvectorBasis.inner_eq_zero
        intro hh
        have hfin := idx.injective hh
        have hval := congrArg Fin.val hfin
        change Fintype.card V - 2 = Fintype.card V - 1 at hval
        omega
      have htp : inner ℝ t p = 0 := by
        calc
          inner ℝ t p = inner ℝ p t := real_inner_comm _ _
          _ = 0 := hpt
      have hLp : L.toEuclideanLin p = a • p := by
        have hh := heigen L hL (idx second)
        rw [hindex L hL second] at hh
        exact hh
      have hLt : L.toEuclideanLin t = ell • t := by
        have hh := heigen L hL (idx last)
        rw [hindex L hL last] at hh
        exact hh
      have hell : ell ≤ a := by
        change hL.eigenvalues₀ last ≤ hL.eigenvalues₀ second
        apply hL.eigenvalues₀_antitone
        change Fintype.card V - 2 ≤ Fintype.card V - 1
        omega
      have hnormspan (c d : ℝ) :
          inner ℝ (c • p + d • t) (c • p + d • t) = c ^ 2 + d ^ 2 := by
        simp only [inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hpunit, htunit, hpt, htp]
        ring
      have htrial (c d : ℝ) :
          inner ℝ (L.toEuclideanLin (c • p + d • t)) (c • p + d • t) ≤
            a * inner ℝ (c • p + d • t) (c • p + d • t) := by
        calc
          inner ℝ (L.toEuclideanLin (c • p + d • t)) (c • p + d • t) =
              a * c ^ 2 + ell * d ^ 2 := by
            simp only [map_add, map_smul, hLp, hLt, inner_add_left,
              inner_add_right, real_inner_smul_left, real_inner_smul_right,
              hpunit, htunit, hpt, htp]
            ring
          _ ≤ a * (c ^ 2 + d ^ 2) := by
            have hh := mul_nonneg (sub_nonneg.mpr hell) (sq_nonneg d)
            nlinarith only [hh]
          _ = a * inner ℝ (c • p + d • t) (c • p + d • t) := by
            rw [hnormspan]
      let c : ℝ := inner ℝ (S p) k
      let d : ℝ := inner ℝ (S t) k
      obtain ⟨z, hzpos, hzorth, hzenergy⟩ :
          ∃ z : EuclideanSpace ℝ V,
            0 < inner ℝ z z ∧ inner ℝ (S z) k = 0 ∧
              inner ℝ (L.toEuclideanLin z) z ≤ a * inner ℝ z z := by
        by_cases hc : c = 0
        · refine ⟨p, ?_, hc, ?_⟩
          · rw [hpunit]
            norm_num
          · simpa only [one_smul, zero_smul, add_zero] using htrial 1 0
        · refine ⟨d • p + (-c) • t, ?_, ?_, htrial d (-c)⟩
          · rw [hnormspan]
            exact add_pos_of_nonneg_of_pos (sq_nonneg d)
              (sq_pos_of_ne_zero (neg_ne_zero.mpr hc))
          · simp only [map_add, map_smul, inner_add_left, real_inner_smul_left]
            change d * c + (-c) * d = 0
            ring
      have hchain : (m * g) * inner ℝ z z ≤ a * inner ℝ z z := by
        calc
          (m * g) * inner ℝ z z = g * (m * inner ℝ z z) := by ring
          _ ≤ g * inner ℝ (S z) (S z) :=
            mul_le_mul_of_nonneg_left (hSnorm z) hg
          _ ≤ inner ℝ (B.toEuclideanLin (S z)) (S z) := hRay (S z) hzorth
          _ = inner ℝ (L.toEuclideanLin z) z := hEnergy z
          _ ≤ a * inner ℝ z z := hzenergy
      exact le_of_mul_le_mul_right hchain hzpos
  have hn : 0 < n := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero hV
  have hdelta : 0 < delta := by
    change (0 : ℝ) < (G.maxDegree : ℝ)
    linarith only [hdegree]
  have hK : 0 < K := by
    change 0 < 8 * n * delta ^ 2 + (delta - m) ^ 2
    have hmain : 0 < 8 * n * delta ^ 2 :=
      mul_pos (mul_pos (by norm_num) hn) (sq_pos_of_pos hdelta)
    exact hmain.trans_le (le_add_of_nonneg_right (sq_nonneg (delta - m)))
  have hbase := model_bde7d8e48dd145e3a003 G ⟨hconn, horder, hdegree⟩
  simp only [if_neg hV, if_pos hconn, dif_pos htwo] at hbase
  change a * (delta - m) ^ 2 ≤ gap * K at hbase
  apply (div_le_iff₀ hK).2
  exact (mul_le_mul_of_nonneg_right hcomp (sq_nonneg (delta - m))).trans hbase
