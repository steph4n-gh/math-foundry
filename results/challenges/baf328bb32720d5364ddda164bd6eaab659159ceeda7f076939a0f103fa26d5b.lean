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

theorem hull3d_max_degree_le_0_1_diameter_nordhaus_gaddum_spectral_sum_0_is_connected_3b0accd8be72 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.maxDegree : ℝ) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  letI : Nonempty V := h_guard.nonempty
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast hn
  have hnzero : Fintype.card V ≠ 0 := ne_of_gt hn
  have hbound (H : SimpleGraph V) [DecidableRel H.Adj] :
      (∑ v : V, (H.degree v : ℝ)) ≤
        (Fintype.card V : ℝ) *
          sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues) := by
    let T : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
      Matrix.toEuclideanLin (H.adjMatrix ℝ)
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (H.isHermitian_adjMatrix ℝ).eigenvectorBasis
    let r : ℝ := sSup (Set.range (H.isHermitian_adjMatrix ℝ).eigenvalues)
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
    have hsym : T.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (H.isHermitian_adjMatrix ℝ)
    have heig (i : V) :
        T (b i) = (H.isHermitian_adjMatrix ℝ).eigenvalues i • b i := by
      apply (WithLp.ofLp_injective 2)
      change Matrix.mulVec (H.adjMatrix ℝ)
          ⇑((H.isHermitian_adjMatrix ℝ).eigenvectorBasis i) =
        (H.isHermitian_adjMatrix ℝ).eigenvalues i •
          ⇑((H.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
      exact (H.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
    have hlambda (i : V) : (H.isHermitian_adjMatrix ℝ).eigenvalues i ≤ r := by
      exact le_csSup
        (Set.finite_range (H.isHermitian_adjMatrix ℝ).eigenvalues).bddAbove
        ⟨i, rfl⟩
    have hexpand : inner ℝ x (T x) =
        ∑ i : V, (H.isHermitian_adjMatrix ℝ).eigenvalues i *
          (inner ℝ (b i) x) ^ 2 := by
      calc
        inner ℝ x (T x) =
            ∑ i : V, inner ℝ x (b i) * inner ℝ (b i) (T x) :=
          (b.sum_inner_mul_inner x (T x)).symm
        _ = ∑ i : V, (H.isHermitian_adjMatrix ℝ).eigenvalues i *
            (inner ℝ (b i) x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hsym (b i) x, heig i, real_inner_smul_left,
            real_inner_comm (b i) x]
          ring
    have hnorm : ‖x‖ ^ 2 = (Fintype.card V : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [x]
    have hquad : inner ℝ x (T x) = ∑ v : V, (H.degree v : ℝ) := by
      dsimp only [T, x]
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_toLp_toLp]
      simp [dotProduct]
    calc
      (∑ v : V, (H.degree v : ℝ)) = inner ℝ x (T x) := hquad.symm
      _ = ∑ i : V, (H.isHermitian_adjMatrix ℝ).eigenvalues i *
          (inner ℝ (b i) x) ^ 2 := hexpand
      _ ≤ ∑ i : V, r * (inner ℝ (b i) x) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hlambda i) (sq_nonneg _))
      _ = r * ‖x‖ ^ 2 := by
        rw [← Finset.mul_sum, b.sum_sq_inner_right x]
      _ = (Fintype.card V : ℝ) * r := by
        rw [hnorm]
        ring
  have hdeg (v : V) :
      (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) = (Fintype.card V : ℝ) - 1 := by
    have hdlt := G.degree_lt_card_verts v
    have hcomp := G.degree_compl v
    have hnat : G.degree v + Gᶜ.degree v + 1 = Fintype.card V := by
      omega
    have hreal : (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) + 1 =
        (Fintype.card V : ℝ) := by
      exact_mod_cast hnat
    linarith only [hreal]
  have hsum : (∑ v : V, (G.degree v : ℝ)) +
      (∑ v : V, (Gᶜ.degree v : ℝ)) =
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hdeg]
    simp [nsmul_eq_mul]
    ring
  have hsum_bound :
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) ≤
        (Fintype.card V : ℝ) *
          (sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) +
            sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)) := by
    calc
      _ = (∑ v : V, (G.degree v : ℝ)) +
          (∑ v : V, (Gᶜ.degree v : ℝ)) := hsum.symm
      _ ≤ (Fintype.card V : ℝ) *
            sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) +
          (Fintype.card V : ℝ) *
            sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) :=
        add_le_add (hbound G) (hbound Gᶜ)
      _ = _ := by ring
  have hspec : (Fintype.card V : ℝ) - 1 ≤
      sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) +
        sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues) :=
    le_of_mul_le_mul_left hsum_bound hnR
  have hmax : G.maxDegree + 1 ≤ Fintype.card V :=
    Nat.succ_le_of_lt G.maxDegree_lt_card_verts
  have hmaxR : (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hmax
  simp only [if_neg hnzero]
  linarith only [hmaxR, hspec]

theorem hull_density_le_1_max_degree_0_f5fbcb14104c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) ≤ (G.maxDegree : ℝ) := by
  classical
  by_cases hn : Fintype.card V < 2
  · rw [if_pos hn]
    exact Nat.cast_nonneg _
  · rw [if_neg hn]
    have hn2nat : 2 ≤ Fintype.card V := by omega
    have hn2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hn2nat
    have hsum : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
      calc
        2 * G.edgeFinset.card = Finset.univ.sum (fun v : V => G.degree v) :=
          G.sum_degrees_eq_twice_card_edges.symm
        _ ≤ Finset.univ.sum (fun _ : V => G.maxDegree) :=
          Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
        _ = Fintype.card V * G.maxDegree := by simp
    have hsumR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hsum
    have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hmpos : (0 : ℝ) < (Fintype.card V : ℝ) - 1 := by linarith
    have hmone : (1 : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by linarith
    apply (div_le_iff₀ (mul_pos hnpos hmpos)).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
          (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
      _ ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) *
          ((Fintype.card V : ℝ) - 1) :=
        le_mul_of_one_le_right (by positivity) hmone
      _ = (G.maxDegree : ℝ) *
          ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring

theorem hull_max_degree_le_0_375_estrada_index_0_1_67202976fe25 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℝ) ≤ (((3 / 8 : ℝ) * (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v))) + (1 / 10 : ℝ)) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      haveI : IsEmpty V := hV
      simp <;> norm_num
  | inr hV =>
      haveI : Nonempty V := hV
      let A : Matrix V V ℝ := G.adjMatrix ℝ
      let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
      let e : V → ℝ := hA.eigenvalues
      let d : ℝ := G.maxDegree
      change d ≤ (3 / 8 : ℝ) * (∑ i : V, Real.exp (e i)) + (1 / 10 : ℝ)
      have hd : 0 ≤ d := Nat.cast_nonneg _
      have hexp (x : ℝ) :
          HasSum (fun k : ℕ => x ^ k / (Nat.factorial k : ℝ)) (Real.exp x) := by
        have hlim : Filter.Tendsto (Complex.exp' (x : ℂ)) Filter.atTop
            (nhds (Complex.exp (x : ℂ))) := by
          rw [Complex.exp]
          apply Metric.tendsto_atTop.2
          intro ε hε
          obtain ⟨N, hN⟩ := CauSeq.equiv_lim (Complex.exp' (x : ℂ)) ε hε
          refine ⟨N, fun n hn => ?_⟩
          simpa only [dist_eq_norm, CauSeq.sub_apply, CauSeq.const_apply] using hN n hn
        have hc : HasSum
            (fun k : ℕ => (x : ℂ) ^ k / (Nat.factorial k : ℂ))
            (Complex.exp (x : ℂ)) := by
          have hs := (NormedSpace.expSeries_div_summable (x : ℂ)).hasSum
          have heq : (∑' k : ℕ, (x : ℂ) ^ k / (Nat.factorial k : ℂ)) =
              Complex.exp (x : ℂ) :=
            tendsto_nhds_unique hs.tendsto_sum_nat hlim
          exact heq ▸ hs
        simpa only [Complex.reCLM_apply, ← Complex.ofReal_pow,
          ← Complex.ofReal_natCast, ← Complex.ofReal_div,
          Complex.ofReal_re, Real.exp] using (Complex.reCLM.hasSum hc)
      have htrace (k : ℕ) : (A ^ k).trace = ∑ i : V, e i ^ k := by
        rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
          Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
        simp [Matrix.diagonal_pow, e, Function.comp_def]
      have hnonneg (k : ℕ) (i j : V) : 0 ≤ (A ^ k) i j := by
        change 0 ≤ (G.adjMatrix ℝ ^ k) i j
        rw [G.adjMatrix_pow_apply_eq_card_walk k i j]
        exact Nat.cast_nonneg _
      have hAnonneg (i j : V) : 0 ≤ A i j := by
        simpa only [pow_one] using hnonneg 1 i j
      have ht (k : ℕ) : 0 ≤ (A ^ k).trace := by
        change 0 ≤ ∑ i : V, (A ^ k) i i
        exact Finset.sum_nonneg (fun i _ => hnonneg k i i)
      have hseries : HasSum
          (fun k : ℕ => (A ^ k).trace / (Nat.factorial k : ℝ))
          (∑ i : V, Real.exp (e i)) := by
        have hs : HasSum
            (fun k : ℕ => ∑ i : V, e i ^ k / (Nat.factorial k : ℝ))
            (∑ i : V, Real.exp (e i)) := by
          apply hasSum_sum
          intro i hi
          exact hexp (e i)
        simpa only [← Finset.sum_div, ← htrace] using hs
      have hEE : (Fintype.card V : ℝ) + (A ^ 2).trace / 2 +
          (A ^ 4).trace / 24 + (A ^ 6).trace / 720 ≤
          ∑ i : V, Real.exp (e i) := by
        have hpartial := sum_le_hasSum ({0, 2, 4, 6} : Finset ℕ)
          (fun k _ => div_nonneg (ht k) (Nat.cast_nonneg _)) hseries
        norm_num [Finset.sum_insert] at hpartial
        simpa only [add_assoc] using hpartial
      obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
      let N : Finset V := G.neighborFinset v
      have hnot : v ∉ N := by simp [N]
      have hdeg : (A ^ 2) v v = d := by
        change (G.adjMatrix ℝ ^ 2) v v = (G.maxDegree : ℝ)
        rw [pow_two, G.adjMatrix_mul_self_apply_self, ← hv]
      have hcenter (k : ℕ) : d ^ k ≤ (A ^ (2 * k)) v v := by
        induction k with
        | zero => simp
        | succ k ih =>
            change d ^ (k + 1) ≤ (A ^ (2 * (k + 1))) v v
            have hk : 2 * (k + 1) = 2 * k + 2 := by omega
            have hpow : A ^ (2 * (k + 1)) = A ^ (2 * k) * A ^ 2 := by
              rw [hk, pow_add]
            rw [hpow, Matrix.mul_apply]
            calc
              d ^ (k + 1) = d ^ k * d := by rw [pow_succ]
              _ ≤ (A ^ (2 * k)) v v * (A ^ 2) v v := by
                rw [hdeg]
                exact mul_le_mul_of_nonneg_right ih hd
              _ ≤ ∑ u : V, (A ^ (2 * k)) v u * (A ^ 2) u v :=
                Finset.single_le_sum
                  (fun u _ => mul_nonneg (hnonneg (2 * k) v u) (hnonneg 2 u v))
                  (Finset.mem_univ v)
      have hmulnonneg (k : ℕ) (i j : V) : 0 ≤ (A * A ^ k) i j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg
          (fun u _ => mul_nonneg (hAnonneg i u) (hnonneg k u j))
      have hleaf (k : ℕ) (w : V) (hw : w ∈ N) :
          d ^ k ≤ (A ^ (2 * (k + 1))) w w := by
        have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
        have haw : A w v = 1 := by simp [A, hvw.symm]
        have hva : A v w = 1 := by simp [A, hvw]
        have hfactor : A ^ (2 * (k + 1)) = A * A ^ (2 * k) * A := by
          rw [show 2 * (k + 1) = (1 + 2 * k) + 1 by omega, pow_add, pow_add]
          simp only [pow_one]
        have hinner : (A ^ (2 * k)) v v ≤ (A * A ^ (2 * k)) w v := by
          calc
            (A ^ (2 * k)) v v = A w v * (A ^ (2 * k)) v v := by
              rw [haw, one_mul]
            _ ≤ (A * A ^ (2 * k)) w v := by
              rw [Matrix.mul_apply]
              exact Finset.single_le_sum
                (fun u _ => mul_nonneg (hAnonneg w u) (hnonneg (2 * k) u v))
                (Finset.mem_univ v)
        have houter : (A * A ^ (2 * k)) w v ≤ (A * A ^ (2 * k) * A) w w := by
          calc
            (A * A ^ (2 * k)) w v = (A * A ^ (2 * k)) w v * A v w := by
              rw [hva, mul_one]
            _ ≤ (A * A ^ (2 * k) * A) w w := by
              rw [Matrix.mul_apply]
              exact Finset.single_le_sum
                (fun u _ => mul_nonneg (hmulnonneg (2 * k) w u) (hAnonneg u w))
                (Finset.mem_univ v)
        rw [hfactor]
        exact (hcenter k).trans (hinner.trans houter)
      have hmoment (k : ℕ) : 2 * d ^ (k + 1) ≤ (A ^ (2 * (k + 1))).trace := by
        calc
          2 * d ^ (k + 1) = d ^ (k + 1) + ∑ w ∈ N, d ^ k := by
            simp only [N, Finset.sum_const, G.card_neighborFinset_eq_degree,
              nsmul_eq_mul, ← hv]
            change 2 * d ^ (k + 1) = d ^ (k + 1) + d * d ^ k
            ring
          _ ≤ (A ^ (2 * (k + 1))) v v +
              ∑ w ∈ N, (A ^ (2 * (k + 1))) w w :=
            add_le_add (hcenter (k + 1))
              (Finset.sum_le_sum (fun w hw => hleaf k w hw))
          _ = ∑ w ∈ insert v N, (A ^ (2 * (k + 1))) w w := by
            rw [Finset.sum_insert hnot]
          _ ≤ ∑ w : V, (A ^ (2 * (k + 1))) w w :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun w _ _ => hnonneg (2 * (k + 1)) w w)
          _ = (A ^ (2 * (k + 1))).trace := rfl
      have h2 : 2 * d ≤ (A ^ 2).trace := by simpa using hmoment 0
      have h4 : 2 * d ^ 2 ≤ (A ^ 4).trace := by simpa using hmoment 1
      have h6 : 2 * d ^ 3 ≤ (A ^ 6).trace := by simpa using hmoment 2
      have hlower : (Fintype.card V : ℝ) + d + d ^ 2 / 12 + d ^ 3 / 360 ≤
          ∑ i : V, Real.exp (e i) := by
        linarith only [hEE, h2, h4, h6]
      have hnat : G.maxDegree + 1 ≤ Fintype.card V :=
        Nat.succ_le_of_lt G.maxDegree_lt_card_verts
      have hn : d + 1 ≤ (Fintype.card V : ℝ) := by
        change (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ)
        exact_mod_cast hnat
      have hpoly : 0 ≤ (d - (7 / 2 : ℝ)) ^ 2 * (d + 37) :=
        mul_nonneg (sq_nonneg _) (by linarith only [hd])
      nlinarith only [hlower, hn, hd, hpoly]

theorem hull3d_max_degree_ge_1__1_order_complement_spectral_radius__1_c3ce2e082db9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℝ) ≥ (((Fintype.card V : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) - (1 : ℝ)) := by
  classical
  by_cases hzero : Fintype.card V = 0
  · rw [if_pos hzero, hzero]
    simpa using
      (le_trans (show (-1 : ℝ) ≤ 0 by norm_num)
        (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _))
  · rw [if_neg hzero]
    have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hzero)
    let hA : (Gᶜ.adjMatrix ℝ).IsHermitian := Gᶜ.isHermitian_adjMatrix ℝ
    let r : ℝ := sSup (Set.range hA.eigenvalues)
    let U : Matrix V V ℝ := hA.eigenvectorUnitary
    change ((Fintype.card V : ℝ) - r) - 1 ≤ (G.maxDegree : ℝ)
    have hD : (Matrix.diagonal (fun v : V => r - hA.eigenvalues v)).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro v
      exact sub_nonneg.mpr
        (le_csSup (Set.finite_range hA.eigenvalues).bddAbove ⟨v, rfl⟩)
    have hdiag : Matrix.diagonal (fun v : V => r - hA.eigenvalues v) =
        r • (1 : Matrix V V ℝ) - Matrix.diagonal hA.eigenvalues := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal, Matrix.one_apply, hij, smul_eq_mul]
    have hunit : U * Matrix.conjTranspose U = 1 := by
      simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have hspec : Gᶜ.adjMatrix ℝ =
        U * Matrix.diagonal hA.eigenvalues * Matrix.conjTranspose U := by
      simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hA.spectral_theorem
    have hP : (r • (1 : Matrix V V ℝ) - Gᶜ.adjMatrix ℝ).PosSemidef := by
      have hp := hD.mul_mul_conjTranspose_same U
      rw [hdiag, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hunit, ← hspec] at hp
      exact hp
    have hMx : Matrix.mulVec
        (r • (1 : Matrix V V ℝ) - Gᶜ.adjMatrix ℝ)
        (fun _ : V => (1 : ℝ)) =
          fun v => r - (Gᶜ.degree v : ℝ) := by
      ext v
      simp [Matrix.sub_mulVec, Matrix.smul_mulVec]
    have hupper : (∑ v : V, (Gᶜ.degree v : ℝ)) ≤
        (Fintype.card V : ℝ) * r := by
      apply sub_nonneg.mp
      have hq := hP.dotProduct_mulVec_nonneg (fun _ : V => (1 : ℝ))
      rw [hMx] at hq
      simpa [dotProduct, Finset.sum_sub_distrib, nsmul_eq_mul] using hq
    have hdegrees (v : V) :
        (Fintype.card V : ℝ) - 1 - (G.maxDegree : ℝ) ≤ (Gᶜ.degree v : ℝ) := by
      have hdeg : G.degree v + Gᶜ.degree v + 1 = Fintype.card V := by
        rw [G.degree_compl v]
        have hv := G.degree_lt_card_verts v
        omega
      have hdegR : (G.degree v : ℝ) + (Gᶜ.degree v : ℝ) + 1 =
          (Fintype.card V : ℝ) := by
        exact_mod_cast hdeg
      have hmaxR : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
        exact_mod_cast (G.degree_le_maxDegree v)
      linarith only [hdegR, hmaxR]
    have hlower : (Fintype.card V : ℝ) *
        ((Fintype.card V : ℝ) - 1 - (G.maxDegree : ℝ)) ≤
          ∑ v : V, (Gᶜ.degree v : ℝ) := by
      calc
        (Fintype.card V : ℝ) *
            ((Fintype.card V : ℝ) - 1 - (G.maxDegree : ℝ)) =
            ∑ _ : V, ((Fintype.card V : ℝ) - 1 - (G.maxDegree : ℝ)) := by
              simp [nsmul_eq_mul] <;> ring
        _ ≤ ∑ v : V, (Gᶜ.degree v : ℝ) :=
          Finset.sum_le_sum (fun v _ => hdegrees v)
    have hbound : (Fintype.card V : ℝ) - 1 - (G.maxDegree : ℝ) ≤ r :=
      le_of_mul_le_mul_left (hlower.trans hupper) hnpos
    linarith only [hbound]

theorem model_8b660ccec0c7e356f6cf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.maxDegree : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) + ((G.cliqueFinset 3).card : ℝ)) := by
  classical
  have hnat : G.maxDegree ≤ Gᶜ.cliqueNum + (G.cliqueFinset 3).card := by
    apply G.maxDegree_le_of_forall_degree_le
    intro v
    let A : Finset (Finset V) :=
      (G.neighborFinset v).powerset.filter (fun s => Gᶜ.IsClique (s : Set V))
    have hA : A.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [A]
    obtain ⟨s, hsA, hsmax⟩ :=
      Finset.exists_max_image A (fun s : Finset V => s.card) hA
    have hsN : s ⊆ G.neighborFinset v :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hsA).1
    have hsC : Gᶜ.IsClique (s : Set V) :=
      (Finset.mem_filter.mp hsA).2
    let t : Finset V := G.neighborFinset v \ s
    have ht : ∀ w : ↥t, ∃ u : V, u ∈ s ∧ G.Adj (w : V) u := by
      intro w
      have hwN : (w : V) ∈ G.neighborFinset v :=
        (Finset.mem_sdiff.mp w.property).1
      have hws : (w : V) ∉ s :=
        (Finset.mem_sdiff.mp w.property).2
      by_contra hw
      have hc : Gᶜ.IsClique ((insert (w : V) s : Finset V) : Set V) := by
        rw [Finset.coe_insert]
        apply hsC.insert
        intro u hu hne
        exact (SimpleGraph.compl_adj G _ _).mpr
          ⟨hne, fun hadj => hw ⟨u, hu, hadj⟩⟩
      have hin : insert (w : V) s ∈ A :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr
            (Finset.insert_subset_iff.mpr ⟨hwN, hsN⟩), hc⟩
      have hle := hsmax (insert (w : V) s) hin
      rw [Finset.card_insert_of_notMem hws] at hle
      omega
    choose f hfS hfAdj using ht
    let F : ↥t → ↥(G.cliqueFinset 3) := fun w =>
      ⟨{v, (w : V), f w},
        SimpleGraph.mem_cliqueFinset_iff.mpr
          (SimpleGraph.is3Clique_triple_iff.mpr
            ⟨(G.mem_neighborFinset v (w : V)).mp
                (Finset.mem_sdiff.mp w.property).1,
              (G.mem_neighborFinset v (f w)).mp (hsN (hfS w)),
              hfAdj w⟩)⟩
    have hFinj : Function.Injective F := by
      intro x y hxy
      apply Subtype.ext
      have hsets : ({v, (x : V), f x} : Finset V) = {v, (y : V), f y} :=
        congrArg Subtype.val hxy
      have hxmem : (x : V) ∈ ({v, (y : V), f y} : Finset V) := by
        rw [← hsets]
        simp
      have hxne : (x : V) ≠ v :=
        ((G.mem_neighborFinset v (x : V)).mp
          (Finset.mem_sdiff.mp x.property).1).ne'
      have hxnot : (x : V) ∉ s :=
        (Finset.mem_sdiff.mp x.property).2
      have hxf : (x : V) ≠ f y := by
        intro h
        apply hxnot
        rw [h]
        exact hfS y
      simpa [hxne, hxf] using hxmem
    have htcard : t.card ≤ (G.cliqueFinset 3).card :=
      Finset.card_le_card_of_injective hFinj
    have hscard : s.card ≤ Gᶜ.cliqueNum := hsC.card_le_cliqueNum
    have hsum : t.card + s.card = G.degree v := by
      simpa only [t, G.card_neighborFinset_eq_degree] using
        Finset.card_sdiff_add_card_eq_card hsN
    calc
      G.degree v = t.card + s.card := hsum.symm
      _ ≤ (G.cliqueFinset 3).card + Gᶜ.cliqueNum := Nat.add_le_add htcard hscard
      _ = Gᶜ.cliqueNum + (G.cliqueFinset 3).card := Nat.add_comm _ _
  exact_mod_cast hnat

theorem hull3d_max_degree_le_1_1_independence_number_clique_number__2_is_tree_9f6ecc4441d8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (G.maxDegree : ℝ) ≤ (((Gᶜ.cliqueNum : ℝ) + (G.cliqueNum : ℝ)) - (2 : ℝ)) := by
  classical
  letI : Nonempty V := h_guard.connected.nonempty
  by_cases hbot : G = ⊥
  · have hd : G.maxDegree = 0 :=
      (SimpleGraph.maxDegree_eq_zero_iff (G := G)).mpr hbot
    have hc : (1 : ℝ) ≤ (G.cliqueNum : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr G.cliqueNum_ne_zero_of_finite)
    have hi : (1 : ℝ) ≤ (Gᶜ.cliqueNum : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Gᶜ).cliqueNum_ne_zero_of_finite)
    have hdR : (G.maxDegree : ℝ) = 0 := by
      exact_mod_cast hd
    linarith only [hdR, hc, hi]
  · have hfree : G.CliqueFree 3 :=
      h_guard.isAcyclic.cliqueFree (by norm_num)
    have ht : (G.cliqueFinset 3).card = 0 := by
      simp only [hfree.cliqueFinset, Finset.card_empty]
    have hb : (G.maxDegree : ℝ) ≤ (Gᶜ.cliqueNum : ℝ) := by
      simpa only [ht, Nat.cast_zero, add_zero] using model_8b660ccec0c7e356f6cf G
    obtain ⟨u, v, huv⟩ :=
      (SimpleGraph.ne_bot_iff_exists_adj (G := G)).mp hbot
    have hp : G.IsClique (({u, v} : Finset V) : Set V) := by
      rw [Finset.coe_pair]
      exact SimpleGraph.isClique_pair.mpr (fun _ => huv)
    have hc : 2 ≤ G.cliqueNum := by
      simpa only [Finset.card_pair huv.ne] using hp.card_le_cliqueNum
    have hcR : (2 : ℝ) ≤ (G.cliqueNum : ℝ) := by
      exact_mod_cast hc
    linarith only [hb, hcR]
theorem hull3d_max_degree_le_1__1_nordhaus_gaddum_spectral_sum_spectral_radius_1_is_tree_1113fa47dd29 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (G.maxDegree : ℝ) ≤ ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) - (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  sorry
