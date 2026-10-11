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

theorem hull3d_algebraic_connectivity_le_0_1_min_degree_laplacian_spectral_radius_0_2a2b3957145e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn0 : Fintype.card V = 0
  · have hn : ¬ 2 ≤ Fintype.card V := by omega
    simp [hn0, hn]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn0)
    rw [if_neg hn0]
    let H := G.isHermitian_lapMatrix ℝ
    have hbdd : BddAbove (Set.range H.eigenvalues) :=
      (Set.finite_range H.eigenvalues).bddAbove
    have hzero : (0 : ℝ) ∈ Set.range H.eigenvalues := by
      rw [← H.spectrum_real_eq_range_eigenvalues]
      exact G.zero_mem_spectrum_lapMatrix ℝ
    have hnonneg : (0 : ℝ) ≤ sSup (Set.range H.eigenvalues) :=
      le_csSup hbdd hzero
    by_cases hc : G.Connected
    · simp only [if_pos hc]
      by_cases hn : 2 ≤ Fintype.card V
      · simp only [dif_pos hn]
        let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
        let e : Fin (Fintype.card V) ≃ V :=
          Fintype.equivOfCardEq (Fintype.card_fin _)
        have he : H.eigenvalues (e j) = H.eigenvalues₀ j := by
          change H.eigenvalues₀ (e.symm (e j)) = H.eigenvalues₀ j
          rw [e.symm_apply_apply]
        change H.eigenvalues₀ j ≤ sSup (Set.range H.eigenvalues)
        rw [← he]
        exact le_csSup hbdd ⟨e j, rfl⟩
      · simp only [dif_neg hn]
        exact hnonneg
    · simp only [if_neg hc]
      exact hnonneg

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

theorem hull3d_max_degree_ge_0_1_diameter_min_degree_0_is_bipartite_4065a324009b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≥ (G.minDegree : ℝ) := by
  simp

theorem hull3d_max_degree_ge_1_0_min_degree_girth_0_is_regular_9277ab7750da {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≥ (G.minDegree : ℝ) := by
  simp

theorem hull3d_max_degree_le_1_0_min_degree_girth_0_is_regular_a8cd4d70ab45 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ (G.minDegree : ℝ) := by
  classical
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨d, hd⟩ := h_guard
    rw [SimpleGraph.IsRegularOfDegree.maxDegree_eq (G := G) hd,
      SimpleGraph.IsRegularOfDegree.minDegree_eq (G := G) hd]

theorem hull3d_order_ge_1_0_laplacian_spectral_radius_signless_laplacian_spectral_radius_0_is_connected_88f94a53c8e1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (Fintype.card V : ℝ) ≥ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · rw [if_neg hn]
    haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    let u : EuclideanSpace ℝ V := (G.isHermitian_lapMatrix ℝ).eigenvectorBasis i
    let x : V → ℝ := ⇑u
    have hu : ‖u‖ = 1 :=
      (G.isHermitian_lapMatrix ℝ).eigenvectorBasis.orthonormal.1 i
    have hnorm : (∑ v : V, (x v) ^ 2) = 1 := by
      have hh := EuclideanSpace.real_norm_sq_eq u
      rw [hu, one_pow] at hh
      exact hh.symm
    have heig : (G.isHermitian_lapMatrix ℝ).eigenvalues i =
        Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x := by
      simpa only [Matrix.toLinearMap₂'_apply', star_trivial, RCLike.re_to_real]
        using (G.isHermitian_lapMatrix ℝ).eigenvalues_eq i
    have hsumle :
        (∑ v : V, ∑ w : V, if G.Adj v w then (x v - x w) ^ 2 else 0) ≤
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      by_cases hadj : G.Adj v w
      · simp only [if_pos hadj, le_refl]
      · simpa only [if_neg hadj] using sq_nonneg (x v - x w)
    have hsum :
        (∑ v : V, ∑ w : V, (x v - x w) ^ 2) =
        2 * ((Fintype.card V : ℝ) * (∑ v : V, (x v) ^ 2) -
          (∑ v : V, x v) ^ 2) := by
      have hrow (v : V) :
          (∑ w : V, (x v - x w) ^ 2) =
          (Fintype.card V : ℝ) * (x v) ^ 2 -
            2 * x v * (∑ w : V, x w) + (∑ w : V, (x w) ^ 2) := by
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      simp_rw [hrow]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum, hnorm] at hsumle
    rw [heig, G.lapMatrix_toLinearMap₂' ℝ x]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [hsumle, sq_nonneg (∑ v : V, x v)]
theorem model_8381b1d261739251d279 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((2 : ℝ) * (((((Fintype.card V : ℝ) - (1 : ℝ)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues))) - ((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) * (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)))))) ≥ (((2 : ℝ) * (((Fintype.card V : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) * (((Fintype.card V : ℝ) - (1 : ℝ)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))))) + (((Fintype.card V : ℝ) - (1 : ℝ)) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hle : Fintype.card V ≤ 1 := by omega
    have hle' : (Fintype.card V : ℝ) ≤ 1 := by exact_mod_cast hle
    linarith only [hle', h_guard.2]
  have hn0 : Fintype.card V ≠ 0 := by omega
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let H := G.isHermitian_lapMatrix ℝ
  let e : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let f : Fin (Fintype.card V) → ℝ := H.eigenvalues₀
  let z : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let j : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let s : Finset (Fin (Fintype.card V)) := Finset.univ.erase z
  let N : ℝ := Fintype.card V
  let d : ℝ := 2 * (G.edgeFinset.card : ℝ) / N
  let a : ℝ := f j
  let b : ℝ := sSup (Set.range H.eigenvalues)
  let D : V → ℝ := fun v => (G.degree v : ℝ)
  let Q : ℝ := ∑ v : V, (D v) ^ 2
  have hNpos : 0 < N := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hN2 : (2 : ℝ) ≤ N := by
    change (2 : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast hn
  have he (i : Fin (Fintype.card V)) : H.eigenvalues (e i) = f i := by
    change H.eigenvalues₀ (e.symm (e i)) = H.eigenvalues₀ i
    rw [e.symm_apply_apply]
  have hfnonneg (i : Fin (Fintype.card V)) : 0 ≤ f i := by
    rw [← he i, H.eigenvalues_eq]
    simpa only [RCLike.re_to_real] using
      (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg
        (⇑(H.eigenvectorBasis (e i)))
  have hfz : f z = 0 := by
    have hzero : (0 : ℝ) ∈ Set.range H.eigenvalues := by
      rw [← H.spectrum_real_eq_range_eigenvalues]
      exact G.zero_mem_spectrum_lapMatrix ℝ
    obtain ⟨v, hv⟩ := hzero
    have hfv : f (e.symm v) = 0 := by
      rw [← he (e.symm v), e.apply_symm_apply]
      exact hv
    have hidx : e.symm v ≤ z := by
      change (e.symm v).val ≤ Fintype.card V - 1
      have hi := (e.symm v).isLt
      omega
    have hle : f z ≤ f (e.symm v) := H.eigenvalues₀_antitone hidx
    rw [hfv] at hle
    exact le_antisymm hle (hfnonneg z)
  have hbdd : BddAbove (Set.range H.eigenvalues) :=
    (Set.finite_range H.eigenvalues).bddAbove
  have hupper (i : Fin (Fintype.card V)) : f i ≤ b := by
    rw [← he i]
    exact le_csSup hbdd ⟨e i, rfl⟩
  have hlower (i : Fin (Fintype.card V)) (hi : i ∈ s) : a ≤ f i := by
    have hneq : i ≠ z := (Finset.mem_erase.mp hi).1
    have hneqval : i.val ≠ Fintype.card V - 1 := by
      intro h
      apply hneq
      apply Fin.ext
      exact h
    have hidx : i ≤ j := by
      change i.val ≤ Fintype.card V - 2
      have hi' := i.isLt
      omega
    exact H.eigenvalues₀_antitone hidx
  have hscard_nat : s.card = Fintype.card V - 1 := by
    dsimp only [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ z),
      Finset.card_univ, Fintype.card_fin]
  have hscard : (s.card : ℝ) = N - 1 := by
    simpa only [Nat.cast_sub (show 1 ≤ Fintype.card V by omega), Nat.cast_one]
      using congrArg (fun t : ℕ => (t : ℝ)) hscard_nat
  have hNd : N * d = 2 * (G.edgeFinset.card : ℝ) := by
    dsimp only [d]
    field_simp [ne_of_gt hNpos] <;> ring
  have hsumD : (∑ v : V, D v) = N * d := by
    rw [hNd]
    dsimp only [D]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have htrace : (G.lapMatrix ℝ).trace = ∑ v : V, D v := by
    simp [Matrix.trace, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, D]
  have hsumf : (∑ i : Fin (Fintype.card V), f i) = N * d := by
    calc
      (∑ i : Fin (Fintype.card V), f i) =
          ∑ i : Fin (Fintype.card V), H.eigenvalues (e i) :=
        Finset.sum_congr rfl (fun i _ => (he i).symm)
      _ = ∑ v : V, H.eigenvalues v := e.sum_comp H.eigenvalues
      _ = (G.lapMatrix ℝ).trace := by
        simpa using H.trace_eq_sum_eigenvalues.symm
      _ = N * d := htrace.trans hsumD
  have htrace2spec : (G.lapMatrix ℝ * G.lapMatrix ℝ).trace =
      ∑ v : V, (H.eigenvalues v) ^ 2 := by
    let A : Matrix V V ℝ := Matrix.diagonal H.eigenvalues
    let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) H.eigenvectorUnitary
    have hspec : G.lapMatrix ℝ = C A := by
      simpa only [RCLike.ofReal_real_eq_id, Function.id_comp]
        using H.spectral_theorem
    calc
      (G.lapMatrix ℝ * G.lapMatrix ℝ).trace = (C A * C A).trace :=
        congrArg (fun M : Matrix V V ℝ => (M * M).trace) hspec
      _ = (C (A * A)).trace := congrArg Matrix.trace (map_mul C A A).symm
      _ = (A * A).trace := by
        change ((H.eigenvectorUnitary : Matrix V V ℝ) * (A * A) *
          (star H.eigenvectorUnitary : Matrix V V ℝ)).trace = (A * A).trace
        rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
      _ = ∑ v : V, (H.eigenvalues v) ^ 2 := by simp [A, pow_two]
  have hrow (v : V) :
      (∑ w : V, G.lapMatrix ℝ v w * G.lapMatrix ℝ w v) = (D v) ^ 2 + D v := by
    calc
      (∑ w : V, G.lapMatrix ℝ v w * G.lapMatrix ℝ w v) =
          ∑ w : V, ((if w = v then (D v) ^ 2 else 0) +
            (if G.Adj v w then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases hvw : v = w
        · subst w
          simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, D, pow_two]
        · have hwv : w ≠ v := Ne.symm hvw
          by_cases hadj : G.Adj v w
          · have hwa : G.Adj w v := G.adj_symm hadj
            simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hvw, hwv, hadj, hwa]
          · have hwa : ¬ G.Adj w v := by
              intro h
              exact hadj (G.adj_symm h)
            simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hvw, hwv, hadj, hwa]
      _ = (D v) ^ 2 + D v := by
        rw [Finset.sum_add_distrib, ← G.degree_eq_sum_if_adj (R := ℝ) v]
        simp [D]
  have htrace2graph : (G.lapMatrix ℝ * G.lapMatrix ℝ).trace = Q + N * d := by
    change (∑ v : V, ∑ w : V,
      G.lapMatrix ℝ v w * G.lapMatrix ℝ w v) = Q + N * d
    simp_rw [hrow]
    simpa only [Finset.sum_add_distrib, hsumD, Q]
  have hsumf2 : (∑ i : Fin (Fintype.card V), (f i) ^ 2) = Q + N * d := by
    calc
      (∑ i : Fin (Fintype.card V), (f i) ^ 2) =
          ∑ i : Fin (Fintype.card V), (H.eigenvalues (e i)) ^ 2 :=
        Finset.sum_congr rfl
          (fun i _ => (congrArg (fun t : ℝ => t ^ 2) (he i)).symm)
      _ = ∑ v : V, (H.eigenvalues v) ^ 2 :=
        e.sum_comp (fun v => (H.eigenvalues v) ^ 2)
      _ = (G.lapMatrix ℝ * G.lapMatrix ℝ).trace := htrace2spec.symm
      _ = Q + N * d := htrace2graph
  have hs1 : (∑ i ∈ s, f i) = N * d := by
    calc
      (∑ i ∈ s, f i) = ∑ i : Fin (Fintype.card V), f i :=
        Finset.sum_erase _ hfz
      _ = N * d := hsumf
  have hs2 : (∑ i ∈ s, (f i) ^ 2) = Q + N * d := by
    calc
      (∑ i ∈ s, (f i) ^ 2) = ∑ i : Fin (Fintype.card V), (f i) ^ 2 :=
        Finset.sum_erase _ (by simp [hfz])
      _ = Q + N * d := hsumf2
  have hmoment : Q + N * d ≤ (a + b) * (N * d) - (N - 1) * a * b := by
    calc
      Q + N * d = ∑ i ∈ s, (f i) ^ 2 := hs2.symm
      _ ≤ ∑ i ∈ s, ((a + b) * f i - a * b) := by
        apply Finset.sum_le_sum
        intro i hi
        have hterm := mul_nonneg (sub_nonneg.mpr (hupper i))
          (sub_nonneg.mpr (hlower i hi))
        nlinarith only [hterm]
      _ = (a + b) * (N * d) - (N - 1) * a * b := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs1,
          Finset.sum_const, nsmul_eq_mul, hscard] <;> ring
  let T : ℝ := ∑ v : V, (D v - d) ^ 2
  have hT : T = Q - N * d ^ 2 := by
    dsimp only [T]
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hsumD,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change Q - 2 * (N * d) * d + N * d ^ 2 = Q - N * d ^ 2
    ring
  have hvariance : ((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2 ≤
      2 * (Q - N * d ^ 2) := by
    rw [← hT]
    have hT0 : 0 ≤ T := Finset.sum_nonneg (fun v _ => sq_nonneg (D v - d))
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    obtain ⟨w, hw⟩ := G.exists_minimal_degree_vertex
    have hv' : D v = (G.maxDegree : ℝ) := by
      dsimp only [D]
      exact_mod_cast hv.symm
    have hw' : D w = (G.minDegree : ℝ) := by
      dsimp only [D]
      exact_mod_cast hw.symm
    by_cases hvw : v = w
    · have hr : (G.maxDegree : ℝ) - (G.minDegree : ℝ) = 0 := by
        rw [← hv', ← hw', hvw, sub_self]
      rw [hr]
      nlinarith only [hT0]
    · have hpair : (D v - d) ^ 2 + (D w - d) ^ 2 ≤ T := by
        calc
          (D v - d) ^ 2 + (D w - d) ^ 2 =
              ∑ u ∈ ({v, w} : Finset V), (D u - d) ^ 2 := by simp [hvw]
          _ ≤ T := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun u _ _ => sq_nonneg (D u - d))
      rw [hv', hw'] at hpair
      nlinarith only [hpair,
        sq_nonneg ((G.maxDegree : ℝ) + (G.minDegree : ℝ) - 2 * d)]
  have hK : 0 ≤ N - 1 := by linarith only [hN2]
  have hM := mul_le_mul_of_nonneg_left hmoment hK
  have hV := mul_le_mul_of_nonneg_left hvariance hK
  simp only [if_neg hn0, if_pos h_guard.1, dif_pos hn]
  change 2 * (((N - 1) * b - N * d) * (N * d - (N - 1) * a)) ≥
    2 * (N * d * (N - 1 - d)) +
      (N - 1) * ((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2
  nlinarith only [hM, hV]
