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

theorem hull3d_max_degree_le_1_0_min_degree_girth_0_is_regular_a8cd4d70ab45 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ (G.minDegree : ℝ) := by
  classical
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨d, hd⟩ := h_guard
    rw [SimpleGraph.IsRegularOfDegree.maxDegree_eq (G := G) hd,
      SimpleGraph.IsRegularOfDegree.minDegree_eq (G := G) hd]

theorem hull_order_le_1_nordhaus_gaddum_spectral_sum_1_914963b7a9e6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Fintype.card V : ℝ) ≤ (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  classical
  by_cases hn : Fintype.card V = 0
  · simp [hn]
  · simp only [if_neg hn]
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let B : Matrix V V ℝ := Gᶜ.adjMatrix ℝ
    let hA : A.IsHermitian := G.isHermitian_adjMatrix ℝ
    let hB : B.IsHermitian := Gᶜ.isHermitian_adjMatrix ℝ
    let a : ℝ := sSup (Set.range hA.eigenvalues)
    let b : ℝ := sSup (Set.range hB.eigenvalues)
    change (Fintype.card V : ℝ) ≤ a + b + 1
    have hupper : ∀ (M : Matrix V V ℝ) (hM : M.IsHermitian),
        ((sSup (Set.range hM.eigenvalues)) • (1 : Matrix V V ℝ) - M).PosSemidef := by
      intro M hM
      let t : ℝ := sSup (Set.range hM.eigenvalues)
      change (t • (1 : Matrix V V ℝ) - M).PosSemidef
      have ht : ∀ i, hM.eigenvalues i ≤ t := by
        intro i
        exact le_csSup (Set.finite_range hM.eigenvalues).bddAbove (Set.mem_range_self i)
      have hd : (t • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)).PosSemidef := by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
        apply Matrix.PosSemidef.diagonal
        intro i
        simpa only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          mul_one, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
          using sub_nonneg.mpr (ht i)
      let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hM.eigenvectorUnitary
      have hC : C (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) = M :=
        hM.spectral_theorem.symm
      have heq : t • (1 : Matrix V V ℝ) - M =
          C (t • (1 : Matrix V V ℝ) -
            Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) := by
        rw [map_sub, map_smul, map_one, hC]
      rw [heq]
      change ((hM.eigenvectorUnitary : Matrix V V ℝ) *
        (t • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) *
        Matrix.conjTranspose (hM.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
      exact hd.mul_mul_conjTranspose_same _
    have hsum : (1 : Matrix V V ℝ) + A + B = Matrix.of 1 := by
      simpa only [A, B, G.compl_adjMatrix_eq_adjMatrix_compl ℝ] using
        G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    have htotal : ((a + b + 1) • (1 : Matrix V V ℝ) -
        Matrix.of 1).PosSemidef := by
      have heq : (a + b + 1) • (1 : Matrix V V ℝ) - Matrix.of 1 =
          (a • (1 : Matrix V V ℝ) - A) +
            (b • (1 : Matrix V V ℝ) - B) := by
        rw [← hsum, add_smul, add_smul, one_smul]
        abel
      rw [heq]
      exact (hupper A hA).add (hupper B hB)
    have hones : Matrix.mulVec (Matrix.of 1 : Matrix V V ℝ) (1 : V → ℝ) =
        (Fintype.card V : ℝ) • (1 : V → ℝ) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hnonneg : 0 ≤ (a + b + 1) * (Fintype.card V : ℝ) -
        (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := by
      simpa only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, hones, dotProduct_sub, dotProduct_smul,
        one_dotProduct_one, smul_eq_mul]
        using htotal.dotProduct_mulVec_nonneg (1 : V → ℝ)
    have hprod : 0 ≤ ((a + b + 1) - (Fintype.card V : ℝ)) *
        (Fintype.card V : ℝ) := by
      simpa only [sub_mul] using hnonneg
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hpos).mp hprod)
theorem model_058cec8793b79911021d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * ((((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues))) ^ 2) - (((Fintype.card V : ℝ) - (1 : ℝ)) ^ 2))) ≥ ((4 : ℝ) * (max (((G.maxDegree : ℝ) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) ^ 2) (((if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) - (G.minDegree : ℝ)) ^ 2))) := by
  sorry
