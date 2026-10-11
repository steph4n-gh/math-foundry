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
  classical
    let n : ℝ := (Fintype.card V : ℝ)
    have hn2Nat : 2 ≤ Fintype.card V := by
      by_contra hn
      have hsmall : Fintype.card V ≤ 1 := by omega
      have hsmallR : (Fintype.card V : ℝ) ≤ 1 := by
        exact_mod_cast hsmall
      linarith only [h_guard, hsmallR]
    have hn2 : (2 : ℝ) ≤ n := by
      dsimp only [n]
      exact_mod_cast hn2Nat
    have hnpos : 0 < n := by linarith only [hn2]
    have hnne : n ≠ 0 := ne_of_gt hnpos
    have hnNat : 0 < Fintype.card V := by omega
    have hnzero : Fintype.card V ≠ 0 := ne_of_gt hnNat
    letI : Nonempty V := Fintype.card_pos_iff.mp hnNat
    let a : ℝ := 2 * (G.edgeFinset.card : ℝ) / n
    let c : ℝ := n - 1
    let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
    let s : ℝ := sSup (Set.range (Gᶜ.isHermitian_adjMatrix ℝ).eigenvalues)
    let S : ℝ := r + s
    have hupper (M : Matrix V V ℝ) (hM : M.IsHermitian) :
        ((sSup (Set.range hM.eigenvalues)) • (1 : Matrix V V ℝ) - M).PosSemidef := by
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
      let E := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hM.eigenvectorUnitary
      have hE : E (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) = M :=
        hM.spectral_theorem.symm
      have heq : t • (1 : Matrix V V ℝ) - M =
          E (t • (1 : Matrix V V ℝ) -
            Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) := by
        rw [map_sub, map_smul, map_one, hE]
      rw [heq]
      change ((hM.eigenvectorUnitary : Matrix V V ℝ) *
        (t • (1 : Matrix V V ℝ) -
          Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)) *
        Matrix.conjTranspose (hM.eigenvectorUnitary : Matrix V V ℝ)).PosSemidef
      exact hd.mul_mul_conjTranspose_same _
    have hcs (M : Matrix V V ℝ) (hM : M.PosSemidef) (x y : V → ℝ) :
        (dotProduct x (M.mulVec y)) ^ 2 ≤
          dotProduct x (M.mulVec x) * dotProduct y (M.mulVec y) := by
      have hcomm : dotProduct y (M.mulVec x) = dotProduct x (M.mulVec y) := by
        simpa only [star_trivial] using
          hM.isHermitian.star_dotProduct_mulVec_comm y x
      have hpoly (z : ℝ) :
          0 ≤ dotProduct x (M.mulVec x) * (z * z) +
            (2 * dotProduct x (M.mulVec y)) * z + dotProduct y (M.mulVec y) := by
        have ht : 0 ≤ dotProduct (z • x + y) (M.mulVec (z • x + y)) := by
          simpa only [star_trivial] using
            hM.dotProduct_mulVec_nonneg (z • x + y)
        calc
          0 ≤ dotProduct (z • x + y) (M.mulVec (z • x + y)) := ht
          _ = dotProduct x (M.mulVec x) * (z * z) +
              (2 * dotProduct x (M.mulVec y)) * z +
              dotProduct y (M.mulVec y) := by
            simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
              dotProduct_smul, add_dotProduct, smul_dotProduct, smul_eq_mul, hcomm]
            ring
      have hd := discrim_le_zero hpoly
      dsimp only [discrim] at hd
      nlinarith only [hd]
    have hpair (M N : Matrix V V ℝ) (hM : M.PosSemidef) (hN : N.PosSemidef)
        (x y : V → ℝ)
        (hxy : dotProduct x (N.mulVec y) = -dotProduct x (M.mulVec y)) :
        4 * (dotProduct x (M.mulVec y)) ^ 2 ≤
          (dotProduct x (M.mulVec x) + dotProduct x (N.mulVec x)) *
            (dotProduct y (M.mulVec y) + dotProduct y (N.mulVec y)) := by
      let p : ℝ := dotProduct x (M.mulVec x)
      let q : ℝ := dotProduct x (N.mulVec x)
      let U : ℝ := dotProduct y (M.mulVec y)
      let W : ℝ := dotProduct y (N.mulVec y)
      let t : ℝ := dotProduct x (M.mulVec y)
      have hp : 0 ≤ p := by
        simpa only [p, star_trivial] using hM.dotProduct_mulVec_nonneg x
      have hq : 0 ≤ q := by
        simpa only [q, star_trivial] using hN.dotProduct_mulVec_nonneg x
      have hU : 0 ≤ U := by
        simpa only [U, star_trivial] using hM.dotProduct_mulVec_nonneg y
      have hW : 0 ≤ W := by
        simpa only [W, star_trivial] using hN.dotProduct_mulVec_nonneg y
      have ht1 : t ^ 2 ≤ p * U := hcs M hM x y
      have ht2 : t ^ 2 ≤ q * W := by
        have hh := hcs N hN x y
        rw [hxy, neg_sq] at hh
        exact hh
      have hprod : (t ^ 2) ^ 2 ≤ (p * W) * (q * U) := by
        calc
          (t ^ 2) ^ 2 = t ^ 2 * t ^ 2 := pow_two _
          _ ≤ (p * U) * (q * W) :=
            mul_le_mul ht1 ht2 (sq_nonneg t) (mul_nonneg hp hU)
          _ = (p * W) * (q * U) := by ring
      have ht3 : 2 * (t ^ 2) ≤ p * W + q * U :=
        two_mul_le_add_of_sq_le_mul (mul_nonneg hp hW) (mul_nonneg hq hU) hprod
      change 4 * t ^ 2 ≤ (p + q) * (U + W)
      calc
        4 * t ^ 2 = t ^ 2 + t ^ 2 + 2 * t ^ 2 := by ring
        _ ≤ (p * U + q * W) + (p * W + q * U) :=
          add_le_add (add_le_add ht1 ht2) ht3
        _ = (p + q) * (U + W) := by ring
    let A : Matrix V V ℝ := G.adjMatrix ℝ
    let B : Matrix V V ℝ := Gᶜ.adjMatrix ℝ
    let C : Matrix V V ℝ := r • (1 : Matrix V V ℝ) - A
    let D : Matrix V V ℝ := s • (1 : Matrix V V ℝ) - B
    let J : Matrix V V ℝ := Matrix.of 1
    let u : V → ℝ := 1
    have hC : C.PosSemidef := hupper A (G.isHermitian_adjMatrix ℝ)
    have hD : D.PosSemidef := hupper B (Gᶜ.isHermitian_adjMatrix ℝ)
    have hAB : (1 : Matrix V V ℝ) + A + B = J := by
      simpa only [A, B, J, G.compl_adjMatrix_eq_adjMatrix_compl ℝ] using
        G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one ℝ
    have hCD : C + D = (S + 1) • (1 : Matrix V V ℝ) - J := by
      dsimp only [C, D, S]
      rw [← hAB, add_smul, add_smul, one_smul]
      abel
    have huu : dotProduct u u = n := by simp [u, n]
    have hJ (x : V → ℝ) : J.mulVec x = (dotProduct u x) • u := by
      ext v
      simp [J, u, Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hAu : A.mulVec u = fun v : V => (G.degree v : ℝ) := by
      ext v
      change (Matrix.mulVec (G.adjMatrix ℝ) (1 : V → ℝ)) v = (G.degree v : ℝ)
      simpa using
        (SimpleGraph.adjMatrix_mulVec_const_apply (G := G) (α := ℝ) (a := (1 : ℝ)) (v := v))
    have hdegSum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hna : n * a = 2 * (G.edgeFinset.card : ℝ) := by
      dsimp only [a]
      exact mul_div_cancel₀ _ hnne
    have hua : dotProduct u (A.mulVec u) = n * a := by
      calc
        dotProduct u (A.mulVec u) = ∑ v : V, (G.degree v : ℝ) := by
          rw [hAu]
          simp [u, dotProduct]
        _ = 2 * (G.edgeFinset.card : ℝ) := hdegSum
        _ = n * a := hna.symm
    have hSn : n ≤ S + 1 := by
      simpa only [n, S, r, s, if_neg hnzero] using
        hull_order_le_1_nordhaus_gaddum_spectral_sum_1_914963b7a9e6 G
    have hc0 : 0 ≤ c := by
      dsimp only [c]
      linarith only [hn2]
    have hc1 : 0 ≤ c - 1 := by
      dsimp only [c]
      linarith only [hn2]
    have hSc : 0 ≤ S - c := by
      dsimp only [c]
      linarith only [hSn]
    have hweaken : c * (S - c) * (S + 1) ≤ c * (S ^ 2 - c ^ 2) := by
      calc
        c * (S - c) * (S + 1) ≤
            c * (S - c) * (S + 1) + c * (S - c) * (c - 1) :=
          le_add_of_nonneg_right (mul_nonneg (mul_nonneg hc0 hSc) hc1)
        _ = c * (S ^ 2 - c ^ 2) := by ring
    have huCD : dotProduct u (C.mulVec u) + dotProduct u (D.mulVec u) =
        n * (S - c) := by
      calc
        dotProduct u (C.mulVec u) + dotProduct u (D.mulVec u) =
            dotProduct u ((C + D).mulVec u) := by
          rw [Matrix.add_mulVec, dotProduct_add]
        _ = n * (S - c) := by
          simp only [hCD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
            hJ, dotProduct_sub, dotProduct_smul, smul_eq_mul, huu]
          dsimp only [c]
          ring
    have hvertex (v : V) :
        4 * ((G.degree v : ℝ) - a) ^ 2 ≤ c * (S ^ 2 - c ^ 2) := by
      let e : V → ℝ := Pi.single v 1
      let x : V → ℝ := n • e - u
      have hue : dotProduct u e = 1 := by simp [e, u]
      have heu : dotProduct e u = 1 := by simp [e, u]
      have hee : dotProduct e e = 1 := by simp [e]
      have hux : dotProduct u x = 0 := by
        dsimp only [x]
        simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hue, huu] <;> ring
      have hxx : dotProduct x x = n * c := by
        dsimp only [x, c]
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, huu, hue, heu, hee] <;> ring
      have huAe : dotProduct u (A.mulVec e) = (G.degree v : ℝ) := by
        calc
          dotProduct u (A.mulVec e) = dotProduct e (A.mulVec u) := by
            simpa only [A, star_trivial] using
              (G.isHermitian_adjMatrix ℝ).star_dotProduct_mulVec_comm u e
          _ = (G.degree v : ℝ) := by
            rw [hAu]
            simp [e]
      have huAx : dotProduct u (A.mulVec x) = n * ((G.degree v : ℝ) - a) := by
        dsimp only [x]
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
          dotProduct_smul, smul_eq_mul, huAe, hua] <;> ring
      have hcrossC : dotProduct u (C.mulVec x) = -(n * ((G.degree v : ℝ) - a)) := by
        simp only [C, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          dotProduct_sub, dotProduct_smul, smul_eq_mul, hux, huAx, mul_zero, zero_sub]
      have hcrossSum : dotProduct u (C.mulVec x) + dotProduct u (D.mulVec x) = 0 := by
        calc
          dotProduct u (C.mulVec x) + dotProduct u (D.mulVec x) =
              dotProduct u ((C + D).mulVec x) := by
            rw [Matrix.add_mulVec, dotProduct_add]
          _ = 0 := by
            simp only [hCD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
              hJ, dotProduct_sub, dotProduct_smul, smul_eq_mul, hux,
              mul_zero, zero_mul, sub_self]
      have hcrossD : dotProduct u (D.mulVec x) = -dotProduct u (C.mulVec x) := by
        linarith only [hcrossSum]
      have hxCD : dotProduct x (C.mulVec x) + dotProduct x (D.mulVec x) =
          n * c * (S + 1) := by
        calc
          dotProduct x (C.mulVec x) + dotProduct x (D.mulVec x) =
              dotProduct x ((C + D).mulVec x) := by
            rw [Matrix.add_mulVec, dotProduct_add]
          _ = n * c * (S + 1) := by
            simp only [hCD, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
              hJ, dotProduct_sub, dotProduct_smul, smul_eq_mul, hux, hxx,
              zero_mul, sub_zero] <;> ring
      have hp := hpair C D hC hD u x hcrossD
      rw [hcrossC, huCD, hxCD] at hp
      have hscaled : n ^ 2 * (4 * ((G.degree v : ℝ) - a) ^ 2) ≤
          n ^ 2 * (c * (S - c) * (S + 1)) := by
        calc
          n ^ 2 * (4 * ((G.degree v : ℝ) - a) ^ 2) =
              4 * (-(n * ((G.degree v : ℝ) - a))) ^ 2 := by ring
          _ ≤ (n * (S - c)) * (n * c * (S + 1)) := hp
          _ = n ^ 2 * (c * (S - c) * (S + 1)) := by ring
      exact (le_of_mul_le_mul_left hscaled (sq_pos_of_ne_zero hnne)).trans hweaken
    obtain ⟨vmax, hvmax⟩ := G.exists_maximal_degree_vertex
    obtain ⟨vmin, hvmin⟩ := G.exists_minimal_degree_vertex
    have hmax : 4 * ((G.maxDegree : ℝ) - a) ^ 2 ≤ c * (S ^ 2 - c ^ 2) := by
      rw [hvmax]
      exact hvertex vmax
    have hmin : 4 * (a - (G.minDegree : ℝ)) ^ 2 ≤ c * (S ^ 2 - c ^ 2) := by
      calc
        4 * (a - (G.minDegree : ℝ)) ^ 2 =
            4 * ((G.minDegree : ℝ) - a) ^ 2 := by ring
        _ ≤ c * (S ^ 2 - c ^ 2) := by
          rw [hvmin]
          exact hvertex vmin
    simp only [if_neg hnzero]
    change c * (S ^ 2 - c ^ 2) ≥
      4 * max (((G.maxDegree : ℝ) - a) ^ 2) ((a - (G.minDegree : ℝ)) ^ 2)
    rcases le_total (((G.maxDegree : ℝ) - a) ^ 2)
        ((a - (G.minDegree : ℝ)) ^ 2) with h | h
    · rw [max_eq_right h]
      exact hmin
    · rw [max_eq_left h]
      exact hmax
