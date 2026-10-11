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

theorem degree_sum_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have hn : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _v : V, G.maxDegree := Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
      _ = Fintype.card V * G.maxDegree := by simp
  exact_mod_cast hn

theorem gutman_energy_size_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  let b := (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  let x : V → V → ℝ := fun i v => b i v
  have hsq (v : V) : (∑ i : V, x i v ^ 2) = 1 := by
    simpa only [x, EuclideanSpace.basisFun_inner,
      (EuclideanSpace.basisFun V ℝ).orthonormal.1 v, one_pow] using
      b.sum_sq_inner_left ((EuclideanSpace.basisFun V ℝ) v)
  have heig (i : V) :
      (G.isHermitian_adjMatrix ℝ).eigenvalues i =
        ∑ u : V, ∑ v : V, if G.Adj u v then x i u * x i v else 0 := by
    simpa only [RCLike.re_to_real, dotProduct, Pi.star_apply, star_trivial,
      Matrix.mulVec_apply_eq_sum, SimpleGraph.adjMatrix_apply, ite_mul,
      one_mul, zero_mul, Finset.mul_sum, mul_ite, mul_zero, x, b] using
      (G.isHermitian_adjMatrix ℝ).eigenvalues_eq i
  have hbound (i : V) :
      |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤
        ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
    rw [heig i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun u _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases huv : G.Adj u v
    · simp only [if_pos huv, abs_mul]
      have h := two_mul_le_add_sq |x i u| |x i v|
      simp only [sq_abs] at h
      linarith only [h]
    · simp [huv]
  calc
    (∑ i : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues i|) ≤
        ∑ i : V, ∑ u : V, ∑ v : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = ∑ u : V, ∑ v : V, ∑ i : V,
          if G.Adj u v then (x i u ^ 2 + x i v ^ 2) / 2 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      by_cases huv : G.Adj u v
      · simp only [if_pos huv]
        rw [← Finset.sum_div, Finset.sum_add_distrib, hsq u, hsq v]
        norm_num
      · simp only [if_neg huv, Finset.sum_const_zero]
    _ = ∑ u : V, (G.degree u : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact (G.degree_eq_sum_if_adj u).symm
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem composed_1f7e49d87d42f727 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  calc
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≤ (2 : ℝ) * (G.edgeFinset.card : ℝ) := gutman_energy_size_bound G
    _ ≤ (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := degree_sum_density_bound G

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem clique_edges_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hdv : ∀ v ∈ s, (G.cliqueNum : ℝ) - 1 ≤ (G.degree v : ℝ) := by
    intro v hv
    have hsubset : s.erase v ⊆ G.neighborFinset v := by
      intro w hw
      rw [G.mem_neighborFinset]
      exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
    have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
    have hn : G.cliqueNum ≤ G.degree v + 1 := by omega
    have hr : (G.cliqueNum : ℝ) ≤ (G.degree v : ℝ) + 1 := by exact_mod_cast hn
    linarith
  calc
    (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) = ∑ v ∈ s, ((G.cliqueNum : ℝ) - 1) := by
      simp [hs.card_eq]
      ring
    _ ≤ ∑ v ∈ s, (G.degree v : ℝ) := Finset.sum_le_sum hdv
    _ ≤ ∑ v : V, (G.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ s) (fun v _ _ => Nat.cast_nonneg _)
    _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem clique_le_max_degree_plus_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((G.maxDegree : ℝ) + (1 : ℝ)) := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  have hn : G.cliqueNum ≤ G.maxDegree + 1 := by
    by_cases he : s.Nonempty
    · obtain ⟨v, hv⟩ := he
      have hsubset : s.erase v ⊆ G.neighborFinset v := by
        intro w hw
        rw [G.mem_neighborFinset]
        exact hs.isClique hv (Finset.mem_erase.mp hw).2 (Finset.mem_erase.mp hw).1.symm
      have hcard := Finset.card_le_card hsubset
      rw [Finset.card_erase_of_mem hv, G.card_neighborFinset_eq_degree, hs.card_eq] at hcard
      have hmax := G.degree_le_maxDegree v
      have hpos : 0 < G.cliqueNum := hs.card_eq ▸ Finset.card_pos.mpr ⟨v,hv⟩
      omega
    · have : G.cliqueNum = 0 := by
        rw [← hs.card_eq]
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
      omega
  exact_mod_cast hn

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem composed_b214f1e86200a2e1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  have checked_0 := clique_le_max_degree_plus_one G; have checked_1 := composed_2cd2dd810fbb9720 G; have checked_2 := degree_sum_density_bound G; have checked_3 := archetype_chi_ge_omega G; have checked_4 := chromatic_le_order G; have checked_5 := clique_edges_density_bound G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

theorem model_e679ce9c7fa60e2c7bfd {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) * ((G.chromaticNumber.toNat : ℝ) - (1 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
    let n := G.chromaticNumber.toNat
    obtain ⟨c⟩ := G.colorable_chromaticNumber_of_fintype
    let H : SimpleGraph (Fin n) := G.map c
    have hn : (n : ℕ∞) ≤ H.chromaticNumber :=
      (ENat.natCast_toNat_le_self G.chromaticNumber).trans
        (SimpleGraph.chromaticNumber_mono_of_hom c.homMap)
    have hH : H = ⊤ := by
      apply SimpleGraph.eq_top_of_chromaticNumber_eq_card
      apply le_antisymm H.chromaticNumber_le_card
      simpa only [Fintype.card_fin] using hn
    have hsurj : Function.Surjective c.homMap.mapDart := by
      intro d
      obtain ⟨_, u, v, huv, hu, hv⟩ :=
        (SimpleGraph.map_adj' c G d.fst d.snd).mp d.adj
      refine ⟨⟨(u, v), huv⟩, ?_⟩
      apply SimpleGraph.Dart.ext
      exact Prod.ext hu hv
    have hcard : Fintype.card H.Dart ≤ Fintype.card G.Dart :=
      Fintype.card_le_of_surjective c.homMap.mapDart hsurj
    rw [H.dart_card_eq_twice_card_edges,
      G.dart_card_eq_twice_card_edges] at hcard
    have hreal : (2 : ℝ) * (H.edgeFinset.card : ℝ) ≤
        (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hcard
    have hclique : H.cliqueNum = n := by
      rw [hH, SimpleGraph.cliqueNum_top, Nat.card_fin]
    have hbound := clique_edges_density_bound H
    rw [hclique] at hbound
    exact hbound.trans hreal

theorem composed_ef727e745e60525c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((G.chromaticNumber.toNat : ℝ) * ((G.chromaticNumber.toNat : ℝ) - (1 : ℝ))) ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) := by
  exact (model_e679ce9c7fa60e2c7bfd G).trans (degree_sum_density_bound G)

theorem hull3d_max_degree_le_1__1_order_density_0_is_regular_f85632d19957 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≤ ((Fintype.card V : ℝ) - (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))) := by
  classical
  have hmax : G.maxDegree ≤ Fintype.card V - 1 := by
    apply G.maxDegree_le_of_forall_degree_le
    intro v
    have hv := G.degree_lt_card_verts v
    omega
  by_cases hsmall : Fintype.card V < 2
  · rw [if_pos hsmall, sub_zero]
    exact_mod_cast (hmax.trans (Nat.sub_le (Fintype.card V) 1))
  · rw [if_neg hsmall]
    have hn : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.not_lt.mp hsmall)
    have hmaxR : (G.maxDegree : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (show G.maxDegree + 1 ≤ Fintype.card V from by omega)
    have hsum : 2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
      calc
        2 * G.edgeFinset.card =
            Finset.sum Finset.univ (fun v : V => G.degree v) :=
          G.sum_degrees_eq_twice_card_edges.symm
        _ ≤ Finset.sum Finset.univ (fun _ : V => G.maxDegree) :=
          Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
        _ = Fintype.card V * G.maxDegree := by simp
    have hsumR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hsum
    have hden : 0 < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have hdensity : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      calc
        (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
            (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
        _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = 1 * ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring
    linarith

theorem model_5c1b1cd577e96807f60f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((Fintype.card V : ℝ) / ((2 : ℝ) * (G.maxDegree : ℝ)))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have heq : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  have heven :
      ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W]
        (B : Matrix W W (ZMod 2)),
        Fintype.card W = n → (∀ i j, B i j = B j i) →
        (∀ i, B i i = 0) → Even B.rank := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ B hc hs hd
      by_cases hz : B = 0
      · rw [hz, Matrix.rank_zero]
        exact ⟨0, rfl⟩
      · obtain ⟨a, b, hab0⟩ : ∃ a b : W, B a b ≠ 0 := by
          by_contra hnot
          apply hz
          ext i j
          by_contra hij
          exact hnot ⟨i, j, hij⟩
        have hab : B a b = 1 := hone _ hab0
        have hba : B b a = 1 := (hs b a).trans hab
        have hne : a ≠ b := by
          intro h
          apply hab0
          rw [h]
          exact hd b
        let s : Finset W := ({a, b} : Finset W)ᶜ
        let T := ↥s
        have hsa : a ∉ s := by simp [s]
        have hsb : b ∉ s := by simp [s]
        have hcT : Fintype.card T = s.card := Fintype.card_coe s
        have hcards : Fintype.card T + 2 = Fintype.card W := by
          rw [hcT]
          have hh := Finset.card_add_card_compl ({a, b} : Finset W)
          rw [Finset.card_pair hne] at hh
          change 2 + s.card = Fintype.card W at hh
          omega
        have hlt : Fintype.card T < n := by omega
        have hsum (f : W → ZMod 2) :
            (∑ i : W, f i) = f a + f b + ∑ i : T, f (i : W) := by
          calc
            _ = (∑ i ∈ ({a, b} : Finset W), f i) + ∑ i ∈ s, f i :=
              (Finset.sum_add_sum_compl ({a, b} : Finset W) f).symm
            _ = _ := by
              rw [Finset.sum_pair hne, ← Finset.sum_coe_sort s f]
        let E : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) :=
          { toFun := fun y i => if hi : i ∈ s then y ⟨i, hi⟩ else 0
            map_add' := by
              intro x y
              funext i
              by_cases hi : i ∈ s <;> simp [hi]
            map_smul' := by
              intro c x
              funext i
              by_cases hi : i ∈ s <;> simp [hi] }
        let Q : Matrix W T (ZMod 2) := fun i j => B i (j : W)
        let P : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) := Q.mulVecLin
        have hP (y : T → ZMod 2) (i : W) :
            P y i = ∑ j : T, B i (j : W) * y j := rfl
        let U : (T → ZMod 2) →ₗ[ZMod 2] (W → ZMod 2) :=
          E +
            (LinearMap.single (ZMod 2) (fun _ : W => ZMod 2) a).comp
              ((LinearMap.proj b).comp P) +
            (LinearMap.single (ZMod 2) (fun _ : W => ZMod 2) b).comp
              ((LinearMap.proj a).comp P)
        have hUa (y : T → ZMod 2) :
            U y a = ∑ j : T, B b (j : W) * y j := by
          change (E y a + (Pi.single a (P y b) : W → ZMod 2) a) +
            (Pi.single b (P y a) : W → ZMod 2) a = _
          simpa [E, hsa, hne, hne.symm, Pi.single_apply] using hP y b
        have hUb (y : T → ZMod 2) :
            U y b = ∑ j : T, B a (j : W) * y j := by
          change (E y b + (Pi.single a (P y b) : W → ZMod 2) b) +
            (Pi.single b (P y a) : W → ZMod 2) b = _
          simpa [E, hsb, hne, hne.symm, Pi.single_apply] using hP y a
        have hUt (y : T → ZMod 2) (i : T) : U y (i : W) = y i := by
          have hia : (i : W) ≠ a := by
            intro h
            exact hsa (h ▸ i.property)
          have hib : (i : W) ≠ b := by
            intro h
            exact hsb (h ▸ i.property)
          change (E y (i : W) + (Pi.single a (P y b) : W → ZMod 2) (i : W)) +
            (Pi.single b (P y a) : W → ZMod 2) (i : W) = y i
          simp [E, i.property, hia, hib, hia.symm, hib.symm, Pi.single_apply]
        let N : Matrix T T (ZMod 2) := fun i j =>
          B (i : W) (j : W) + B (i : W) a * B b (j : W) +
            B (i : W) b * B a (j : W)
        have hNs (i j : T) : N i j = N j i := by
          dsimp only [N]
          rw [hs (i : W) (j : W), hs b (j : W), hs a (j : W),
            hs (i : W) a, hs (i : W) b]
          ring
        have hNd (i : T) : N i i = 0 := by
          dsimp only [N]
          rw [hd (i : W), zero_add, hs b (i : W), hs a (i : W)]
          rw [mul_comm (B (i : W) b) (B (i : W) a)]
          exact htwo _
        have hUa0 (y : T → ZMod 2) : B.mulVecLin (U y) a = 0 := by
          change (∑ i : W, B a i * U y i) = 0
          rw [hsum]
          simp only [hd a, hab, zero_mul, one_mul, zero_add, hUb, hUt]
          exact htwo _
        have hUb0 (y : T → ZMod 2) : B.mulVecLin (U y) b = 0 := by
          change (∑ i : W, B b i * U y i) = 0
          rw [hsum]
          simp only [hba, hd b, one_mul, zero_mul, add_zero, hUa, hUt]
          exact htwo _
        have hUrow (y : T → ZMod 2) (i : T) :
            B.mulVecLin (U y) (i : W) = N.mulVecLin y i := by
          change (∑ j : W, B (i : W) j * U y j) = ∑ j : T, N i j * y j
          rw [hsum, hUa, hUb]
          simp only [hUt]
          dsimp only [N]
          simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
          ring
        have hUker (y : T → ZMod 2) (hy : N.mulVecLin y = 0) :
            B.mulVecLin (U y) = 0 := by
          funext i
          change B.mulVecLin (U y) i = 0
          by_cases hia : i = a
          · subst i
            exact hUa0 y
          by_cases hib : i = b
          · subst i
            exact hUb0 y
          have hi : i ∈ s := by simp [s, hia, hib]
          exact (hUrow y ⟨i, hi⟩).trans (congrFun hy ⟨i, hi⟩)
        have hrecon (x : W → ZMod 2) (hx : B.mulVecLin x = 0) :
            x = U (fun i : T => x (i : W)) := by
          have hxa : x a = ∑ i : T, B b (i : W) * x (i : W) := by
            apply heq
            have hh := congrFun hx b
            change (∑ i : W, B b i * x i) = 0 at hh
            rw [hsum] at hh
            simpa only [hba, hd b, one_mul, zero_mul, add_zero] using hh
          have hxb : x b = ∑ i : T, B a (i : W) * x (i : W) := by
            apply heq
            have hh := congrFun hx a
            change (∑ i : W, B a i * x i) = 0 at hh
            rw [hsum] at hh
            simpa only [hd a, hab, zero_mul, one_mul, zero_add] using hh
          funext i
          by_cases hia : i = a
          · subst i
            rw [hUa]
            exact hxa
          by_cases hib : i = b
          · subst i
            rw [hUb]
            exact hxb
          have hi : i ∈ s := by simp [s, hia, hib]
          exact (hUt (fun j : T => x (j : W)) ⟨i, hi⟩).symm
        let K := LinearMap.ker B.mulVecLin
        let K' := LinearMap.ker N.mulVecLin
        have hres (x : K) :
            N.mulVecLin (fun i : T => (x : W → ZMod 2) (i : W)) = 0 := by
          funext i
          have hx : B.mulVecLin (x : W → ZMod 2) = 0 :=
            LinearMap.mem_ker.mp x.property
          have hr := hUrow (fun j : T => (x : W → ZMod 2) (j : W)) i
          rw [← hrecon (x : W → ZMod 2) hx] at hr
          exact hr.symm.trans (congrFun hx (i : W))
        let R : K →ₗ[ZMod 2] K' :=
          { toFun := fun x => ⟨fun i : T => (x : W → ZMod 2) (i : W), hres x⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              rfl
            map_smul' := by
              intro c x
              apply Subtype.ext
              rfl }
        let e : K ≃ₗ[ZMod 2] K' :=
          { R with
            invFun := fun y =>
              ⟨U (y : T → ZMod 2),
                hUker (y : T → ZMod 2) (LinearMap.mem_ker.mp y.property)⟩
            left_inv := by
              intro x
              apply Subtype.ext
              change U (fun i : T => (x : W → ZMod 2) (i : W)) =
                (x : W → ZMod 2)
              exact (hrecon _ (LinearMap.mem_ker.mp x.property)).symm
            right_inv := by
              intro y
              apply Subtype.ext
              funext i
              change U (y : T → ZMod 2) (i : W) = (y : T → ZMod 2) i
              exact hUt (y : T → ZMod 2) i }
        have hk : Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) K' :=
          e.finrank_eq
        have hrB : B.rank + Module.finrank (ZMod 2) K = Fintype.card W := by
          simpa only [Matrix.rank, K, Module.finrank_fintype_fun_eq_card] using
            LinearMap.finrank_range_add_finrank_ker B.mulVecLin
        have hrN : N.rank + Module.finrank (ZMod 2) K' = Fintype.card T := by
          simpa only [Matrix.rank, K', Module.finrank_fintype_fun_eq_card] using
            LinearMap.finrank_range_add_finrank_ker N.mulVecLin
        have hstep : B.rank = N.rank + 2 := by omega
        obtain ⟨r, hr⟩ := ih (Fintype.card T) hlt T N rfl hNs hNd
        exact ⟨r + 1, by omega⟩
  let M := G.adjMatrix (ZMod 2)
  have hsym (v w : V) : M v w = M w v :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply w v
  have hdiag (v : V) : M v v = 0 :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).apply_diag v
  obtain ⟨q, hq⟩ := heven (Fintype.card V) V M rfl hsym hdiag
  have hr2 : M.rank = 2 * q := by omega
  have hdeg : 0 < G.minDegree := by
    by_contra h
    have hz : G.minDegree = 0 := Nat.eq_zero_of_not_pos h
    have hg := h_guard.1
    rw [hz] at hg
    norm_num at hg
  have hD : 0 < G.maxDegree := by
    by_contra h
    have hz : G.maxDegree = 0 := Nat.eq_zero_of_not_pos h
    have hg := h_guard.2.1
    rw [hz] at hg
    norm_num at hg
  obtain ⟨S, hSsub, hScard, hSspan, hSind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn (ZMod 2) (Set.range M.col)
  have hScard' : S.card = M.rank := by
    rw [M.rank_eq_finrank_span_cols]
    exact hScard
  let supp : (V → ZMod 2) → Finset V :=
    fun x => Finset.univ.filter (fun i => x i ≠ 0)
  have hsuppcol (v : V) : supp (M.col v) = G.neighborFinset v := by
    ext i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.mem_neighborFinset]
    change M i v ≠ 0 ↔ G.Adj v i
    rw [hsym i v]
    by_cases h : G.Adj v i <;> simp [M, SimpleGraph.adjMatrix_apply, h]
  have hsupp (x : V → ZMod 2) (hx : x ∈ S) :
      (supp x).card ≤ G.maxDegree := by
    obtain ⟨v, hv⟩ := hSsub hx
    rw [← hv, hsuppcol, G.card_neighborFinset_eq_degree]
    exact G.degree_le_maxDegree v
  have hcover : (Finset.univ : Finset V) ⊆ S.biUnion supp := by
    intro i hi
    by_contra hin
    have hz : ∀ x ∈ S, x i = 0 := by
      intro x hx
      by_contra hxi
      apply hin
      exact Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi⟩⟩
    let Z : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (LinearMap.proj i)
    have hSZ : Submodule.span (ZMod 2) (S : Set (V → ZMod 2)) ≤ Z := by
      apply Submodule.span_le.mpr
      intro x hx
      change x i = 0
      exact hz x hx
    have hcol (v : V) : M.col v ∈ Z := by
      apply hSZ
      rw [hSspan]
      exact Submodule.subset_span ⟨v, rfl⟩
    obtain ⟨v, hiv⟩ := (G.degree_pos_iff_exists_adj i).mp
      (lt_of_lt_of_le hdeg (G.minDegree_le_degree i))
    have hzero : M i v = 0 := by
      have hh := hcol v
      change M i v = 0 at hh
      exact hh
    have h_one : M i v = 1 := by
      simp [M, SimpleGraph.adjMatrix_apply, hiv]
    exact zero_ne_one (hzero.symm.trans h_one)
  have hcount : Fintype.card V ≤ M.rank * G.maxDegree := by
    calc
      _ = (Finset.univ : Finset V).card := by simp
      _ ≤ (S.biUnion supp).card := Finset.card_le_card hcover
      _ ≤ ∑ x ∈ S, (supp x).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S, G.maxDegree :=
        Finset.sum_le_sum (fun x hx => hsupp x hx)
      _ = S.card * G.maxDegree := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      _ = M.rank * G.maxDegree := by rw [hScard']
  have hcountR : (Fintype.card V : ℝ) ≤ (M.rank : ℝ) * (G.maxDegree : ℝ) := by
    exact_mod_cast hcount
  have hr2R : (M.rank : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hr2
  have hDR : (0 : ℝ) < (G.maxDegree : ℝ) := by exact_mod_cast hD
  have hfrac : (Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ)) ≤ (q : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (G.maxDegree : ℝ))).2
    calc
      _ ≤ (M.rank : ℝ) * (G.maxDegree : ℝ) := hcountR
      _ = (q : ℝ) * (2 * (G.maxDegree : ℝ)) := by rw [hr2R]; ring
  have hceil : Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) ≤
      (q : ℤ) := by
    apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using hfrac
  have hceilR :
      (Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) : ℝ) ≤
        (q : ℝ) := by exact_mod_cast hceil
  have hdim : M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hdimR : (M.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) =
        (Fintype.card V : ℝ) := by exact_mod_cast hdim
  change (Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) : ℝ) +
    2 * (Int.ceil ((Fintype.card V : ℝ) / (2 * (G.maxDegree : ℝ))) : ℝ) ≤
      (Fintype.card V : ℝ)
  linarith only [hdimR, hr2R, hceilR]

theorem model_01fb90bd2b4c0045f68b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.ceil ((Fintype.card V : ℝ) / ((2 : ℝ) * (G.maxDegree : ℝ)))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  apply model_5c1b1cd577e96807f60f G
  refine ⟨h_guard.1, ?_, h_guard.2.2⟩
  exact le_trans (by norm_num : (9999999 / 10000000 : ℝ) ≤ (19999999 / 10000000 : ℝ)) h_guard.2.1
theorem model_69d93273dcefb22a5491 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (((((Fintype.card V : ℝ) - (1 : ℝ)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues))) - ((Fintype.card V : ℝ) * (G.maxDegree : ℝ))) * (((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) - (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))) ≥ (((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) * (((Fintype.card V : ℝ) - (G.maxDegree : ℝ)) - (1 : ℝ))) := by
  classical
  have hn : 2 ≤ Fintype.card V := by
    by_contra h
    have hc : (Fintype.card V : ℝ) ≤ 1 := by
      exact_mod_cast (show Fintype.card V ≤ 1 from by omega)
    have hh := h_guard.2.2
    norm_num at hh
    linarith
  have hn0 : Fintype.card V ≠ 0 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d, hd⟩ := h_guard.2.1
  have hdmax : G.maxDegree = d := hd.maxDegree_eq
  let N : ℝ := (Fintype.card V : ℝ)
  let D : ℝ := (d : ℝ)
  let L : Matrix V V ℝ := G.lapMatrix ℝ
  let ev : V → ℝ := (G.isHermitian_lapMatrix ℝ).eigenvalues
  let lam : Fin (Fintype.card V) → ℝ := (G.isHermitian_lapMatrix ℝ).eigenvalues₀
  let e : Fin (Fintype.card V) ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
  have he (i : Fin (Fintype.card V)) : ev (e i) = lam i := by
    change (G.isHermitian_lapMatrix ℝ).eigenvalues₀ (e.symm (e i)) = _
    rw [Equiv.symm_apply_apply]
  have htransport (f : ℝ → ℝ) :
      (∑ i : Fin (Fintype.card V), f (lam i)) = ∑ v : V, f (ev v) :=
    Fintype.sum_equiv e _ _ (fun i => congrArg f ((he i).symm))
  have hsumV : (∑ v : V, ev v) = N * D := by
    calc
      _ = Matrix.trace L := (G.isHermitian_lapMatrix ℝ).trace_eq_sum_eigenvalues.symm
      _ = N * D := by
        simp [L, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hd.degree_eq, N, D]
  have hLreg : L = Matrix.diagonal (fun _ : V => D) - G.adjMatrix ℝ := by
    simp only [L, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hd.degree_eq, D]
  have hsqtrace : Matrix.trace (L * L) = N * D * (D + 1) := by
    have hzero (i : V) :
        (∑ u ∈ G.neighborFinset i,
          Matrix.diagonal (fun _ : V => (d : ℝ)) i u) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      have hiu : G.Adj i u := by
        simpa only [G.mem_neighborFinset] using hu
      exact Matrix.diagonal_apply_ne _ hiu.ne
    simp only [hLreg, sub_mul, mul_sub, Matrix.trace_sub]
    simp [Matrix.trace, G.adjMatrix_mul_self_apply_self, hd.degree_eq, N, D, hzero]
    ring
  let U := (G.isHermitian_lapMatrix ℝ).eigenvectorUnitary
  let C := Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) (star U)
  have hC : C L = Matrix.diagonal ev := by
    simpa only [C, U, L, ev, RCLike.ofReal_real_eq_id, Function.id_comp] using
      (G.isHermitian_lapMatrix ℝ).conjStarAlgAut_star_eigenvectorUnitary
  have htr (B : Matrix V V ℝ) : Matrix.trace (C B) = Matrix.trace B := by
    change Matrix.trace (Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) (star U) B) = _
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.trace_mul_cycle]
    have hU : (U : Matrix V V ℝ) * star (U : Matrix V V ℝ) = 1 :=
      Unitary.mul_star_self_of_mem U.property
    rw [hU, one_mul]
  have hsqspec : (∑ v : V, ev v ^ 2) = Matrix.trace (L * L) := by
    calc
      _ = Matrix.trace (Matrix.diagonal ev * Matrix.diagonal ev) := by
        simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_two]
      _ = Matrix.trace (C (L * L)) := by
        simp only [map_mul, hC]
      _ = Matrix.trace (L * L) := htr _
  have hnonneg (v : V) : 0 ≤ ev v := by
    dsimp only [ev]
    rw [(G.isHermitian_lapMatrix ℝ).eigenvalues_eq v]
    simpa only [RCLike.re_to_real] using
      (G.posSemidef_lapMatrix ℝ).dotProduct_mulVec_nonneg
        (⇑((G.isHermitian_lapMatrix ℝ).eigenvectorBasis v))
  have hzrange : (0 : ℝ) ∈ Set.range ev := by
    change (0 : ℝ) ∈ Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues
    rw [← (G.isHermitian_lapMatrix ℝ).spectrum_real_eq_range_eigenvalues]
    exact G.zero_mem_spectrum_lapMatrix ℝ
  obtain ⟨v, hv⟩ := hzrange
  let z : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
  let t : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
  let s : Finset (Fin (Fintype.card V)) := Finset.univ.erase z
  let A : ℝ := lam t
  let B : ℝ := sSup (Set.range ev)
  have hiz (i : Fin (Fintype.card V)) : i ≤ z := by
    change i.val ≤ Fintype.card V - 1
    have hi := i.isLt
    omega
  have hlast : lam z = 0 := by
    apply le_antisymm
    · calc
        lam z ≤ lam (e.symm v) :=
          (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone (hiz _)
        _ = ev v := by
          simpa only [Equiv.apply_symm_apply] using (he (e.symm v)).symm
        _ = 0 := hv
    · rw [← he z]
      exact hnonneg (e z)
  have hsCard : (s.card : ℝ) = N - 1 := by
    have hc : s.card = Fintype.card V - 1 := by
      dsimp only [s]
      rw [Finset.card_erase_of_mem (Finset.mem_univ z), Finset.card_univ,
        Fintype.card_fin]
    rw [hc, Nat.cast_sub (by omega : 1 ≤ Fintype.card V)]
    simp only [Nat.cast_one, N]
  have hsSum : (∑ i ∈ s, lam i) = N * D := by
    calc
      _ = ∑ i : Fin (Fintype.card V), lam i := Finset.sum_erase _ hlast
      _ = ∑ w : V, ev w := htransport (fun x => x)
      _ = N * D := hsumV
  have hsSq : (∑ i ∈ s, lam i ^ 2) = N * D * (D + 1) := by
    calc
      _ = ∑ i : Fin (Fintype.card V), lam i ^ 2 :=
        Finset.sum_erase _ (by rw [hlast]; norm_num)
      _ = ∑ w : V, ev w ^ 2 := htransport (fun x => x ^ 2)
      _ = Matrix.trace (L * L) := hsqspec
      _ = N * D * (D + 1) := hsqtrace
  have ha (i : Fin (Fintype.card V)) (hi : i ∈ s) : A ≤ lam i := by
    apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
    change i.val ≤ Fintype.card V - 2
    have hiNe : i ≠ z := (Finset.mem_erase.mp hi).1
    have hiValNe : i.val ≠ Fintype.card V - 1 := by
      intro hh
      apply hiNe
      apply Fin.ext
      exact hh
    have hiLt := i.isLt
    omega
  have hb (i : Fin (Fintype.card V)) : lam i ≤ B := by
    rw [← he i]
    exact le_csSup (Set.finite_range ev).bddAbove ⟨e i, rfl⟩
  have hbound : 0 ≤ ∑ i ∈ s, (B - lam i) * (lam i - A) :=
    Finset.sum_nonneg (fun i hi =>
      mul_nonneg (sub_nonneg.mpr (hb i)) (sub_nonneg.mpr (ha i hi)))
  have hexpand :
      (∑ i ∈ s, (B - lam i) * (lam i - A)) =
        (A + B) * (N * D) - N * D * (D + 1) - (N - 1) * A * B := by
    calc
      _ = ∑ i ∈ s, ((A + B) * lam i - lam i ^ 2 - A * B) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      _ = _ := by
        simp only [Finset.sum_sub_distrib]
        rw [← Finset.mul_sum, hsSum, hsSq]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hsCard]
        ring
  rw [hexpand] at hbound
  have hN1 : 0 ≤ N - 1 := by
    have hNr : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    dsimp only [N]
    linarith only [hNr]
  have hmain := mul_nonneg hN1 hbound
  simp only [if_neg hn0, if_pos h_guard.1, dif_pos hn, hdmax]
  change ((N - 1) * B - N * D) * (N * D - (N - 1) * A) ≥
    N * D * (N - D - 1)
  calc
    ((N - 1) * B - N * D) * (N * D - (N - 1) * A) =
        N * D * (N - D - 1) +
          (N - 1) * ((A + B) * (N * D) - N * D * (D + 1) - (N - 1) * A * B) := by
      ring
    _ ≥ N * D * (N - D - 1) := le_add_of_nonneg_right hmain
