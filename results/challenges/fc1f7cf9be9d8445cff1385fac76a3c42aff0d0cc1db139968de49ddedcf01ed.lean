import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem model_0a01f6ea5c2542c96796 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  have hmax : G.maxDegree ≤ 2 := by
    have hh : (G.maxDegree : ℝ) < 3 := by
      linarith only [h_guard.1]
    have hn : G.maxDegree < 3 := by exact_mod_cast hh
    omega
  have hmin : 1 ≤ G.minDegree := by
    have hh : (0 : ℝ) < (G.minDegree : ℝ) := by
      linarith only [h_guard.2.1]
    have hn : 0 < G.minDegree := by exact_mod_cast hh
    omega
  have hdeg (v : V) : G.degree v = 1 ∨ G.degree v = 2 := by
    have hlo := hmin.trans (G.minDegree_le_degree v)
    have hhi := (G.degree_le_maxDegree v).trans hmax
    omega
  let K : Submodule (ZMod 2) (V → ZMod 2) :=
    LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
  letI : Fintype K := Fintype.ofFinite K
  let E : V → (K → ZMod 2) := fun v x => (x : V → ZMod 2) v
  let Q := {q : K → ZMod 2 // q ≠ 0 ∧ ∃ v : V, E v = q}
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → V := fun q => Classical.choose q.property.2
  have hrep (q : Q) : E (rep q) = q.val :=
    Classical.choose_spec q.property.2
  have hleaf (v : V) (hv : G.degree v = 1) :
      ∃ a : V, G.neighborFinset v = {a} ∧ E a = 0 := by
    have hc : (G.neighborFinset v).card = 1 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv
    rcases Finset.card_eq_one.mp hc with ⟨a, hs⟩
    refine ⟨a, hs, ?_⟩
    funext x
    change (x : V → ZMod 2) a = 0
    have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
      x.property
    simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      hs, Finset.sum_singleton, Pi.zero_apply] using congrFun hx v
  have hpairs (v : V) (hv : G.degree v = 2) :
      ∃ a b : V, a ≠ b ∧ G.neighborFinset v = {a, b} ∧ E a = E b := by
    have hc : (G.neighborFinset v).card = 2 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv
    rcases Finset.card_eq_two.mp hc with ⟨a, b, hab, hs⟩
    refine ⟨a, b, hab, hs, ?_⟩
    funext x
    change (x : V → ZMod 2) a = (x : V → ZMod 2) b
    have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
      x.property
    have hsum : (x : V → ZMod 2) a + (x : V → ZMod 2) b = 0 := by
      simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
        hs, Finset.sum_pair hab, Pi.zero_apply] using congrFun hx v
    simpa only [ZMod.neg_eq_self_mod_two] using
      (eq_neg_iff_add_eq_zero.mpr hsum)
  let f : K →ₗ[ZMod 2] (Q → ZMod 2) :=
    { toFun := fun x q => (x : V → ZMod 2) (rep q)
      map_add' := by
        intro x y
        funext q
        rfl
      map_smul' := by
        intro a x
        funext q
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext v
    by_cases hz : E v = 0
    · have hx0 : (x : V → ZMod 2) v = 0 := congrFun hz x
      have hy0 : (y : V → ZMod 2) v = 0 := congrFun hz y
      rw [hx0, hy0]
    · let q : Q := ⟨E v, hz, ⟨v, rfl⟩⟩
      calc
        (x : V → ZMod 2) v = (x : V → ZMod 2) (rep q) :=
          (congrFun (hrep q) x).symm
        _ = (y : V → ZMod 2) (rep q) := congrFun hxy q
        _ = (y : V → ZMod 2) v := congrFun (hrep q) y
  have hkdim : Module.finrank (ZMod 2) K ≤ Fintype.card Q := by
    calc
      _ ≤ Module.finrank (ZMod 2) (Q → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hf
      _ = Fintype.card Q := Module.finrank_fintype_fun_eq_card (ZMod 2)
  let fiber : Q → Finset V := fun q =>
    (Finset.univ : Finset V).filter (fun v => E v = q.val)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  have hbound (q : Q) : d ≤ (fiber q).card := by
    let c : V → ZMod 2 := fun v => if E v = q.val then 1 else 0
    have hc0 : c ≠ 0 := by
      intro hc
      have hh := congrFun hc (rep q)
      simpa [c, hrep q] using hh
    have hker : (G.adjMatrix (ZMod 2)).mulVecLin c = 0 := by
      funext v
      rcases hdeg v with hv | hv
      · rcases hleaf v hv with ⟨a, hs, ha⟩
        have hne : E a ≠ q.val := by
          intro hh
          exact q.property.1 (hh.symm.trans ha)
        have hca : c a = 0 := by simp [c, hne]
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_singleton, Pi.zero_apply] using hca
      · rcases hpairs v hv with ⟨a, b, hab, hs, he⟩
        have hcab : c a = c b := by
          dsimp only [c]
          rw [he]
        have hz : c b + c b = 0 := by
          simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (c b)
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, hcab, Pi.zero_apply] using hz
    have hcw : hammingNorm c ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨c, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc0, hker⟩
    have hd : d ≤ hammingNorm c := Finset.min'_le weights (hammingNorm c) hcw
    simpa [hammingNorm, c, fiber] using hd
  let s : Finset V := (Finset.univ : Finset V).filter (fun v => E v ≠ 0)
  let t : Finset V := sᶜ
  have hdisj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint fiber := by
    intro q _ z _ hqz
    apply Finset.disjoint_left.mpr
    intro v hvq hvz
    apply hqz
    apply Subtype.ext
    have heq : E v = q.val := (Finset.mem_filter.mp hvq).2
    have hez : E v = z.val := (Finset.mem_filter.mp hvz).2
    exact heq.symm.trans hez
  have hunion : (Finset.univ : Finset Q).biUnion fiber = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨q, _, hq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
      intro hz
      have heq : E v = q.val := (Finset.mem_filter.mp hq).2
      exact q.property.1 (heq.symm.trans hz)
    · intro hv
      have hz : E v ≠ 0 := (Finset.mem_filter.mp hv).2
      let q : Q := ⟨E v, hz, ⟨v, rfl⟩⟩
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩⟩
  have hsum : (∑ q : Q, (fiber q).card) = s.card := by
    rw [← Finset.card_biUnion hdisj, hunion]
  have hnat : Module.finrank (ZMod 2) K * d ≤ s.card := by
    calc
      _ ≤ Fintype.card Q * d := Nat.mul_le_mul_right d hkdim
      _ = ∑ _q : Q, d := by simp [Nat.nsmul_eq_mul]
      _ ≤ ∑ q : Q, (fiber q).card :=
        Finset.sum_le_sum (fun q _ => hbound q)
      _ = s.card := hsum
  have hlocal (v : V) (hv : v ∈ s) :
      2 ≤ G.degree v + (t.filter (fun w => G.Adj v w)).card := by
    rcases hdeg v with hv1 | hv2
    · rcases hleaf v hv1 with ⟨a, hs, ha⟩
      have hat : a ∈ t := by simp [t, s, ha]
      have hvan : a ∈ G.neighborFinset v := by rw [hs]; simp
      have hva : G.Adj v a := by
        simpa only [SimpleGraph.mem_neighborFinset] using hvan
      have hc : 0 < (t.filter (fun w => G.Adj v w)).card :=
        Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨hat, hva⟩⟩
      omega
    · omega
  have hcross :
      (∑ v ∈ s, (t.filter (fun w => G.Adj v w)).card) ≤
        ∑ w ∈ t, G.degree w := by
    calc
      _ = ∑ w ∈ t, (s.filter (fun v => G.Adj v w)).card := by
        simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := s) (t := t) G.Adj)
      _ ≤ ∑ w ∈ t, G.degree w := by
        apply Finset.sum_le_sum
        intro w hw
        calc
          (s.filter (fun v => G.Adj v w)).card ≤ (G.neighborFinset w).card := by
            apply Finset.card_le_card
            intro v hv
            have hvw : G.Adj v w := (Finset.mem_filter.mp hv).2
            simpa only [SimpleGraph.mem_neighborFinset] using hvw.symm
          _ = G.degree w := by simp only [SimpleGraph.card_neighborFinset_eq_degree]
  have hsplit :
      (∑ v ∈ s, G.degree v) + (∑ v ∈ t, G.degree v) =
        2 * G.edgeFinset.card := by
    calc
      _ = ∑ v : V, G.degree v := by
        simpa only [t] using Finset.sum_add_sum_compl s (fun v => G.degree v)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have htwice : 2 * s.card ≤ 2 * G.edgeFinset.card := by
    calc
      _ = ∑ _v ∈ s, 2 := by simp [Nat.nsmul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ v ∈ s, (G.degree v + (t.filter (fun w => G.Adj v w)).card) :=
        Finset.sum_le_sum (fun v hv => hlocal v hv)
      _ = (∑ v ∈ s, G.degree v) +
          (∑ v ∈ s, (t.filter (fun w => G.Adj v w)).card) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ v ∈ s, G.degree v) + (∑ v ∈ t, G.degree v) :=
        Nat.add_le_add_left hcross _
      _ = 2 * G.edgeFinset.card := hsplit
  have hsedges : s.card ≤ G.edgeFinset.card := by omega
  change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) ≤ (G.edgeFinset.card : ℝ)
  exact_mod_cast (hnat.trans hsedges)

theorem model_8ce30216566f34c2605a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ)) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    let t : Finset V := Finset.univ \ s
    have hcover : G.edgeFinset ⊆ t.biUnion (fun v => G.incidenceFinset v) := by
      intro e
      refine Sym2.inductionOn e ?_
      intro v w he
      have hadj : G.Adj v w := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      by_cases hv : v ∈ s
      · have hw : w ∉ s := by
          intro hw
          exact ((SimpleGraph.compl_adj G v w).mp (hs.isClique hv hw hadj.ne)).2 hadj
        refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
        · simp [t, hw]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_right_iff] using hadj
      · refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
        · simp [t, hv]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_left_iff] using hadj
    have hn : G.edgeFinset.card ≤ t.card * G.maxDegree := by
      calc
        G.edgeFinset.card ≤ (t.biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ t, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ t, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ t, G.maxDegree :=
          Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
        _ = t.card * G.maxDegree := by simp
    have hcard : t.card + Gᶜ.cliqueNum = Fintype.card V := by
      simpa only [t, hs.card_eq, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcard_real : (t.card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have ht : (t.card : ℝ) = (Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ) := by
      linarith
    have hbound : (G.edgeFinset.card : ℝ) ≤ (t.card : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hn
    rw [ht] at hbound
    exact hbound

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h

theorem hull3d_size_ge_1_0_max_degree_normalized_laplacian_spectral_gap_0_is_connected_9b83028c151a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ (G.maxDegree : ℝ) := by
  classical
  have hn : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le G.edgeFinset.card
      (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast hn

theorem model_255bb4d9cb35aa834f3d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.CliqueFree 3)) :
    (G.edgeFinset.card : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ))) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    have hi : G.IsIndepSet (s : Set V) := (G.isClique_compl).mp hs.isClique
    have hdeg : ∀ v : V, G.degree v ≤ Gᶜ.cliqueNum := by
      intro v
      have hn : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
        rw [G.isClique_compl, G.coe_neighborFinset]
        exact G.isIndepSet_neighborSet_of_triangleFree h_guard v
      exact hn.card_le_cliqueNum
    have hcover : G.edgeFinset ⊆ (sᶜ).biUnion (fun v => G.incidenceFinset v) := by
      intro e he
      have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨v, hv, hve⟩ :=
        SimpleGraph.IsIndepSet.nonempty_mem_compl_mem_edge G hi he'
      refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_compl.mpr hv, ?_⟩
      exact SimpleGraph.mem_incidenceFinset.mpr ⟨he', hve⟩
    have hnat : G.edgeFinset.card ≤ (sᶜ).card * Gᶜ.cliqueNum := by
      calc
        G.edgeFinset.card ≤ ((sᶜ).biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ sᶜ, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ sᶜ, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ sᶜ, Gᶜ.cliqueNum := Finset.sum_le_sum (fun v _ => hdeg v)
        _ = (sᶜ).card * Gᶜ.cliqueNum := by simp
    have hc : ((sᶜ).card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      have hn := Finset.card_compl_add_card s
      rw [hs.card_eq] at hn
      exact_mod_cast hn
    calc
      (G.edgeFinset.card : ℝ) ≤ ((sᶜ).card : ℝ) * (Gᶜ.cliqueNum : ℝ) := by
        exact_mod_cast hnat
      _ = (Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) := by
        rw [← hc]
        ring

theorem model_fadaed797ff612bf4d71 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.CliqueFree 3)) :
    (G.edgeFinset.card : ℝ) ≤ ((G.maxDegree : ℝ) * ((Fintype.card V : ℝ) - (G.maxDegree : ℝ))) := by
  classical
  have hmax : G.maxDegree ≤ Gᶜ.cliqueNum := by
    refine G.maxDegree_le_of_forall_degree_le _ ?_
    intro v
    have hn : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
      rw [G.isClique_compl, G.coe_neighborFinset]
      exact G.isIndepSet_neighborSet_of_triangleFree h_guard v
    exact hn.card_le_cliqueNum
  have hmax_real : (G.maxDegree : ℝ) ≤ (Gᶜ.cliqueNum : ℝ) := by
    exact_mod_cast hmax
  calc
    (G.edgeFinset.card : ℝ) ≤
        ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ) :=
      model_8ce30216566f34c2605a G
    _ ≤ ((Fintype.card V : ℝ) - (G.maxDegree : ℝ)) * (G.maxDegree : ℝ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hmax_real _) (Nat.cast_nonneg _)
    _ = (G.maxDegree : ℝ) * ((Fintype.card V : ℝ) - (G.maxDegree : ℝ)) :=
      mul_comm _ _
theorem model_10001ff1f3df81eb1d71 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (max ((G.minDegree : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ((2 : ℝ) * ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) - (1 : ℝ)))) ≤ (G.edgeFinset.card : ℝ) := by
  sorry
