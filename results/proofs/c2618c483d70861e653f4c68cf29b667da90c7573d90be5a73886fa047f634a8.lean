import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic





open scoped BigOperators
theorem model_6a9d528a62da01e31f36 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    ((6 : ℝ) * ((G.cliqueFinset 3).card : ℝ)) ≥ ((((G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - (1 : ℝ))) * ((G.cliqueNum : ℝ) - (2 : ℝ))) + ((((3 : ℝ) * ((Fintype.card V : ℝ) - (G.cliqueNum : ℝ))) * (max (0 : ℝ) ((((G.minDegree : ℝ) + (G.cliqueNum : ℝ)) + (1 : ℝ)) - (Fintype.card V : ℝ)))) * ((max (0 : ℝ) ((((G.minDegree : ℝ) + (G.cliqueNum : ℝ)) + (1 : ℝ)) - (Fintype.card V : ℝ))) - (1 : ℝ)))) := by
  classical
    obtain ⟨c, hc⟩ := G.exists_isNClique_cliqueNum
    let N : V → Finset V := fun v => G.neighborFinset v ∩ c
    let T : V → Finset (Finset V) := fun v =>
      ((N v).powersetCard 2).image (fun p => insert v p)
    have hNc (v : V) : N v ⊆ c := by
      intro w hw
      change w ∈ G.neighborFinset v ∩ c at hw
      exact (Finset.mem_inter.mp hw).2
    have hNv (v : V) : v ∉ N v := by
      intro hv
      change v ∈ G.neighborFinset v ∩ c at hv
      exact G.notMem_neighborFinset_self v (Finset.mem_inter.mp hv).1
    have hcomp : G.cliqueNum + (cᶜ).card = Fintype.card V := by
      simpa only [hc.card_eq] using Finset.card_add_card_compl c
    let r : ℕ := G.minDegree + G.cliqueNum + 1 - Fintype.card V
    have hNbound (v : V) (hv : v ∈ cᶜ) : r ≤ (N v).card := by
      have hdiff : G.neighborFinset v \ c ⊆ (cᶜ).erase v := by
        intro w hw
        obtain ⟨hwN, hwnc⟩ := Finset.mem_sdiff.mp hw
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_compl.mpr hwnc⟩
        intro hwv
        subst w
        exact G.notMem_neighborFinset_self v hwN
      have hdiffcard := Finset.card_le_card hdiff
      rw [Finset.card_erase_of_mem hv] at hdiffcard
      have hpart : (N v).card + (G.neighborFinset v \ c).card = G.degree v := by
        simpa only [N, G.card_neighborFinset_eq_degree] using
          Finset.card_inter_add_card_sdiff (G.neighborFinset v) c
      have hmin := G.minDegree_le_degree v
      have hpos : 0 < (cᶜ).card := Finset.card_pos.mpr ⟨v, hv⟩
      dsimp only [r]
      omega
    have hTshape (v : V) (t : Finset V) (ht : t ∈ T v) :
        v ∈ t ∧ ∀ w ∈ t, w = v ∨ w ∈ c := by
      change t ∈ ((N v).powersetCard 2).image (fun p => insert v p) at ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      have hpN := (Finset.mem_powersetCard.mp hp).1
      refine ⟨Finset.mem_insert_self _ _, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with h | h
      · exact Or.inl h
      · exact Or.inr (hNc v (hpN h))
    have hTsub (v : V) : T v ⊆ G.cliqueFinset 3 := by
      intro t ht
      change t ∈ ((N v).powersetCard 2).image (fun p => insert v p) at ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hpN, hpcard⟩ := Finset.mem_powersetCard.mp hp
      have hvp : v ∉ p := fun h => hNv v (hpN h)
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        change a ∈ insert v p at ha
        change b ∈ insert v p at hb
        rcases Finset.mem_insert.mp ha with hav | ha
        · rcases Finset.mem_insert.mp hb with hbv | hb
          · exact (hab (hav.trans hbv.symm)).elim
          · rw [hav]
            exact (G.mem_neighborFinset v b).mp
              (Finset.mem_inter.mp (hpN hb)).1
        · rcases Finset.mem_insert.mp hb with hbv | hb
          · rw [hbv]
            exact G.adj_symm ((G.mem_neighborFinset v a).mp
              (Finset.mem_inter.mp (hpN ha)).1)
          · exact hc.isClique (hNc v (hpN ha)) (hNc v (hpN hb)) hab
      · simp only [Finset.card_insert_of_notMem hvp, hpcard]
    have hTcard (v : V) : (T v).card = (N v).card.choose 2 := by
      calc
        (T v).card = ((N v).powersetCard 2).card := by
          change (((N v).powersetCard 2).image (fun p => insert v p)).card = _
          apply Finset.card_image_of_injOn
          intro p hp q hq hpq
          have hvp : v ∉ p := fun h =>
            hNv v ((Finset.mem_powersetCard.mp hp).1 h)
          have hvq : v ∉ q := fun h =>
            hNv v ((Finset.mem_powersetCard.mp hq).1 h)
          have he := congrArg (fun s : Finset V => s.erase v) hpq
          simpa only [Finset.erase_insert hvp, Finset.erase_insert hvq] using he
        _ = (N v).card.choose 2 := Finset.card_powersetCard 2 (N v)
    have hdisj : ((cᶜ : Finset V) : Set V).PairwiseDisjoint T := by
      intro v hv w hw hvw
      apply Finset.disjoint_left.mpr
      intro t htv htw
      have hvnc : v ∉ c := Finset.mem_compl.mp hv
      rcases (hTshape w t htw).2 v (hTshape v t htv).1 with h | h
      · exact hvw h
      · exact hvnc h
    have hBdisj : Disjoint (c.powersetCard 3) ((cᶜ).biUnion T) := by
      apply Finset.disjoint_left.mpr
      intro t htB htU
      obtain ⟨v, hv, htv⟩ := Finset.mem_biUnion.mp htU
      exact (Finset.mem_compl.mp hv)
        ((Finset.mem_powersetCard.mp htB).1 (hTshape v t htv).1)
    have hBsub : c.powersetCard 3 ⊆ G.cliqueFinset 3 := by
      intro t ht
      obtain ⟨htc, htcard⟩ := Finset.mem_powersetCard.mp ht
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      refine ⟨?_, htcard⟩
      intro a ha b hb hab
      exact hc.isClique (htc ha) (htc hb) hab
    have hUsub : c.powersetCard 3 ∪ (cᶜ).biUnion T ⊆ G.cliqueFinset 3 := by
      intro t ht
      rcases Finset.mem_union.mp ht with htB | htU
      · exact hBsub htB
      · obtain ⟨v, hv, htv⟩ := Finset.mem_biUnion.mp htU
        exact hTsub v htv
    have hsum : (cᶜ).card * r.choose 2 ≤ ∑ v ∈ cᶜ, (T v).card := by
      calc
        _ = ∑ _v ∈ cᶜ, r.choose 2 := by simp
        _ ≤ _ := Finset.sum_le_sum fun v hv => by
          rw [hTcard v]
          exact Nat.choose_le_choose 2 (hNbound v hv)
    have hcount : c.card.choose 3 + (cᶜ).card * r.choose 2 ≤
        (G.cliqueFinset 3).card := by
      calc
        _ ≤ c.card.choose 3 + ∑ v ∈ cᶜ, (T v).card :=
          Nat.add_le_add_left hsum _
        _ = (c.powersetCard 3 ∪ (cᶜ).biUnion T).card := by
          rw [Finset.card_union_of_disjoint hBdisj,
            Finset.card_biUnion hdisj, Finset.card_powersetCard]
        _ ≤ (G.cliqueFinset 3).card := Finset.card_le_card hUsub
    rw [hc.card_eq] at hcount
    have hcountR : (G.cliqueNum.choose 3 : ℝ) +
        ((cᶜ).card : ℝ) * (r.choose 2 : ℝ) ≤ ((G.cliqueFinset 3).card : ℝ) := by
      exact_mod_cast hcount
    have hOreal : ((cᶜ).card : ℝ) = (Fintype.card V : ℝ) - (G.cliqueNum : ℝ) := by
      have hcompR : (G.cliqueNum : ℝ) + ((cᶜ).card : ℝ) =
          (Fintype.card V : ℝ) := by exact_mod_cast hcomp
      linarith only [hcompR]
    have hrreal : (r : ℝ) = max (0 : ℝ)
        (((G.minDegree : ℝ) + (G.cliqueNum : ℝ) + 1) - (Fintype.card V : ℝ)) := by
      by_cases h : Fintype.card V ≤ G.minDegree + G.cliqueNum + 1
      · have hs : (Fintype.card V : ℝ) ≤
            (G.minDegree : ℝ) + (G.cliqueNum : ℝ) + 1 := by exact_mod_cast h
        have hnonneg : (0 : ℝ) ≤
            ((G.minDegree : ℝ) + (G.cliqueNum : ℝ) + 1) - (Fintype.card V : ℝ) := by
          linarith only [hs]
        rw [max_eq_right hnonneg]
        dsimp only [r]
        rw [Nat.cast_sub h]
        simp only [Nat.cast_add, Nat.cast_one]
      · have hn : G.minDegree + G.cliqueNum + 1 ≤ Fintype.card V := by omega
        have hs : (G.minDegree : ℝ) + (G.cliqueNum : ℝ) + 1 ≤
            (Fintype.card V : ℝ) := by exact_mod_cast hn
        have hnonpos :
            ((G.minDegree : ℝ) + (G.cliqueNum : ℝ) + 1) - (Fintype.card V : ℝ) ≤ 0 := by
          linarith only [hs]
        rw [max_eq_left hnonpos]
        have hrzero : r = 0 := Nat.sub_eq_zero_of_le hn
        simp only [hrzero, Nat.cast_zero]
    have htwo (k : ℕ) : (2 : ℝ) * (k.choose 2 : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) := by
      induction k with
      | zero => norm_num [Nat.choose]
      | succ k ih =>
        rw [Nat.choose_succ_succ k 1]
        simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
        nlinarith only [ih]
    have hthree (k : ℕ) : (6 : ℝ) * (k.choose 3 : ℝ) =
        (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) := by
      induction k with
      | zero => norm_num [Nat.choose]
      | succ k ih =>
        rw [Nat.choose_succ_succ k 2]
        simp only [Nat.cast_add, Nat.cast_succ]
        nlinarith only [ih, htwo k]
    have hcast :
        (G.cliqueNum : ℝ) * ((G.cliqueNum : ℝ) - 1) *
            ((G.cliqueNum : ℝ) - 2) +
          3 * ((cᶜ).card : ℝ) * (r : ℝ) * ((r : ℝ) - 1)
        ≤ 6 * ((G.cliqueFinset 3).card : ℝ) := by
      calc
        _ = 6 * ((G.cliqueNum.choose 3 : ℝ) +
            ((cᶜ).card : ℝ) * (r.choose 2 : ℝ)) := by
          calc
            _ = 6 * (G.cliqueNum.choose 3 : ℝ) +
                3 * ((cᶜ).card : ℝ) *
                  ((r : ℝ) * ((r : ℝ) - 1)) := by
              rw [hthree G.cliqueNum]
              ring
            _ = _ := by
              rw [← htwo r]
              ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcountR (by norm_num)
    simpa only [hOreal, hrreal] using hcast
