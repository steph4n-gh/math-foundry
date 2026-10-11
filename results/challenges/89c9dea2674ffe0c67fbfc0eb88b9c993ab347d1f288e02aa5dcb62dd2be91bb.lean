import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic







open scoped BigOperators

theorem hull3d_max_degree_ge_0_1_order_density_0_is_regular_3887d517131d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.maxDegree : ℝ) ≥ (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) := by
  classical
  by_cases hsmall : Fintype.card V < 2
  · rw [if_pos hsmall]
    exact Nat.cast_nonneg _
  · rw [if_neg hsmall]
    have hn : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (Nat.not_lt.mp hsmall)
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
    apply (div_le_iff₀ hden).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
          (Fintype.card V : ℝ) * (G.maxDegree : ℝ) := hsumR
      _ ≤ ((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) *
          ((Fintype.card V : ℝ) - 1) :=
        le_mul_of_one_le_right
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (by linarith)
      _ = (G.maxDegree : ℝ) *
          ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by ring

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
theorem hull3d_signless_laplacian_spectral_radius_ge_0_2_normalized_laplacian_spectral_gap_max_degree_0_is_regular_26c733c31f3e {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ ((2 : ℝ) * (G.maxDegree : ℝ)) := by
  sorry
