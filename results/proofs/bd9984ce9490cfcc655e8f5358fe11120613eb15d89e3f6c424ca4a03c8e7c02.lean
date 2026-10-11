import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic





open scoped BigOperators
theorem model_5d619440ee288c0ae37f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (((6 : ℝ) * ((G.cliqueFinset 3).card : ℝ)) + ((G.minDegree : ℝ) * (((Fintype.card V : ℝ) * (G.maxDegree : ℝ)) - ((2 : ℝ) * (G.edgeFinset.card : ℝ))))) ≤ (((2 : ℝ) * (G.edgeFinset.card : ℝ)) * ((G.maxDegree : ℝ) - (1 : ℝ))) := by
  classical
  have hlocal (v : V) :
      ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card ≤ (G.degree v).choose 2 := by
    calc
      _ ≤ ((G.neighborFinset v).powersetCard 2).card := by
        apply Finset.card_le_card_of_injOn (fun s : Finset V => s.erase v)
        · intro s hs
          obtain ⟨hs, hv⟩ := Finset.mem_filter.mp hs
          have hc := SimpleGraph.mem_cliqueFinset_iff.mp hs
          apply Finset.mem_powersetCard.mpr
          constructor
          · intro w hw
            obtain ⟨hwne, hws⟩ := Finset.mem_erase.mp hw
            exact (G.mem_neighborFinset v w).mpr (hc.isClique hv hws hwne.symm)
          · rw [Finset.card_erase_of_mem hv, hc.card_eq]
        · intro s hs t ht hst
          have hvs := (Finset.mem_filter.mp hs).2
          have hvt := (Finset.mem_filter.mp ht).2
          calc
            s = insert v (s.erase v) := (Finset.insert_erase hvs).symm
            _ = insert v (t.erase v) := congrArg (fun u : Finset V => insert v u) hst
            _ = t := Finset.insert_erase hvt
      _ = (G.degree v).choose 2 := by simp
  have hcount :
      (∑ v : V, ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card) =
        3 * (G.cliqueFinset 3).card := by
    calc
      _ = ∑ v : V, ∑ s ∈ G.cliqueFinset 3,
            if v ∈ s then (1 : ℕ) else 0 := by simp
      _ = ∑ s ∈ G.cliqueFinset 3, ∑ v : V,
            if v ∈ s then (1 : ℕ) else 0 := Finset.sum_comm
      _ = ∑ s ∈ G.cliqueFinset 3, 3 := by
        apply Finset.sum_congr rfl
        intro s hs
        simpa [Finset.filter_mem_eq_inter] using
          (SimpleGraph.mem_cliqueFinset_iff.mp hs).card_eq
      _ = 3 * (G.cliqueFinset 3).card := by simp [Nat.mul_comm]
  have htriNat :
      3 * (G.cliqueFinset 3).card ≤ ∑ v : V, (G.degree v).choose 2 := by
    rw [← hcount]
    exact Finset.sum_le_sum (fun v _ => hlocal v)
  have htri :
      (3 : ℝ) * ((G.cliqueFinset 3).card : ℝ) ≤
        ∑ v : V, ((G.degree v).choose 2 : ℝ) := by
    exact_mod_cast htriNat
  have hchoose (d : ℕ) :
      (2 : ℝ) * (d.choose 2 : ℝ) = (d : ℝ) * ((d : ℝ) - 1) := by
    by_cases hd : d = 0
    · simp [hd]
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      have hn : 2 * d.choose 2 = d * (d - 1) := by
        simpa [Nat.mul_comm] using (Nat.choose_succ_right_eq d 1)
      have hr := congrArg (fun k : ℕ => (k : ℝ)) hn
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hd1, Nat.cast_one] using hr
  have hb (v : V) :
      (2 : ℝ) * ((G.degree v).choose 2 : ℝ) ≤
        ((G.maxDegree : ℝ) + (G.minDegree : ℝ) - 1) * (G.degree v : ℝ) -
          (G.minDegree : ℝ) * (G.maxDegree : ℝ) := by
    rw [hchoose]
    have hlo : (G.minDegree : ℝ) ≤ (G.degree v : ℝ) := by
      exact_mod_cast G.minDegree_le_degree v
    have hhi : (G.degree v : ℝ) ≤ (G.maxDegree : ℝ) := by
      exact_mod_cast G.degree_le_maxDegree v
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  have hdeg :
      (∑ v : V, (G.degree v : ℝ)) = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsum :
      (2 : ℝ) * (∑ v : V, ((G.degree v).choose 2 : ℝ)) ≤
        ((G.maxDegree : ℝ) + (G.minDegree : ℝ) - 1) *
            ((2 : ℝ) * (G.edgeFinset.card : ℝ)) -
          (Fintype.card V : ℝ) * ((G.minDegree : ℝ) * (G.maxDegree : ℝ)) := by
    calc
      _ = ∑ v : V, (2 : ℝ) * ((G.degree v).choose 2 : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ v : V,
            (((G.maxDegree : ℝ) + (G.minDegree : ℝ) - 1) * (G.degree v : ℝ) -
              (G.minDegree : ℝ) * (G.maxDegree : ℝ)) :=
        Finset.sum_le_sum (fun v _ => hb v)
      _ = ((G.maxDegree : ℝ) + (G.minDegree : ℝ) - 1) *
            ((2 : ℝ) * (G.edgeFinset.card : ℝ)) -
          (Fintype.card V : ℝ) * ((G.minDegree : ℝ) * (G.maxDegree : ℝ)) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdeg]
        simp [nsmul_eq_mul]
  nlinarith only [htri, hsum]
