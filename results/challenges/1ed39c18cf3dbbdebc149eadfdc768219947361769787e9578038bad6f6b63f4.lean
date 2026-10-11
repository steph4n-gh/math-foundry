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

theorem model_b2848857e600ffe393f5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))) ≤ ((2 : ℝ) * (G.edgeFinset.card : ℝ)) := by
  classical
  by_cases hc : G.Connected
  · simp only [if_pos hc]
    by_cases hn : 2 ≤ Fintype.card V
    · simp only [dif_pos hn]
      letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      let hL := G.isHermitian_lapMatrix ℝ
      let ev := hL.eigenvalues₀
      let e : Fin (Fintype.card V) ≃ V :=
        Fintype.equivOfCardEq (Fintype.card_fin _)
      have heval (i : Fin (Fintype.card V)) :
          hL.eigenvalues (e i) = ev i := by
        simp only [Matrix.IsHermitian.eigenvalues, e, ev, Equiv.symm_apply_apply]
      have hnonneg (i : Fin (Fintype.card V)) : 0 ≤ ev i := by
        rw [← heval i, hL.eigenvalues_eq]
        simpa only [RCLike.re_to_real] using
          (SimpleGraph.posSemidef_lapMatrix ℝ G).dotProduct_mulVec_nonneg
            (⇑(hL.eigenvectorBasis (e i)))
      have hzero : ∃ i : Fin (Fintype.card V), ev i = 0 := by
        have hz : (0 : ℝ) ∈ spectrum ℝ (G.lapMatrix ℝ) :=
          G.zero_mem_spectrum_lapMatrix ℝ
        rw [hL.spectrum_real_eq_range_eigenvalues] at hz
        obtain ⟨v, hv⟩ := hz
        refine ⟨e.symm v, ?_⟩
        simpa only [ev, Matrix.IsHermitian.eigenvalues, e] using hv
      let last : Fin (Fintype.card V) := ⟨Fintype.card V - 1, by omega⟩
      let second : Fin (Fintype.card V) := ⟨Fintype.card V - 2, by omega⟩
      have hlast : ev last = 0 := by
        obtain ⟨i, hi⟩ := hzero
        have hilast : i ≤ last := by
          change i.val ≤ Fintype.card V - 1
          have hi_lt := i.isLt
          omega
        have hle : ev last ≤ ev i := hL.eigenvalues₀_antitone hilast
        rw [hi] at hle
        exact le_antisymm hle (hnonneg last)
      have hpoint (i : Fin (Fintype.card V))
          (hi : i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last) :
          ev second ≤ ev i := by
        have hne : i.val ≠ Fintype.card V - 1 := by
          intro hv
          exact (Finset.mem_erase.mp hi).1 (Fin.ext hv)
        have hisecond : i ≤ second := by
          change i.val ≤ Fintype.card V - 2
          have hi_lt := i.isLt
          omega
        exact hL.eigenvalues₀_antitone hisecond
      have htrace : (∑ i : Fin (Fintype.card V), ev i) =
          (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
        calc
          (∑ i : Fin (Fintype.card V), ev i) =
              ∑ v : V, hL.eigenvalues v := by
            simpa only [heval] using e.sum_comp hL.eigenvalues
          _ = (G.lapMatrix ℝ).trace := hL.trace_eq_sum_eigenvalues.symm
          _ = ∑ v : V, (G.degree v : ℝ) := by
            simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.trace_sub]
          _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
            exact_mod_cast G.sum_degrees_eq_twice_card_edges
      calc
        ((Fintype.card V : ℝ) - 1) * ev second =
            ∑ _i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last,
              ev second := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            Finset.card_erase_of_mem (Finset.mem_univ last), Finset.card_univ,
            Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ Fintype.card V),
            Nat.cast_one]
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (Fintype.card V))).erase last,
            ev i := Finset.sum_le_sum hpoint
        _ = ∑ i : Fin (Fintype.card V), ev i :=
          Finset.sum_erase (Finset.univ : Finset (Fin (Fintype.card V))) hlast
        _ = (2 : ℝ) * (G.edgeFinset.card : ℝ) := htrace
    · simp only [dif_neg hn, mul_zero]
      exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  · simp only [if_neg hc, mul_zero]
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)

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

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h
theorem model_f360875414013a6cbad5 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    (((((Fintype.card V : ℝ) - (1 : ℝ)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_lapMatrix ℝ).eigenvalues))) - ((2 : ℝ) * (G.edgeFinset.card : ℝ))) * (((2 : ℝ) * (G.edgeFinset.card : ℝ)) - (((Fintype.card V : ℝ) - (1 : ℝ)) * (letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ))))) ≥ ((((2 : ℝ) * (G.edgeFinset.card : ℝ)) * (((Fintype.card V : ℝ) - (1 : ℝ)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) + (((1 / 2 : ℝ) * ((Fintype.card V : ℝ) - (1 : ℝ))) * (((G.maxDegree : ℝ) - (G.minDegree : ℝ)) ^ 2))) := by
  sorry
