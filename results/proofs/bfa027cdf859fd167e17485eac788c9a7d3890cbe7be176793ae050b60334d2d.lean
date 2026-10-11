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
theorem hull3d_chromatic_number_ge_3__1_average_degree_size_0_is_regular_c63a1b194af4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (G.chromaticNumber.toNat : ℝ) ≥ (((3 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - (G.edgeFinset.card : ℝ)) := by
  classical
  have hchi0 : (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
  by_cases hn0 : Fintype.card V = 0
  · simp only [if_pos hn0, mul_zero, zero_sub]
    linarith only [hchi0, hm0]
  obtain ⟨d, hd⟩ := h_guard
  have hsum : Fintype.card V * d = 2 * G.edgeFinset.card := by
    simpa only [hd.degree_eq, Finset.sum_const, Finset.card_univ,
      Nat.nsmul_eq_mul] using G.sum_degrees_eq_twice_card_edges
  have hsumR : (Fintype.card V : ℝ) * (d : ℝ) =
      2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum
  have hnpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hn0
  have hnposR : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast hnpos
  have havg : (2 : ℝ) * (G.edgeFinset.card : ℝ) /
      (Fintype.card V : ℝ) = (d : ℝ) := by
    apply (div_eq_iff (ne_of_gt hnposR)).mpr
    nlinarith only [hsumR]
  rw [if_neg hn0, havg]
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hnpos
  have hdlt : d < Fintype.card V := by
    simpa only [hd.degree_eq] using G.degree_lt_card_verts v
  by_cases hd0 : d = 0
  · have hd0R : (d : ℝ) = 0 := by exact_mod_cast hd0
    linarith only [hchi0, hm0, hd0R]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hvpos : 0 < G.degree v := by
    rw [hd.degree_eq v]
    exact hdpos
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hvpos
  have hfinite : G.chromaticNumber ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top (Fintype.card V))
      G.chromaticNumber_le_card
  have hchi2Nat : 2 ≤ G.chromaticNumber.toNat := by
    simpa only [ENat.toNat_ofNat] using
      (ENat.toNat_le_toNat
        (SimpleGraph.two_le_chromaticNumber_of_adj hvw) hfinite)
  have hchi2 : (2 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) := by
    exact_mod_cast hchi2Nat
  have hcomplete (hfull : d = Fintype.card V - 1) :
      (G.chromaticNumber.toNat : ℝ) = (Fintype.card V : ℝ) := by
    have htop : G = ⊤ := by
      apply SimpleGraph.eq_top_iff_forall_isUniversal.mpr
      intro u
      apply (G.degree_eq_card_sub_one u).mp
      exact (hd.degree_eq u).trans hfull
    rw [htop, SimpleGraph.chromaticNumber_top, ENat.toNat_natCast]
  by_cases hn6 : 6 ≤ Fintype.card V
  · have hn6R : (6 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hn6
    have hp : (0 : ℝ) ≤ ((Fintype.card V : ℝ) - 6) * (d : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hn6R) (Nat.cast_nonneg d)
    nlinarith only [hchi0, hsumR, hp]
  have hcases : Fintype.card V = 2 ∨ Fintype.card V = 3 ∨
      Fintype.card V = 4 ∨ Fintype.card V = 5 := by
    omega
  rcases hcases with hn2 | hn3 | hn4 | hn5
  · have hd1 : d = 1 := by omega
    have hn2R : (Fintype.card V : ℝ) = 2 := by exact_mod_cast hn2
    have hd1R : (d : ℝ) = 1 := by exact_mod_cast hd1
    nlinarith only [hchi2, hsumR, hn2R, hd1R]
  · have hs : 3 * d = 2 * G.edgeFinset.card := by
      simpa only [hn3] using hsum
    have hd2 : d = 2 := by omega
    have hc := hcomplete (by omega)
    have hn3R : (Fintype.card V : ℝ) = 3 := by exact_mod_cast hn3
    have hd2R : (d : ℝ) = 2 := by exact_mod_cast hd2
    nlinarith only [hc, hsumR, hn3R, hd2R]
  · have hn4R : (Fintype.card V : ℝ) = 4 := by exact_mod_cast hn4
    by_cases hdlow : d ≤ 2
    · have hdlowR : (d : ℝ) ≤ 2 := by exact_mod_cast hdlow
      nlinarith only [hchi2, hsumR, hn4R, hdlowR]
    · have hd3 : d = 3 := by omega
      have hc := hcomplete (by omega)
      have hd3R : (d : ℝ) = 3 := by exact_mod_cast hd3
      nlinarith only [hc, hsumR, hn4R, hd3R]
  · have hdle : d ≤ 4 := by omega
    have hdleR : (d : ℝ) ≤ 4 := by exact_mod_cast hdle
    have hn5R : (Fintype.card V : ℝ) = 5 := by exact_mod_cast hn5
    nlinarith only [hchi2, hsumR, hn5R, hdleR]
