import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic




open scoped BigOperators
theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem hull3d_chromatic_number_le_0_0_1_min_degree_size_5_5_47ced30dbf96 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (((1 / 10 : ℝ) * (G.edgeFinset.card : ℝ)) + (11 / 2 : ℝ)) := by
  classical
  let k : ℕ := G.chromaticNumber.toNat
  obtain ⟨c⟩ := G.colorable_chromaticNumber_of_fintype
  let H : SimpleGraph (Fin k) := G.map c
  have hhom : G →g H :=
    SimpleGraph.Hom.map c G (fun {v w} h => c.valid h)
  have hchi : H.chromaticNumber = (k : ℕ∞) := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using H.chromaticNumber_le_card
    · exact (ENat.natCast_toNat_le_self G.chromaticNumber).trans
        (SimpleGraph.chromaticNumber_mono_of_hom hhom)
  have htop : H = ⊤ :=
    SimpleGraph.eq_top_of_chromaticNumber_eq_card (G := H)
      (by simpa only [Fintype.card_fin] using hchi)
  have hsub : H.edgeFinset ⊆ G.edgeFinset.image (Sym2.map c) := by
    intro e he
    obtain ⟨i, j⟩ := e
    have hij : H.Adj i j := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    obtain ⟨_, v, w, hvw, hvi, hwj⟩ :=
      (SimpleGraph.map_adj' c G i j).mp hij
    refine Finset.mem_image.mpr ⟨s(v, w), ?_, ?_⟩
    · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hvw
    · simp only [Sym2.map_mk, hvi, hwj]
  have hcard : H.edgeFinset.card ≤ G.edgeFinset.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have hsum : k * (k - 1) = 2 * H.edgeFinset.card := by
    calc
      k * (k - 1) = ∑ i : Fin k, H.degree i := by
        have hdeg (i : Fin k) : H.degree i = k - 1 := by
          have hn : H.neighborFinset i =
              (Finset.univ : Finset (Fin k)).erase i := by
            ext j
            simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase,
              Finset.mem_univ, and_true, htop, SimpleGraph.top_adj, ne_comm]
          change (H.neighborFinset i).card = k - 1
          rw [hn, Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp only [Finset.card_univ, Fintype.card_fin]
        simp only [hdeg, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.nsmul_eq_mul]
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hbound : k * (k - 1) ≤ 2 * G.edgeFinset.card := by
    rw [hsum]
    exact Nat.mul_le_mul_left 2 hcard
  change (k : ℝ) ≤ (1 / 10 : ℝ) * (G.edgeFinset.card : ℝ) + (11 / 2 : ℝ)
  by_cases hk : k ≤ 1
  · have hkR : (k : ℝ) ≤ 1 := by exact_mod_cast hk
    have hmR : (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) := Nat.cast_nonneg _
    linarith only [hkR, hmR]
  have hk1 : 1 ≤ k := by omega
  have hboundR : (k : ℝ) * ((k : ℝ) - 1) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have h : (k : ℝ) * ((k - 1 : ℕ) : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast hbound
    simpa only [Nat.cast_sub hk1, Nat.cast_one] using h
  have hprod : (0 : ℝ) ≤ ((k : ℝ) - 10) * ((k : ℝ) - 11) := by
    by_cases hk10 : k ≤ 10
    · have hk10R : (k : ℝ) ≤ 10 := by exact_mod_cast hk10
      exact mul_nonneg_of_nonpos_of_nonpos
        (by linarith only [hk10R]) (by linarith only [hk10R])
    · have hk11 : 11 ≤ k := by omega
      have hk11R : (11 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk11
      exact mul_nonneg
        (by linarith only [hk11R]) (by linarith only [hk11R])
  nlinarith only [hboundR, hprod]
theorem composed_2d2bb804bd98be4f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (((1 / 10 : ℝ) * (G.edgeFinset.card : ℝ)) + (11 / 2 : ℝ)) := by
  exact le_trans (archetype_chi_ge_omega G) (hull3d_chromatic_number_le_0_0_1_min_degree_size_5_5_47ced30dbf96 G)
