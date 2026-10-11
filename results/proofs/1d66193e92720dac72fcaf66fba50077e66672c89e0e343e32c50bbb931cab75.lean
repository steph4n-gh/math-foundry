import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

theorem hull_density_le_0_min_degree_1_13d2302d7d68 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) ≤ (((0 : ℝ) * (G.minDegree : ℝ)) + (1 : ℝ)) := by
  simp only [zero_mul, zero_add]
  split_ifs with h
  · norm_num
  · have hn : 2 ≤ Fintype.card V := by omega
    have hn1 : 1 ≤ Fintype.card V := by omega
    have hnR : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hn
    have he := Nat.mul_le_mul_left 2 G.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_two_right] at he
    have hb : 2 * G.edgeFinset.card ≤ Fintype.card V * (Fintype.card V - 1) := by
      apply he.trans
      simpa only [Nat.mul_comm] using
        (Nat.div_mul_le_self (Fintype.card V * (Fintype.card V - 1)) 2)
    have hbR : (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
        (Fintype.card V : ℝ) * ((Fintype.card V - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb
    rw [Nat.cast_sub hn1, Nat.cast_one] at hbR
    have hp : 0 < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    exact (div_le_one hp).2 hbR
