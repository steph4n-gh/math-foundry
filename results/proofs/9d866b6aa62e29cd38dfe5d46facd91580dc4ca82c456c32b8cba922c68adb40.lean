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

theorem model_19a4636366d151f7cbf8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ))) :
    (((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) - (G.maxDegree : ℝ)) * (((((Fintype.card V : ℝ) - (1 : ℝ)) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues))) - ((4 : ℝ) * (G.edgeFinset.card : ℝ))) + ((3 : ℝ) * (G.maxDegree : ℝ)))) ≥ ((G.maxDegree : ℝ) ^ 2) := by
  classical
  have hV : Fintype.card V ≠ 0 := by
    intro hz
    rw [hz] at h_guard
    norm_num at h_guard
  letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  simp only [if_neg hV]
  let n : ℝ := Fintype.card V
  let m : ℝ := G.edgeFinset.card
  let D : ℝ := G.maxDegree
  let Q : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ
  let hQ : Q.IsHermitian :=
    (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
  let q : ℝ := sSup (Set.range hQ.eigenvalues)
  change (q - D) * ((n - 1) * q - 4 * m + 3 * D) ≥ D ^ 2
  have hu (i : V) : hQ.eigenvalues i ≤ q :=
    le_csSup (Set.finite_range hQ.eigenvalues).bddAbove
      (Set.mem_range_self i)
  let C : Matrix V V ℝ := q • (1 : Matrix V V ℝ) - Q
  have hC : C.PosSemidef := by
    have hp :
        (Matrix.diagonal (fun i : V => q - hQ.eigenvalues i)).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hu i))
    have hspec :
        Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hQ.eigenvectorUnitary
          (Matrix.diagonal hQ.eigenvalues) = Q :=
      hQ.spectral_theorem.symm
    have hs :
        Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hQ.eigenvectorUnitary
          (Matrix.diagonal (fun i : V => q - hQ.eigenvalues i)) = C := by
      dsimp only [C]
      rw [← Matrix.diagonal_sub (fun _ : V => q) hQ.eigenvalues,
        ← Matrix.smul_one_eq_diagonal q, map_sub, map_smul, map_one, hspec]
    rw [← hs]
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose] using
      hp.mul_mul_conjTranspose_same (hQ.eigenvectorUnitary : Matrix V V ℝ)
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hdv : (G.degree v : ℝ) = D := by
    change (G.degree v : ℝ) = (G.maxDegree : ℝ)
    exact_mod_cast hv.symm
  let u : V → ℝ := Pi.single v 1
  let e : V → ℝ := fun _ => 1
  have hee : dotProduct e e = n := by
    simp [dotProduct, e, n]
  have huu : dotProduct u u = 1 := by
    simp [u]
  have hue : dotProduct u e = 1 := by
    simp [u, e]
  have hQe : Matrix.mulVec Q e = fun w => 2 * (G.degree w : ℝ) := by
    ext w
    simp [Q, e, Matrix.add_mulVec, G.degMatrix_mulVec_apply,
      G.adjMatrix_mulVec_apply, G.card_neighborFinset_eq_degree, two_mul]
  have hsum : (∑ w : V, (G.degree w : ℝ)) = 2 * m := by
    dsimp only [m]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hQee : dotProduct e (Matrix.mulVec Q e) = 4 * m := by
    rw [hQe]
    change (∑ w : V, (1 : ℝ) * (2 * (G.degree w : ℝ))) = 4 * m
    simp only [one_mul, ← Finset.mul_sum, hsum]
    ring
  have hQue : dotProduct u (Matrix.mulVec Q e) = 2 * D := by
    rw [hQe]
    simp only [u, single_dotProduct, one_mul, hdv]
  have hQuu : dotProduct u (Matrix.mulVec Q u) = D := by
    change dotProduct (Pi.single v (1 : ℝ))
      (Matrix.mulVec Q (Pi.single v (1 : ℝ))) = D
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    change Q v v = D
    simpa [Q, SimpleGraph.degMatrix] using hdv
  have hCform (x y : V → ℝ) :
      dotProduct x (Matrix.mulVec C y) =
        q * dotProduct x y - dotProduct x (Matrix.mulVec Q y) := by
    dsimp only [C]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hCuu : dotProduct u (Matrix.mulVec C u) = q - D := by
    rw [hCform, huu, hQuu]
    ring
  have hCue : dotProduct u (Matrix.mulVec C e) = q - 2 * D := by
    rw [hCform, hue, hQue]
    ring
  have hCee : dotProduct e (Matrix.mulVec C e) = n * q - 4 * m := by
    rw [hCform, hee, hQee]
    ring
  have hCeu : dotProduct e (Matrix.mulVec C u) = q - 2 * D := by
    simpa only [star_trivial, hCue] using
      hC.isHermitian.star_dotProduct_mulVec_comm e u
  have hpoly (t : ℝ) :
      0 ≤ (q - D) * (t * t) + (2 * (q - 2 * D)) * t + (n * q - 4 * m) := by
    have h := hC.dotProduct_mulVec_nonneg (t • u + e)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hCuu, hCue, hCeu, hCee] at h
    convert h using 1 <;> ring
  have hdis := discrim_le_zero hpoly
  dsimp only [discrim] at hdis
  nlinarith only [hdis]
