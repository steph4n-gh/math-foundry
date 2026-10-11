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

theorem estrada_ge_energy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≥ (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) := by
  classical
  have hsum : (∑ v : V, (G.isHermitian_adjMatrix ℝ).eigenvalues v) = 0 := by
    simpa using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  have hpoint (x : ℝ) : |x| + x ≤ Real.exp x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hexp := Real.quadratic_le_exp_of_nonneg hx
      nlinarith [sq_nonneg (x - 1)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [Real.exp_pos x]
  have hbound :
      (∑ v : V, (|(G.isHermitian_adjMatrix ℝ).eigenvalues v| +
        (G.isHermitian_adjMatrix ℝ).eigenvalues v)) ≤
      ∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v) := by
    exact Finset.sum_le_sum (fun v _ => hpoint _)
  simpa only [Finset.sum_add_distrib, hsum, add_zero] using hbound

theorem graph_energy_spectral_radius_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, |(G.isHermitian_adjMatrix ℝ).eigenvalues v|) ≥ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  let f : V → ℝ := (G.isHermitian_adjMatrix ℝ).eigenvalues
  have hsum : (∑ v : V, f v) = 0 := by
    simpa [f] using (G.isHermitian_adjMatrix ℝ).trace_eq_sum_eigenvalues.symm
  by_cases hV : Fintype.card V = 0
  · haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    simp [hV]
  · haveI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    obtain ⟨v, hv⟩ := (Set.range_nonempty f).csSup_mem (Set.finite_range f)
    have hnonneg (w : V) : 0 ≤ |f w| + f w := by
      linarith [neg_abs_le (f w)]
    have hsingle : |f v| + f v ≤ ∑ w : V, (|f w| + f w) :=
      Finset.single_le_sum (fun w _ => hnonneg w) (Finset.mem_univ v)
    simp only [Finset.sum_add_distrib, hsum, add_zero] at hsingle
    change 2 * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range f)) ≤
      ∑ w : V, |f w|
    rw [if_neg hV, ← hv]
    linarith [le_abs_self (f v)]

theorem composed_35ca49dcc0267544 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ (∑ v : V, Real.exp ((G.isHermitian_adjMatrix ℝ).eigenvalues v)) := by
  exact le_trans (graph_energy_spectral_radius_lower G) (estrada_ge_energy G)

theorem hull_spectral_radius_le_1_size_0_0f3ad4f640d7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg G.edgeFinset.card
  · rw [if_neg hV]
    letI : Nonempty V :=
      Fintype.card_pos_iff.mp (Nat.pos_iff_ne_zero.mpr hV)
    let hA := G.isHermitian_adjMatrix ℝ
    refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hA.eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        (hA.eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    have hw0 : x w ≠ 0 := by
      simpa only [Pi.zero_apply] using hw
    obtain ⟨v, _, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V)
        (fun u => |x u|) Finset.univ_nonempty
    have hp : 0 < |x v| :=
      lt_of_lt_of_le (abs_pos.mpr hw0) (hmax w (Finset.mem_univ w))
    have heq : (∑ u ∈ G.neighborFinset v, x u) =
        hA.eigenvalues i * x v := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply,
        smul_eq_mul] using congrFun (hA.mulVec_eigenvectorBasis i) v
    have habs : |hA.eigenvalues i| * |x v| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        |hA.eigenvalues i| * |x v| =
            |∑ u ∈ G.neighborFinset v, x u| := by
          rw [heq, abs_mul]
        _ ≤ ∑ u ∈ G.neighborFinset v, |x u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _u ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun u _ => hmax u (Finset.mem_univ u))
        _ = (G.degree v : ℝ) * |x v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have heigen : hA.eigenvalues i ≤ (G.degree v : ℝ) :=
      (le_abs_self _).trans (le_of_mul_le_mul_right habs hp)
    have hdegree : (G.degree v : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      exact_mod_cast (G.degree_le_card_edgeFinset v)
    exact heigen.trans hdegree

theorem hull3d_size_ge_0_1_nordhaus_gaddum_spectral_product_spectral_radius_0_is_bipartite_fd5d8dffd858 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.edgeFinset.card : ℝ) ≥ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · rw [if_pos hV]
    exact Nat.cast_nonneg _
  · rw [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    apply csSup_le (Set.range_nonempty _)
    rintro r ⟨i, rfl⟩
    let x : V → ℝ := ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i)
    have hx : x ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2
        ((G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i)
    obtain ⟨v, _, hsup⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : V => |x w|)
    have hmax (w : V) : |x w| ≤ |x v| := by
      rw [← hsup]
      exact Finset.le_sup' (fun w : V => |x w|) (Finset.mem_univ w)
    have hxv : x v ≠ 0 := by
      intro hzero
      apply hx
      funext w
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa only [hzero, abs_zero] using hmax w
      · exact abs_nonneg _
    have hp : 0 < |x v| := abs_pos.mpr hxv
    have hrow : (∑ w ∈ G.neighborFinset v, x w) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i * x v := by
      simpa only [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul]
        using congrFun ((G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i) v
    have hprod : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| * |x v| ≤
        (G.degree v : ℝ) * |x v| := by
      calc
        _ = |∑ w ∈ G.neighborFinset v, x w| := by rw [hrow, abs_mul]
        _ ≤ ∑ w ∈ G.neighborFinset v, |x w| :=
          Finset.abs_sum_le_sum_abs x _
        _ ≤ ∑ _w ∈ G.neighborFinset v, |x v| :=
          Finset.sum_le_sum (fun w _ => hmax w)
        _ = (G.degree v : ℝ) * |x v| := by
          simp only [Finset.sum_const, nsmul_eq_mul,
            SimpleGraph.card_neighborFinset_eq_degree]
    have habs : |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ (G.degree v : ℝ) :=
      le_of_mul_le_mul_right hprod hp
    have hdeg : (G.degree v : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.degree_le_card_edgeFinset v
    exact (le_abs_self _).trans (habs.trans hdeg)

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem archetype_spectral_wilf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (1 : ℝ)) := by
  classical
  by_cases hempty : Fintype.card V = 0
  · have h := chromatic_le_order G
    rw [hempty, Nat.cast_zero] at h
    rw [if_pos hempty]
    linarith
  rw [if_neg hempty]
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
  change (G.chromaticNumber.toNat : ℝ) ≤ r + 1
  let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
    (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
  have hsym : (G.adjMatrix ℝ).toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
  have heig (i : V) : (G.adjMatrix ℝ).toEuclideanLin (b i) =
      (G.isHermitian_adjMatrix ℝ).eigenvalues i • b i := by
    apply WithLp.ofLp_injective 2
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
      (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
  have hle (i : V) : (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ r :=
    le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
  have hq (x : EuclideanSpace ℝ V) :
      inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x ≤ r * inner ℝ x x := by
    calc
      inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
          ∑ i : V, (G.isHermitian_adjMatrix ℝ).eigenvalues i *
            (inner ℝ x (b i)) ^ 2 := by
        rw [← b.sum_inner_mul_inner ((G.adjMatrix ℝ).toEuclideanLin x) x]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsym x (b i), heig i, inner_smul_right, real_inner_comm x (b i)]
        ring
      _ ≤ ∑ i : V, r * (inner ℝ x (b i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
      _ = r * inner ℝ x x := by
        rw [← Finset.mul_sum]
        congr 1
        calc
          (∑ i : V, (inner ℝ x (b i)) ^ 2) =
              ∑ i : V, inner ℝ x (b i) * inner ℝ (b i) x := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_comm x (b i)]
            ring
          _ = inner ℝ x x := b.sum_inner_mul_inner x x
  have hsum (s : Finset V) :
      (∑ v ∈ s, ((G.neighborFinset v ∩ s).card : ℝ)) ≤ r * (s.card : ℝ) := by
    let f : V → ℝ := fun v => if v ∈ s then 1 else 0
    let x : EuclideanSpace ℝ V := WithLp.toLp 2 f
    have hf (v : V) : f v * f v = f v := by
      by_cases hv : v ∈ s <;> simp [f, hv]
    have hvec (v : V) : Matrix.mulVec (G.adjMatrix ℝ) f v =
        ((G.neighborFinset v ∩ s).card : ℝ) := by
      rw [G.adjMatrix_mulVec_apply]
      simp [f, ← Finset.sum_filter, Finset.filter_mem_eq_inter]
    have hnorm : inner ℝ x x = (s.card : ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [x, WithLp.ofLp_toLp, star_trivial]
      change (∑ v : V, f v * f v) = (s.card : ℝ)
      simp only [hf]
      simp [f, ← Finset.sum_filter, Finset.filter_mem_eq_inter]
    have hinner : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
        ∑ v ∈ s, ((G.neighborFinset v ∩ s).card : ℝ) := by
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [x, WithLp.ofLp_toLp, star_trivial]
      change (∑ v : V, f v * Matrix.mulVec (G.adjMatrix ℝ) f v) = _
      simp only [hvec]
      simp [f, ite_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter]
    simpa only [hinner, hnorm] using hq x
  obtain ⟨v⟩ : Nonempty V :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hempty)
  have hr : 0 ≤ r := by
    have h := hsum ({v} : Finset V)
    simpa [Finset.inter_singleton_of_notMem (G.notMem_neighborFinset_self v)] using h
  have hsmall (s : Finset V) (hs : s.Nonempty) :
      ∃ a ∈ s, ((G.neighborFinset a ∩ s).card : ℝ) ≤ r := by
    by_contra hn
    have hall : ∀ a ∈ s, r < ((G.neighborFinset a ∩ s).card : ℝ) := by
      intro a ha
      exact lt_of_not_ge (fun h => hn ⟨a, ha, h⟩)
    have hlt : r * (s.card : ℝ) <
        ∑ a ∈ s, ((G.neighborFinset a ∩ s).card : ℝ) := by
      simpa [mul_comm] using Finset.sum_lt_sum_of_nonempty hs hall
    exact (not_lt_of_ge (hsum s)) hlt
  by_contra hnot
  have hlt : r + 1 < (G.chromaticNumber.toNat : ℝ) := lt_of_not_ge hnot
  have hposR : (0 : ℝ) < (G.chromaticNumber.toNat : ℝ) := by linarith
  have hpos : 0 < G.chromaticNumber.toNat := by exact_mod_cast hposR
  let k : ℕ := G.chromaticNumber.toNat - 1
  have hkchi : G.chromaticNumber.toNat = k + 1 := by
    dsimp [k]
    omega
  have hrk : r < (k : ℝ) := by
    rw [hkchi, Nat.cast_add, Nat.cast_one] at hlt
    linarith
  have hk : 0 < k := by
    have h : (0 : ℝ) < (k : ℝ) := hr.trans_lt hrk
    exact_mod_cast h
  have hpartial : ∀ s : Finset V,
      ∃ c : V → Fin k,
        ∀ v ∈ s, ∀ w ∈ s, G.Adj v w → c v ≠ c w := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hdegR⟩ := hsmall s hs
      have hdeg : (G.neighborFinset a ∩ s).card < k := by
        exact_mod_cast (hdegR.trans_lt hrk)
      obtain ⟨c, hc⟩ := ih (s.erase a) (Finset.erase_ssubset ha)
      have hcard : ((G.neighborFinset a ∩ s).image c).card <
          (Finset.univ : Finset (Fin k)).card := by
        calc
          ((G.neighborFinset a ∩ s).image c).card ≤
              (G.neighborFinset a ∩ s).card := Finset.card_image_le
          _ < (Finset.univ : Finset (Fin k)).card := by simpa using hdeg
      obtain ⟨d, _, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have hdc : ∀ w ∈ s, G.Adj a w → d ≠ c w := by
        intro w hw haw heq
        apply hd
        exact Finset.mem_image.mpr
          ⟨w, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a w).mpr haw, hw⟩,
            heq.symm⟩
      refine ⟨fun v => if v = a then d else c v, ?_⟩
      intro v hv w hw hvw
      by_cases hva : v = a
      · subst v
        have hwa : w ≠ a := hvw.ne'
        simpa [hwa] using hdc w hw hvw
      · by_cases hwa : w = a
        · subst w
          simpa [hva] using (hdc v hv hvw.symm).symm
        · have hvs : v ∈ s.erase a := Finset.mem_erase.mpr ⟨hva, hv⟩
          have hws : w ∈ s.erase a := Finset.mem_erase.mpr ⟨hwa, hw⟩
          simpa [hva, hwa] using hc v hvs w hws hvw
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
      intro v hv
      simp at hv
  obtain ⟨c, hc⟩ := hpartial Finset.univ
  have hcolor : G.Colorable k :=
    ⟨SimpleGraph.Coloring.mk c (fun {v w} h =>
      hc v (Finset.mem_univ v) w (Finset.mem_univ w) h)⟩
  have hn : G.chromaticNumber.toNat ≤ k :=
    ENat.toNat_le_of_le_natCast hcolor.chromaticNumber_le
  omega

theorem hull_density_le_0_spectral_radius_1_b85814518e6b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1))) ≤ (((0 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) + (1 : ℝ)) := by
  classical
  simp only [zero_mul, zero_add]
  by_cases h : Fintype.card V < 2
  · simp [h]
  · rw [if_neg h]
    have hn : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast (not_lt.mp h)
    have hd : (0 : ℝ) < (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    apply (div_le_one hd).2
    have hdeg (v : V) : (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) - 1 := by
      have hv : (G.degree v : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (G.degree_lt_card_verts v))
      linarith
    have heq : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : (∑ v : V, (G.degree v : ℝ)) ≤
        ∑ _v : V, ((Fintype.card V : ℝ) - 1) :=
      Finset.sum_le_sum (fun v _ => hdeg v)
    simpa only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbound
theorem spectral_spread_le_two_spectral_radius {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) ≤ ((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues))) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
    let b : OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
      (G.isHermitian_adjMatrix ℝ).eigenvectorBasis
    change r - sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) ≤ 2 * r
    have hsym : (G.adjMatrix ℝ).toEuclideanLin.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
    have heig (i : V) : (G.adjMatrix ℝ).toEuclideanLin (b i) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i • b i := by
      apply WithLp.ofLp_injective 2
      simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using
        (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i
    have hle (i : V) : (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ r :=
      le_csSup (Set.finite_range _).bddAbove ⟨i, rfl⟩
    have hq (x : EuclideanSpace ℝ V) :
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x ≤ r * inner ℝ x x := by
      calc
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
            ∑ i : V, (G.isHermitian_adjMatrix ℝ).eigenvalues i *
              (inner ℝ x (b i)) ^ 2 := by
          rw [← b.sum_inner_mul_inner ((G.adjMatrix ℝ).toEuclideanLin x) x]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hsym x (b i), heig i, inner_smul_right, real_inner_comm x (b i)]
          ring
        _ ≤ ∑ i : V, r * (inner ℝ x (b i)) ^ 2 :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _))
        _ = r * inner ℝ x x := by
          rw [← Finset.mul_sum]
          congr 1
          calc
            (∑ i : V, (inner ℝ x (b i)) ^ 2) =
                ∑ i : V, inner ℝ x (b i) * inner ℝ (b i) x := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [real_inner_comm x (b i)]
              ring
            _ = inner ℝ x x := b.sum_inner_mul_inner x x
    have hcoord (z : EuclideanSpace ℝ V) :
        inner ℝ ((G.adjMatrix ℝ).toEuclideanLin z) z =
          ∑ v : V, ∑ w ∈ G.neighborFinset v, z v * z w := by
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [WithLp.ofLp_toLp, star_trivial]
      change (∑ v : V, z v * Matrix.mulVec (G.adjMatrix ℝ) (fun w => z w) v) = _
      simp only [SimpleGraph.adjMatrix_mulVec_apply, Finset.mul_sum]
    have hlower (i : V) : -r ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
      let y : EuclideanSpace ℝ V := WithLp.toLp 2 (fun v => |b i v|)
      have hnormy : inner ℝ y y = 1 := by
        calc
          inner ℝ y y = inner ℝ (b i) (b i) := by
            simp only [EuclideanSpace.inner_eq_star_dotProduct, y,
              WithLp.ofLp_toLp, star_trivial]
            change (∑ v : V, |b i v| * |b i v|) =
              (∑ v : V, b i v * b i v)
            simp only [abs_mul_abs_self]
          _ = 1 := b.inner_eq_one i
      have heigen : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) =
          (G.isHermitian_adjMatrix ℝ).eigenvalues i := by
        rw [heig i, real_inner_smul_left, b.inner_eq_one i, mul_one]
      have habs :
          -inner ℝ ((G.adjMatrix ℝ).toEuclideanLin (b i)) (b i) ≤
            inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y := by
        simp only [hcoord]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro v hv
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro w hw
        change -(b i v * b i w) ≤ |b i v| * |b i w|
        rw [← abs_mul]
        exact neg_le_abs _
      have hy : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin y) y ≤ r := by
        simpa only [hnormy, mul_one] using hq y
      have hneg := habs.trans hy
      rw [heigen] at hneg
      linarith only [hneg]
    have hmin : -r ≤ sInf (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues) := by
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨i, rfl⟩
      exact hlower i
    linarith only [hmin]
