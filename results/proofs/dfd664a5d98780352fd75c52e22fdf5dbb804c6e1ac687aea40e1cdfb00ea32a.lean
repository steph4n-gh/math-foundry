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
theorem composed_04950e5f807d8d18 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (1 : ℝ)) := by
  exact (archetype_chi_ge_omega G).trans (archetype_spectral_wilf G)
