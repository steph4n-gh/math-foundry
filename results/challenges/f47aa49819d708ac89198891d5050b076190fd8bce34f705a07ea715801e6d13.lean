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

theorem archetype_chi_ge_omega {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≥ (G.cliqueNum : ℝ) := by
  exact_mod_cast (ENat.toNat_le_toNat G.cliqueNum_le_chromaticNumber (ne_top_of_le_ne_top (by simp) G.chromaticNumber_le_card))

theorem chromatic_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.chromaticNumber.toNat : ℝ) ≤ (Fintype.card V : ℝ) := by
  exact_mod_cast (ENat.toNat_le_of_le_natCast G.chromaticNumber_le_card)

theorem composed_2cd2dd810fbb9720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have checked_0 := chromatic_le_order G; have checked_1 := archetype_chi_ge_omega G; linarith

theorem hull_average_degree_le_1_spectral_radius_0_c2374daf0bc7 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  rw [if_neg hV]
  let r : ℝ := sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)
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
  let x : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ : V => (1 : ℝ))
  have hnorm : inner ℝ x x = (Fintype.card V : ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [x, dotProduct]
  have hinner : inner ℝ ((G.adjMatrix ℝ).toEuclideanLin x) x =
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [x, WithLp.ofLp_toLp, star_trivial]
    change (∑ v : V, (1 : ℝ) *
      Matrix.mulVec (G.adjMatrix ℝ) (fun _ : V => (1 : ℝ)) v) = _
    simp only [one_mul, SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hV
  apply (div_le_iff₀ hpos).2
  simpa only [if_neg hV, hinner, hnorm] using hq x

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

theorem signless_laplacian_avg_deg_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≥ (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  · simp only [if_neg hV]
    let hQ := (G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)
    let f : V → ℝ := hQ.eigenvalues
    have htrace : (∑ v : V, f v) = (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
      change (∑ v : V, hQ.eigenvalues v) = (2 : ℝ) * (G.edgeFinset.card : ℝ)
      have htrace_eq : Matrix.trace (G.degMatrix ℝ + G.adjMatrix ℝ) =
          ∑ v : V, hQ.eigenvalues v := by
        simpa using hQ.trace_eq_sum_eigenvalues
      rw [← htrace_eq]
      simp only [Matrix.trace_add, SimpleGraph.trace_adjMatrix, add_zero,
        SimpleGraph.degMatrix, Matrix.trace_diagonal]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hbound : (∑ v : V, f v) ≤
        (Fintype.card V : ℝ) * sSup (Set.range f) := by
      calc
        (∑ v : V, f v) ≤ ∑ _ : V, sSup (Set.range f) :=
          Finset.sum_le_sum (fun v _ =>
            le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self v))
        _ = (Fintype.card V : ℝ) * sSup (Set.range f) := by simp
    have hpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hV
    change (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤
      sSup (Set.range f)
    apply (div_le_iff₀ hpos).2
    calc
      (2 : ℝ) * (G.edgeFinset.card : ℝ) = ∑ v : V, f v := htrace.symm
      _ ≤ (Fintype.card V : ℝ) * sSup (Set.range f) := hbound
      _ = sSup (Set.range f) * (Fintype.card V : ℝ) := mul_comm _ _

theorem signless_laplacian_spectral_plus_max_deg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range ((G.isHermitian_degMatrix ℝ).add (G.isHermitian_adjMatrix ℝ)).eigenvalues)) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (G.maxDegree : ℝ)) := by
  classical
  by_cases hV : Fintype.card V = 0
  · simp only [if_pos hV, zero_add]
    exact Nat.cast_nonneg _
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
    simp only [if_neg hV]
    let hA : (G.adjMatrix ℝ).IsHermitian := G.isHermitian_adjMatrix ℝ
    let hQ : (G.degMatrix ℝ + G.adjMatrix ℝ).IsHermitian :=
      (G.isHermitian_degMatrix ℝ).add hA
    let r : ℝ := sSup (Set.range hA.eigenvalues)
    change sSup (Set.range hQ.eigenvalues) ≤ r + (G.maxDegree : ℝ)
    have hr (i : V) : hA.eigenvalues i ≤ r :=
      le_csSup (Set.finite_range hA.eigenvalues).bddAbove (Set.mem_range_self i)
    have hC : (r • (1 : Matrix V V ℝ) - G.adjMatrix ℝ).PosSemidef := by
      have hp : (Matrix.diagonal (fun i : V => r - hA.eigenvalues i)).PosSemidef :=
        Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hr i))
      have hs :
          Unitary.conjStarAlgAut ℝ (Matrix V V ℝ) hA.eigenvectorUnitary
            (Matrix.diagonal (fun i : V => r - hA.eigenvalues i)) =
          r • (1 : Matrix V V ℝ) - G.adjMatrix ℝ := by
        rw [← Matrix.diagonal_sub (fun _ : V => r) hA.eigenvalues,
          ← Matrix.smul_one_eq_diagonal r, map_sub, map_smul, map_one]
        exact congrArg (fun M : Matrix V V ℝ => r • (1 : Matrix V V ℝ) - M)
          hA.spectral_theorem.symm
      rw [← hs]
      simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
        Matrix.star_eq_conjTranspose] using
        hp.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix V V ℝ)
    have hD :
        ((G.maxDegree : ℝ) • (1 : Matrix V V ℝ) - G.degMatrix ℝ).PosSemidef := by
      rw [Matrix.smul_one_eq_diagonal, SimpleGraph.degMatrix, Matrix.diagonal_sub]
      apply Matrix.PosSemidef.diagonal
      intro i
      apply sub_nonneg.mpr
      exact_mod_cast (G.degree_le_maxDegree i)
    refine csSup_le (Set.range_nonempty hQ.eigenvalues) ?_
    rintro _ ⟨i, rfl⟩
    let x : V → ℝ := ⇑(hQ.eigenvectorBasis i)
    have hxunit : dotProduct x x = 1 := by
      have hinner :
          inner ℝ (hQ.eigenvectorBasis i) (hQ.eigenvectorBasis i) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hQ.eigenvectorBasis.orthonormal.1 i]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
    have ha := hC.dotProduct_mulVec_nonneg x
    have hd := hD.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hxunit, mul_one] at ha hd
    have heig : hQ.eigenvalues i =
        dotProduct x (Matrix.mulVec (G.degMatrix ℝ + G.adjMatrix ℝ) x) := by
      simpa only [star_trivial, RCLike.re_to_real] using hQ.eigenvalues_eq i
    rw [Matrix.add_mulVec, dotProduct_add] at heig
    linarith

theorem composed_9760f9b31100c13d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)) ≤ ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) + (G.maxDegree : ℝ)) := by
  refine le_trans (signless_laplacian_avg_deg_lower G) ?_
  exact signless_laplacian_spectral_plus_max_deg G

theorem model_f625da6cfd36c5bd35d9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + ((2 : ℝ) * ((Int.floor ((G.cliqueNum : ℝ) / (2 : ℝ))) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let q : ℕ := G.cliqueNum / 2
  obtain ⟨c, hc⟩ := G.exists_isNClique_cliqueNum
  have hq : 2 * q ≤ c.card := by
    rw [hc.card_eq]
    dsimp only [q]
    omega
  obtain ⟨s, hsc, hscard⟩ := Finset.exists_subset_card_eq (s := c) (n := 2 * q) hq
  have hsclique : G.IsClique (s : Set V) := by
    intro v hv w hw hne
    exact hc.isClique (hsc hv) (hsc hw) hne
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hzero (x : V → ZMod 2) (hx : A x = 0)
      (hout : ∀ v : V, v ∉ s → x v = 0) : x = 0 := by
    let z : ZMod 2 := ∑ w ∈ s, x w
    have hrow (v : V) (hv : v ∈ s) :
        A x v = ∑ w ∈ s.erase v, x w := by
      change (∑ w : V, (G.adjMatrix (ZMod 2)) v w * x w) = _
      calc
        _ = ∑ w ∈ s.erase v, (G.adjMatrix (ZMod 2)) v w * x w := by
          symm
          apply Finset.sum_subset (Finset.subset_univ (s.erase v))
          intro w _ hw
          by_cases hws : w ∈ s
          · have hwv : w = v := by
              by_contra hne
              exact hw (Finset.mem_erase.mpr ⟨hne, hws⟩)
            subst w
            simp
          · rw [hout w hws, mul_zero]
        _ = ∑ w ∈ s.erase v, x w := by
          apply Finset.sum_congr rfl
          intro w hw
          have hw' := Finset.mem_erase.mp hw
          have hadj : G.Adj v w := hsclique hv hw'.2 (Ne.symm hw'.1)
          simp [hadj]
    have hval (v : V) (hv : v ∈ s) : x v = z := by
      have hr : (∑ w ∈ s.erase v, x w) = 0 := by
        have hh := congrFun hx v
        rw [hrow v hv] at hh
        exact hh
      have hh := Finset.sum_erase_add s x hv
      rw [hr, zero_add] at hh
      exact hh
    have hz : z = 0 := by
      calc
        z = ∑ w ∈ s, z := Finset.sum_congr rfl (fun w hw => hval w hw)
        _ = (s.card : ZMod 2) * z := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = 0 := by
          rw [hscard, Nat.cast_mul, Nat.cast_ofNat, htwo, zero_mul, zero_mul]
    funext v
    by_cases hv : v ∈ s
    · exact (hval v hv).trans hz
    · exact hout v hv
  let p : K →ₗ[ZMod 2] ((sᶜ : Finset V) → ZMod 2) :=
    { toFun := fun x v => (x : V → ZMod 2) v.1
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hinj : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    have hx : A (x : V → ZMod 2) = 0 := x.property
    have hy : A (y : V → ZMod 2) = 0 := y.property
    have hker : A ((x : V → ZMod 2) - (y : V → ZMod 2)) = 0 := by
      rw [map_sub, hx, hy, sub_self]
    have hout : ∀ v : V, v ∉ s →
        ((x : V → ZMod 2) - (y : V → ZMod 2)) v = 0 := by
      intro v hv
      have hh := congrFun hxy ⟨v, Finset.mem_compl.mpr hv⟩
      change (x : V → ZMod 2) v = (y : V → ZMod 2) v at hh
      simp only [Pi.sub_apply, hh, sub_self]
    exact sub_eq_zero.mp (hzero _ hker hout)
  have hdim : Module.finrank (ZMod 2) K ≤ (sᶜ).card := by
    calc
      _ ≤ Module.finrank (ZMod 2) ((sᶜ : Finset V) → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hinj
      _ = (sᶜ).card := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hcount : s.card + (sᶜ).card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hnat : Module.finrank (ZMod 2) K + 2 * q ≤ Fintype.card V := by
    omega
  have hfloor : Int.floor ((G.cliqueNum : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    have hlo : 2 * q ≤ G.cliqueNum := by
      dsimp only [q]
      omega
    have hhi : G.cliqueNum < 2 * (q + 1) := by
      dsimp only [q]
      omega
    have hloR : (2 : ℝ) * (q : ℝ) ≤ (G.cliqueNum : ℝ) := by
      exact_mod_cast hlo
    have hhiR : (G.cliqueNum : ℝ) < (2 : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast hhi
    constructor <;> simp only [Int.cast_natCast] <;> linarith only [hloR, hhiR]
  change (Module.finrank (ZMod 2) K : ℝ) +
    (2 : ℝ) * (Int.floor ((G.cliqueNum : ℝ) / 2) : ℝ) ≤ (Fintype.card V : ℝ)
  rw [hfloor, Int.cast_natCast]
  exact_mod_cast hnat

theorem hull3d_order_ge__1_2_density_average_degree_1_is_tree_39f653f393cf {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsTree)) :
    (Fintype.card V : ℝ) ≥ ((((2 : ℝ) * (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ))) - (if Fintype.card V < 2 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)))) + (1 : ℝ)) := by
  have hcard : G.edgeFinset.card + 1 = Fintype.card V := h_guard.card_edgeFinset
  rcases (show Fintype.card V = 1 ∨ Fintype.card V = 2 ∨ 3 ≤ Fintype.card V by omega) with h | h | h
  · have he : G.edgeFinset.card = 0 := by omega
    norm_num [h, he]
  · have he : G.edgeFinset.card = 1 := by omega
    norm_num [h, he]
  · have hn : (3 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast h
    have hn0 : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
    have hn1 : (Fintype.card V : ℝ) - 1 ≠ 0 := by linarith
    have hz : Fintype.card V ≠ 0 := by omega
    have ht : ¬ Fintype.card V < 2 := by omega
    have he : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have he' : (G.edgeFinset.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
      linarith
    simp only [if_neg hz, if_neg ht]
    rw [he']
    have hf :
        2 * (2 * ((Fintype.card V : ℝ) - 1) / (Fintype.card V : ℝ)) -
          2 * ((Fintype.card V : ℝ) - 1) /
            ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) + 1 =
        (5 * (Fintype.card V : ℝ) - 6) / (Fintype.card V : ℝ) := by
      field_simp [ne_of_gt hn0, hn1] <;> ring
    rw [hf]
    apply (div_le_iff₀ hn0).2
    have hprod :
        0 ≤ ((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
theorem model_6ef1594add3b905d1214 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Fintype.card V : ℝ) ≥ (19999999 / 10000000 : ℝ)))) :
    ((G.cliqueNum : ℝ) * ((max (0 : ℝ) (((letI : Decidable G.Connected := Classical.propDecidable _; if G.Connected then (if h : 2 ≤ Fintype.card V then (G.isHermitian_lapMatrix ℝ).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ else (0 : ℝ)) else (0 : ℝ)) * ((Fintype.card V : ℝ) - (G.cliqueNum : ℝ))) - ((Fintype.card V : ℝ) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - ((G.cliqueNum : ℝ) - (1 : ℝ)))))) ^ 2)) ≤ ((((Fintype.card V : ℝ) ^ 3) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - ((G.cliqueNum : ℝ) - (1 : ℝ)))) * ((if Fintype.card V = 0 then (0 : ℝ) else sSup (Set.range (G.isHermitian_adjMatrix ℝ).eigenvalues)) - (if Fintype.card V = 0 then (0 : ℝ) else (2 : ℝ) * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)))) := by
  sorry
