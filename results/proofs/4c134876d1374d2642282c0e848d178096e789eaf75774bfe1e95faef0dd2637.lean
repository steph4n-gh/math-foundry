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

theorem model_f802d84309924757f734 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((2 : ℝ) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) - (1 : ℝ))) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  have hmax : G.maxDegree ≤ 2 := by
    have hh : (G.maxDegree : ℝ) < 3 := by
      linarith only [h_guard.2.1]
    have hn : G.maxDegree < 3 := by exact_mod_cast hh
    omega
  have hdeg (v : V) : G.degree v = 0 ∨ G.degree v = 1 ∨ G.degree v = 2 := by
    have hh := (G.degree_le_maxDegree v).trans hmax
    omega
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  letI : Fintype K := Fintype.ofFinite K
  let E : V → (K → ZMod 2) := fun v x => (x : V → ZMod 2) v
  let Q := {q : K → ZMod 2 // q ≠ 0 ∧ ∃ v : V, E v = q}
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → V := fun q => Classical.choose q.property.2
  have hrep (q : Q) : E (rep q) = q.val :=
    Classical.choose_spec q.property.2
  have hleaf (v : V) (hv : G.degree v = 1) :
      ∃ a : V, G.neighborFinset v = {a} ∧ E a = 0 := by
    have hc : (G.neighborFinset v).card = 1 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv
    rcases Finset.card_eq_one.mp hc with ⟨a, hs⟩
    refine ⟨a, hs, ?_⟩
    funext x
    change (x : V → ZMod 2) a = 0
    have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
      x.property
    simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      hs, Finset.sum_singleton, Pi.zero_apply] using congrFun hx v
  have hpairs (v : V) (hv : G.degree v = 2) :
      ∃ a b : V, a ≠ b ∧ G.neighborFinset v = {a, b} ∧ E a = E b := by
    have hc : (G.neighborFinset v).card = 2 := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv
    rcases Finset.card_eq_two.mp hc with ⟨a, b, hab, hs⟩
    refine ⟨a, b, hab, hs, ?_⟩
    funext x
    change (x : V → ZMod 2) a = (x : V → ZMod 2) b
    have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
      x.property
    have hsum : (x : V → ZMod 2) a + (x : V → ZMod 2) b = 0 := by
      simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
        hs, Finset.sum_pair hab, Pi.zero_apply] using congrFun hx v
    simpa only [ZMod.neg_eq_self_mod_two] using
      (eq_neg_iff_add_eq_zero.mpr hsum)
  have hsame (w a b : V) (hw : G.degree w = 2)
      (ha : G.Adj w a) (hb : G.Adj w b) : E a = E b := by
    rcases hpairs w hw with ⟨u, v, huv, hs, he⟩
    have ha' : a = u ∨ a = v := by
      simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using
        ((G.mem_neighborFinset w a).mpr ha)
    have hb' : b = u ∨ b = v := by
      simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using
        ((G.mem_neighborFinset w b).mpr hb)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · rfl
    · exact he
    · exact he.symm
    · rfl
  have hcheck (w a : V) (hwa : G.Adj w a) (ha : E a ≠ 0) :
      G.degree w = 2 ∧ ∀ b : V, G.Adj w b → E b = E a := by
    have hpos : 0 < G.degree w := by
      have hc : 0 < (G.neighborFinset w).card :=
        Finset.card_pos.mpr ⟨a, (G.mem_neighborFinset w a).mpr hwa⟩
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc
    rcases hdeg w with hw0 | hw1 | hw2
    · omega
    · rcases hleaf w hw1 with ⟨b, hs, hb⟩
      have hab : a = b := by
        simpa only [hs, Finset.mem_singleton] using
          ((G.mem_neighborFinset w a).mpr hwa)
      exact (ha (by simpa only [hab] using hb)).elim
    · exact ⟨hw2, fun b hb => hsame w b a hw2 hb hwa⟩
  let s : Set V := {v | E v ≠ 0}
  let H : SimpleGraph s := G.induce s
  have hH : H.IsAcyclic := h_guard.1.induce s
  have hnoone (u : s) : H.degree u ≠ 1 := by
    intro hu
    obtain ⟨a, ha, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hu
    have hga : G.Adj u.val a.val := ha
    have hh := hcheck u.val a.val hga a.property
    have hall : G.neighborSet u.val ⊆ s := by
      intro b hb
      change E b ≠ 0
      intro hz
      exact a.property ((hh.2 b hb).symm.trans hz)
    have hdeq : H.degree u = G.degree u.val :=
      SimpleGraph.degree_induce_of_neighborSet_subset hall
    have hd2 : G.degree u.val = 2 := hh.1
    omega
  have hactive_nonadj (v w : V) (hv : E v ≠ 0) (hw : E w ≠ 0) :
      ¬G.Adj v w := by
    intro hadj
    letI : Nonempty s := ⟨⟨v, hv⟩⟩
    have hedge : H.Adj ⟨v, hv⟩ ⟨w, hw⟩ := hadj
    obtain ⟨u, z, p, hp, hmaxp⟩ :=
      SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
    have hpedge : (SimpleGraph.Walk.cons hedge SimpleGraph.Walk.nil).IsPath := by
      apply (SimpleGraph.Walk.cons_isPath_iff _ _).mpr
      refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
      simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using hedge.ne
    have hlen : 1 ≤ p.length := by
      simpa only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil,
        Nat.zero_add] using
        hmaxp ⟨v, hv⟩ ⟨w, hw⟩
          (SimpleGraph.Walk.cons hedge SimpleGraph.Walk.nil) hpedge
    have hnil : ¬p.Nil :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mpr (by omega)
    have hone : H.degree u = 1 := by
      apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
      refine ⟨p.snd, p.adj_snd hnil, ?_⟩
      intro a ha
      have hmem : a ∈ p.support := by
        by_contra hn
        have hh : p.length + 1 ≤ p.length := by
          simpa only [SimpleGraph.Walk.length_cons] using
            hmaxp a z (SimpleGraph.Walk.cons ha.symm p) (hp.cons hn)
        omega
      exact hH.eq_snd_of_adj_start hp ha hmem
    exact hnoone u hone
  let f : K →ₗ[ZMod 2] (Q → ZMod 2) :=
    { toFun := fun x q => (x : V → ZMod 2) (rep q)
      map_add' := by
        intro x y
        funext q
        rfl
      map_smul' := by
        intro a x
        funext q
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext v
    by_cases hz : E v = 0
    · have hx0 : (x : V → ZMod 2) v = 0 := congrFun hz x
      have hy0 : (y : V → ZMod 2) v = 0 := congrFun hz y
      rw [hx0, hy0]
    · let q : Q := ⟨E v, hz, ⟨v, rfl⟩⟩
      calc
        (x : V → ZMod 2) v = (x : V → ZMod 2) (rep q) :=
          (congrFun (hrep q) x).symm
        _ = (y : V → ZMod 2) (rep q) := congrFun hxy q
        _ = (y : V → ZMod 2) v := congrFun (hrep q) y
  have hkdim : Module.finrank (ZMod 2) K ≤ Fintype.card Q := by
    calc
      _ ≤ Module.finrank (ZMod 2) (Q → ZMod 2) :=
        LinearMap.finrank_le_finrank_of_injective hf
      _ = Fintype.card Q := Module.finrank_fintype_fun_eq_card (ZMod 2)
  let fiber : Q → Finset V := fun q =>
    (Finset.univ : Finset V).filter (fun v => E v = q.val)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  have hdpos : 1 ≤ d := by
    have hdm : d ∈ weights := Finset.min'_mem weights hw
    rcases Finset.mem_union.mp hdm with hs | hi
    · have heq : d = Fintype.card V + 1 := Finset.mem_singleton.mp hs
      omega
    · obtain ⟨x, hx, hxd⟩ := Finset.mem_image.mp hi
      have hx0 : x ≠ 0 := (Finset.mem_filter.mp hx).2.1
      have hh : 0 < hammingNorm x := hammingNorm_pos_iff.mpr hx0
      omega
  have hbound (q : Q) : d ≤ (fiber q).card := by
    let c : V → ZMod 2 := fun v => if E v = q.val then 1 else 0
    have hc0 : c ≠ 0 := by
      intro hc
      have hh := congrFun hc (rep q)
      simpa [c, hrep q] using hh
    have hker : (G.adjMatrix (ZMod 2)).mulVecLin c = 0 := by
      funext v
      rcases hdeg v with hv0 | hv1 | hv2
      · have hs : G.neighborFinset v = ∅ := by
          apply Finset.card_eq_zero.mp
          simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv0
        simp only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_empty, Pi.zero_apply]
      · rcases hleaf v hv1 with ⟨a, hs, ha⟩
        have hne : E a ≠ q.val := by
          intro hh
          exact q.property.1 (hh.symm.trans ha)
        have hca : c a = 0 := by simp [c, hne]
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_singleton, Pi.zero_apply] using hca
      · rcases hpairs v hv2 with ⟨a, b, hab, hs, he⟩
        have hcab : c a = c b := by
          dsimp only [c]
          rw [he]
        have hz : c b + c b = 0 := by
          simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (c b)
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, hcab, Pi.zero_apply] using hz
    have hcw : hammingNorm c ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨c, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc0, hker⟩
    have hd : d ≤ hammingNorm c := Finset.min'_le weights (hammingNorm c) hcw
    simpa [hammingNorm, c, fiber] using hd
  let checks : Q → Finset V := fun q =>
    Finset.univ.filter (fun w => ∃ v ∈ fiber q, G.Adj w v)
  have hchecks (q : Q) (w : V) (hwq : w ∈ checks q) :
      G.degree w = 2 ∧ E w = 0 ∧
        ∀ b : V, G.Adj w b → E b = q.val := by
    rcases (Finset.mem_filter.mp hwq).2 with ⟨a, ha, hwa⟩
    have hea : E a = q.val := (Finset.mem_filter.mp ha).2
    have hanz : E a ≠ 0 := by
      intro hz
      exact q.property.1 (hea.symm.trans hz)
    have hh := hcheck w a hwa hanz
    refine ⟨hh.1, ?_, fun b hb => (hh.2 b hb).trans hea⟩
    by_contra hn
    exact hactive_nonadj w a hn hanz hwa
  have hlow (q : Q) : d - 1 ≤ (checks q).card := by
    have hrep_mem : rep q ∈ fiber q :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ (rep q), hrep q⟩
    let R : Finset V := (fiber q).erase (rep q)
    have hRcard : R.card + 1 = (fiber q).card := by
      simpa only [R] using Finset.card_erase_add_one hrep_mem
    let e : (R → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
      { toFun := fun u v => if h : v ∈ R then u ⟨v, h⟩ else 0
        map_add' := by
          intro u u'
          funext v
          by_cases hv : v ∈ R <;> simp [hv]
        map_smul' := by
          intro a u
          funext v
          by_cases hv : v ∈ R <;> simp [hv] }
    let g : (R → ZMod 2) →ₗ[ZMod 2] (checks q → ZMod 2) :=
      { toFun := fun u w => A (e u) w
        map_add' := by
          intro u u'
          funext w
          change A (e (u + u')) w = A (e u) w + A (e u') w
          simp only [map_add, Pi.add_apply]
        map_smul' := by
          intro a u
          funext w
          change A (e (a • u)) w = a • A (e u) w
          simp only [map_smul, Pi.smul_apply] }
    have hgzero (u : R → ZMod 2) (hu : g u = 0) : u = 0 := by
      have hAu : A (e u) = 0 := by
        funext w
        change A (e u) w = 0
        by_cases hwq : w ∈ checks q
        · exact congrFun hu ⟨w, hwq⟩
        · change ((G.adjMatrix (ZMod 2)).mulVecLin (e u)) w = 0
          rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
          apply Finset.sum_eq_zero
          intro v hv
          have hvR : v ∉ R := by
            intro hvR
            apply hwq
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,
              ⟨v, Finset.mem_of_mem_erase hvR,
                (G.mem_neighborFinset w v).mp hv⟩⟩
          simp [e, hvR]
      let z : K := ⟨e u, hAu⟩
      funext v
      change u v = 0
      have hvq : E v.val = q.val :=
        (Finset.mem_filter.mp (Finset.mem_of_mem_erase v.property)).2
      have heq : E v.val = E (rep q) := hvq.trans (hrep q).symm
      calc
        u v = e u v.val := by simp [e, v.property]
        _ = e u (rep q) := congrFun heq z
        _ = 0 := by simp [e, R]
    have hg : Function.Injective g := by
      intro u u' h
      apply sub_eq_zero.mp
      apply hgzero
      rw [map_sub, h, sub_self]
    have hRle : R.card ≤ (checks q).card := by
      have hh := LinearMap.finrank_le_finrank_of_injective hg
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hh
    have hd := hbound q
    omega
  have hdisj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint checks := by
    intro q _ z _ hqz
    apply Finset.disjoint_left.mpr
    intro w hwq hwz
    rcases (Finset.mem_filter.mp hwz).2 with ⟨a, ha, hwa⟩
    have heq : E a = q.val := (hchecks q w hwq).2.2 a hwa
    have hez : E a = z.val := (Finset.mem_filter.mp ha).2
    apply hqz
    apply Subtype.ext
    exact heq.symm.trans hez
  let T : Finset V := (Finset.univ : Finset Q).biUnion checks
  have hsum : (∑ q : Q, (checks q).card) = T.card :=
    (Finset.card_biUnion hdisj).symm
  have hT (w : V) (hwT : w ∈ T) :
      G.degree w = 2 ∧ E w = 0 ∧
        ∀ v : V, G.Adj w v → E v ≠ 0 := by
    rcases Finset.mem_biUnion.mp hwT with ⟨q, _, hwq⟩
    have hh := hchecks q w hwq
    refine ⟨hh.1, hh.2.1, ?_⟩
    intro v hv hz
    exact q.property.1 ((hh.2.2 v hv).symm.trans hz)
  have hindepT (v w : V) (hv : v ∈ T) (hwT : w ∈ T) : ¬G.Adj v w := by
    intro hadj
    exact (hT v hv).2.2 w hadj (hT w hwT).2.1
  have hincdisj : (↑T : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro v hv w hwT hne
    apply Finset.disjoint_left.mpr
    intro e hev hew
    exact hindepT v w hv hwT
      (G.adj_of_mem_incidenceSet hne
        (SimpleGraph.mem_incidenceFinset.mp hev)
        (SimpleGraph.mem_incidenceFinset.mp hew))
  have hedges : (∑ w ∈ T, G.degree w) ≤ G.edgeFinset.card := by
    calc
      _ = ∑ w ∈ T, (G.incidenceFinset w).card := by
        simp only [SimpleGraph.card_incidenceFinset_eq_degree]
      _ = (T.biUnion (fun w => G.incidenceFinset w)).card :=
        (Finset.card_biUnion hincdisj).symm
      _ ≤ G.edgeFinset.card := by
        apply Finset.card_le_card
        intro e he
        rcases Finset.mem_biUnion.mp he with ⟨w, _, hew⟩
        exact G.incidenceFinset_subset w hew
  have htwo : 2 * T.card ≤ G.edgeFinset.card := by
    calc
      _ = ∑ _w ∈ T, 2 := by simp [Nat.mul_comm]
      _ = ∑ w ∈ T, G.degree w := by
        apply Finset.sum_congr rfl
        intro w hwT
        exact (hT w hwT).1.symm
      _ ≤ G.edgeFinset.card := hedges
  have hcount : Module.finrank (ZMod 2) K * (d - 1) ≤ T.card := by
    calc
      _ ≤ Fintype.card Q * (d - 1) := Nat.mul_le_mul_right (d - 1) hkdim
      _ = ∑ _q : Q, (d - 1) := by simp [Nat.nsmul_eq_mul]
      _ ≤ ∑ q : Q, (checks q).card := Finset.sum_le_sum (fun q _ => hlow q)
      _ = T.card := hsum
  have hnat : 2 * Module.finrank (ZMod 2) K * (d - 1) ≤ G.edgeFinset.card := by
    simpa only [Nat.mul_assoc] using
      ((Nat.mul_le_mul_left 2 hcount).trans htwo)
  have hreal : ((2 : ℝ) * (Module.finrank (ZMod 2) K : ℝ)) *
      ((d - 1 : ℕ) : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hnat
  change ((2 : ℝ) * (Module.finrank (ZMod 2) K : ℝ)) *
    ((d : ℝ) - 1) ≤ (G.edgeFinset.card : ℝ)
  simpa only [Nat.cast_sub hdpos, Nat.cast_one] using hreal
