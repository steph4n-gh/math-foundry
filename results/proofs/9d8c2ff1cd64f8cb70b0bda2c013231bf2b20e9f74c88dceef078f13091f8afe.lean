import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem model_d5876bce3d63a657ae5c {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (Fintype.card V : ℝ) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
    letI : IsEmpty V := hV
    have hm : G.minDegree = 0 := by simp
    have hg := h_guard.2.1
    rw [hm] at hg
    norm_num at hg
  | inr hV =>
    letI : Nonempty V := hV
    rcases h_guard.1 with ⟨r, hr⟩
    have hclose : |(r : ℝ) - 2| ≤ (1 / 10000000 : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.1
    have hrlo : (1 : ℝ) < (r : ℝ) := by
      have ha := (abs_le.mp hclose).1
      linarith
    have hrhi : (r : ℝ) < (3 : ℝ) := by
      have ha := (abs_le.mp hclose).2
      linarith
    have hrlo_nat : 1 < r := by exact_mod_cast hrlo
    have hrhi_nat : r < 3 := by exact_mod_cast hrhi
    have hr2 : r = 2 := by omega
    have hdeg (v : V) : G.degree v = 2 := (hr.degree_eq v).trans hr2
    let K : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    letI : Fintype K := Fintype.ofFinite K
    let E : V → (K → ZMod 2) := fun v x => (x : V → ZMod 2) v
    let Q := {q : K → ZMod 2 // ∃ v : V, E v = q}
    letI : Fintype Q := Fintype.ofFinite Q
    let p : V → Q := fun v => ⟨E v, ⟨v, rfl⟩⟩
    let rep : Q → V := fun q => Classical.choose q.property
    have hrep (q : Q) : E (rep q) = q.val := by
      exact Classical.choose_spec q.property
    have hpairs : ∀ v : V, ∃ a b : V,
        a ≠ b ∧ G.neighborFinset v = {a, b} ∧ E a = E b := by
      intro v
      have hc : (G.neighborFinset v).card = 2 := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v
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
      calc
        (x : V → ZMod 2) v = (x : V → ZMod 2) (rep (p v)) :=
          (congrFun (hrep (p v)) x).symm
        _ = (y : V → ZMod 2) (rep (p v)) := congrFun hxy (p v)
        _ = (y : V → ZMod 2) v := congrFun (hrep (p v)) y
    have hkdim : Module.finrank (ZMod 2) K ≤ Fintype.card Q := by
      calc
        _ ≤ Module.finrank (ZMod 2) (Q → ZMod 2) :=
          LinearMap.finrank_le_finrank_of_injective hf
        _ = Fintype.card Q := Module.finrank_fintype_fun_eq_card (ZMod 2)
    let weights : Finset ℕ := {Fintype.card V + 1} ∪
      ((Finset.univ : Finset (V → ZMod 2)).filter
        (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
    have hw : weights.Nonempty := by simp [weights]
    let d : ℕ := weights.min' hw
    have hbound (q : Q) :
        d ≤ ((Finset.univ : Finset V).filter (fun v => p v = q)).card := by
      let c : V → ZMod 2 := fun v => if p v = q then 1 else 0
      have hp : p (rep q) = q := Subtype.ext (hrep q)
      have hc0 : c ≠ 0 := by
        intro hc
        have hh := congrFun hc (rep q)
        simpa [c, hp] using hh
      have hker : (G.adjMatrix (ZMod 2)).mulVecLin c = 0 := by
        apply funext
        intro v
        rcases hpairs v with ⟨a, b, hab, hs, he⟩
        have hpab : p a = p b := Subtype.ext he
        have hcab : c a = c b := by
          dsimp only [c]
          rw [hpab]
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
      simpa [hammingNorm, c] using hd
    have hsum :
        (∑ q : Q, ((Finset.univ : Finset V).filter (fun v => p v = q)).card) =
          Fintype.card V := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset V) (Finset.univ : Finset Q) p
    have hnat : Module.finrank (ZMod 2) K * d ≤ Fintype.card V := by
      calc
        _ ≤ Fintype.card Q * d := Nat.mul_le_mul_right d hkdim
        _ = ∑ q : Q, d := by simp [Nat.nsmul_eq_mul]
        _ ≤ ∑ q : Q, ((Finset.univ : Finset V).filter (fun v => p v = q)).card :=
          Finset.sum_le_sum (fun q _ => hbound q)
        _ = Fintype.card V := hsum
    change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) ≤ (Fintype.card V : ℝ)
    exact_mod_cast hnat

theorem model_b25136df53f5aa6f52de {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) = (Fintype.card V : ℝ) := by
  classical
    have hupper := model_d5876bce3d63a657ae5c G h_guard.2
    letI : Nonempty V := h_guard.1.nonempty
    rcases h_guard.2.1 with ⟨r, hr⟩
    have hclose : |(r : ℝ) - 2| ≤ (1 / 10000000 : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.2.1
    have hrlo : (1 : ℝ) < (r : ℝ) := by
      have ha := (abs_le.mp hclose).1
      linarith
    have hrhi : (r : ℝ) < (3 : ℝ) := by
      have ha := (abs_le.mp hclose).2
      linarith
    have hrlo_nat : 1 < r := by exact_mod_cast hrlo
    have hrhi_nat : r < 3 := by exact_mod_cast hrhi
    have hr2 : r = 2 := by omega
    have hdeg (w : V) : G.degree w = 2 := (hr.degree_eq w).trans hr2
    obtain ⟨u⟩ := h_guard.1.nonempty
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp
      (by rw [hdeg u]; norm_num)
    let K : Submodule (ZMod 2) (V → ZMod 2) :=
      LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
    letI : Fintype K := Fintype.ofFinite K
    let E : V → (K → ZMod 2) := fun w x => (x : V → ZMod 2) w
    let Q := {q : K → ZMod 2 // ∃ w : V, E w = q}
    letI : Fintype Q := Fintype.ofFinite Q
    let p : V → Q := fun w => ⟨E w, ⟨w, rfl⟩⟩
    let rep : Q → V := fun q => Classical.choose q.property
    have hrep (q : Q) : E (rep q) = q.val :=
      Classical.choose_spec q.property
    have hp (q : Q) : p (rep q) = q := Subtype.ext (hrep q)
    have hpairs : ∀ w : V, ∃ a b : V,
        a ≠ b ∧ G.neighborFinset w = {a, b} ∧ E a = E b := by
      intro w
      have hc : (G.neighborFinset w).card = 2 := by
        simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg w
      rcases Finset.card_eq_two.mp hc with ⟨a, b, hab, hs⟩
      refine ⟨a, b, hab, hs, ?_⟩
      funext x
      change (x : V → ZMod 2) a = (x : V → ZMod 2) b
      have hx : (G.adjMatrix (ZMod 2)).mulVecLin (x : V → ZMod 2) = 0 :=
        x.property
      have hsum : (x : V → ZMod 2) a + (x : V → ZMod 2) b = 0 := by
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_pair hab, Pi.zero_apply] using congrFun hx w
      simpa only [ZMod.neg_eq_self_mod_two] using
        (eq_neg_iff_add_eq_zero.mpr hsum)
    have hcommon (w a b : V) (hwa : G.Adj w a) (hwb : G.Adj w b) :
        p a = p b := by
      rcases hpairs w with ⟨c, e, hce, hs, he⟩
      have ha : a ∈ G.neighborFinset w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hwa
      have hb : b ∈ G.neighborFinset w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hwb
      simp only [hs, Finset.mem_insert, Finset.mem_singleton] at ha hb
      have hpc : p c = p e := Subtype.ext he
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hpc
      · exact hpc.symm
      · rfl
    let P : V → Prop := fun w =>
      (p w = p u ∧ ∀ z : V, G.Adj w z → p z = p v) ∨
        (p w = p v ∧ ∀ z : V, G.Adj w z → p z = p u)
    have hstep (a b : V) (hab : G.Adj a b) : P a → P b := by
      intro ha
      rcases ha with ⟨ha, hna⟩ | ⟨ha, hna⟩
      · right
        refine ⟨hna b hab, ?_⟩
        intro c hbc
        exact (hcommon b c a hbc hab.symm).trans ha
      · left
        refine ⟨hna b hab, ?_⟩
        intro c hbc
        exact (hcommon b c a hbc hab.symm).trans ha
    have hwalk : ∀ {a b : V}, G.Walk a b → P a → P b := by
      intro a b walk
      induction walk with
      | nil => exact fun h => h
      | cons hab walk ih => exact fun h => ih (hstep _ _ hab h)
    have hlabels (w : V) : P w := by
      obtain ⟨walk⟩ := h_guard.1 u w
      exact hwalk walk (Or.inl ⟨rfl, fun z huz => hcommon u z v huz huv⟩)
    have hclasses (q : Q) : q = p u ∨ q = p v := by
      rcases hlabels (rep q) with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl ((hp q).symm.trans h)
      · exact Or.inr ((hp q).symm.trans h)
    let fiber : Q → Finset V := fun q =>
      (Finset.univ : Finset V).filter (fun w => p w = q)
    have hbalance : (fiber (p u)).card = (fiber (p v)).card := by
      by_cases heq : p u = p v
      · rw [heq]
      · have hbip : G.IsBipartiteWith
            (↑(fiber (p u)) : Set V) (↑(fiber (p v)) : Set V) := by
          refine ⟨?_, ?_⟩
          · apply Set.disjoint_left.mpr
            intro w hwu hwv
            have hwu' : p w = p u := (Finset.mem_filter.mp hwu).2
            have hwv' : p w = p v := (Finset.mem_filter.mp hwv).2
            exact heq (hwu'.symm.trans hwv')
          · intro a b hab
            rcases hlabels a with ⟨ha, hna⟩ | ⟨ha, hna⟩
            · left
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hna b hab⟩⟩
            · right
              exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hna b hab⟩⟩
        have hcount : (fiber (p u)).card * 2 = (fiber (p v)).card * 2 := by
          simpa only [hdeg, Finset.sum_const, Nat.nsmul_eq_mul] using
            (SimpleGraph.isBipartiteWith_sum_degrees_eq
              (s := fiber (p u)) (t := fiber (p v)) hbip)
        omega
    have huniform (q z : Q) : (fiber q).card = (fiber z).card := by
      rcases hclasses q with hq | hq <;> rcases hclasses z with hz | hz
      · rw [hq, hz]
      · simpa only [hq, hz] using hbalance
      · simpa only [hq, hz] using hbalance.symm
      · rw [hq, hz]
    have hker (y : Q → ZMod 2) :
        (G.adjMatrix (ZMod 2)).mulVecLin (fun w => y (p w)) = 0 := by
      apply funext
      intro w
      rcases hpairs w with ⟨a, b, hab, hs, he⟩
      have hpab : p a = p b := Subtype.ext he
      have hz : y (p b) + y (p b) = 0 := by
        simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (y (p b))
      simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
        hs, Finset.sum_pair hab, hpab, Pi.zero_apply] using hz
    let g : (Q → ZMod 2) →ₗ[ZMod 2] K :=
      { toFun := fun y => ⟨fun w => y (p w), hker y⟩
        map_add' := by
          intro y z
          apply Subtype.ext
          funext w
          rfl
        map_smul' := by
          intro a y
          apply Subtype.ext
          funext w
          rfl }
    have hg : Function.Injective g := by
      intro y z heq
      funext q
      have hh := congrArg (fun x : K => (x : V → ZMod 2) (rep q)) heq
      change y (p (rep q)) = z (p (rep q)) at hh
      simpa only [hp q] using hh
    have hkdim : Fintype.card Q ≤ Module.finrank (ZMod 2) K := by
      calc
        _ = Module.finrank (ZMod 2) (Q → ZMod 2) :=
          (Module.finrank_fintype_fun_eq_card (ZMod 2)).symm
        _ ≤ Module.finrank (ZMod 2) K :=
          LinearMap.finrank_le_finrank_of_injective hg
    have hsum : (∑ q : Q, (fiber q).card) = Fintype.card V := by
      simpa [fiber] using Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset V) (Finset.univ : Finset Q) p
    have htotal : Fintype.card Q * (fiber (p u)).card = Fintype.card V := by
      calc
        _ = ∑ _q : Q, (fiber (p u)).card := by
          simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
        _ = ∑ q : Q, (fiber q).card := by
          apply Finset.sum_congr rfl
          intro q _
          exact (huniform q (p u)).symm
        _ = Fintype.card V := hsum
    have hcard : (fiber (p u)).card ≤ Fintype.card V := by
      calc
        _ ≤ (Finset.univ : Finset V).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = Fintype.card V := Finset.card_univ
    let weights : Finset ℕ := {Fintype.card V + 1} ∪
      ((Finset.univ : Finset (V → ZMod 2)).filter
        (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm
    have hw : weights.Nonempty := by simp [weights]
    let d : ℕ := weights.min' hw
    have hmin : (fiber (p u)).card ≤ d := by
      refine Finset.le_min' weights hw ((fiber (p u)).card) ?_
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · have heq : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
        rw [heq]
        exact hcard.trans (Nat.le_succ _)
      · rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
        rcases (Finset.mem_filter.mp hx).2 with ⟨hx0, hxker⟩
        obtain ⟨w, hxn⟩ : ∃ w : V, x w ≠ 0 := by
          by_contra hn
          apply hx0
          funext w
          by_contra hxn
          exact hn ⟨w, hxn⟩
        let xc : K := ⟨x, hxker⟩
        have hsubset : fiber (p w) ⊆
            (Finset.univ : Finset V).filter (fun z => x z ≠ 0) := by
          intro z hz
          have hpzw : p z = p w := (Finset.mem_filter.mp hz).2
          have he : E z = E w := congrArg Subtype.val hpzw
          have hval : x z = x w := congrFun he xc
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hval]
          exact hxn
        calc
          _ = (fiber (p w)).card := huniform (p u) (p w)
          _ ≤ ((Finset.univ : Finset V).filter (fun z => x z ≠ 0)).card :=
            Finset.card_le_card hsubset
          _ = hammingNorm x := rfl
    have hnat : Fintype.card V ≤ Module.finrank (ZMod 2) K * d := by
      calc
        _ = Fintype.card Q * (fiber (p u)).card := htotal.symm
        _ ≤ Module.finrank (ZMod 2) K * d := Nat.mul_le_mul hkdim hmin
    have hlower : (Fintype.card V : ℝ) ≤
        (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) := by
      exact_mod_cast hnat
    change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) = (Fintype.card V : ℝ)
    exact le_antisymm hupper hlower

theorem model_8ce30216566f34c2605a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ≤ (((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) * (G.maxDegree : ℝ)) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    let t : Finset V := Finset.univ \ s
    have hcover : G.edgeFinset ⊆ t.biUnion (fun v => G.incidenceFinset v) := by
      intro e
      refine Sym2.inductionOn e ?_
      intro v w he
      have hadj : G.Adj v w := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      by_cases hv : v ∈ s
      · have hw : w ∉ s := by
          intro hw
          exact ((SimpleGraph.compl_adj G v w).mp (hs.isClique hv hw hadj.ne)).2 hadj
        refine Finset.mem_biUnion.mpr ⟨w, ?_, ?_⟩
        · simp [t, hw]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_right_iff] using hadj
      · refine Finset.mem_biUnion.mpr ⟨v, ?_, ?_⟩
        · simp [t, hv]
        · simpa only [SimpleGraph.mem_incidenceFinset,
            SimpleGraph.mk'_mem_incidenceSet_left_iff] using hadj
    have hn : G.edgeFinset.card ≤ t.card * G.maxDegree := by
      calc
        G.edgeFinset.card ≤ (t.biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ t, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ t, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ t, G.maxDegree :=
          Finset.sum_le_sum fun v _ => G.degree_le_maxDegree v
        _ = t.card * G.maxDegree := by simp
    have hcard : t.card + Gᶜ.cliqueNum = Fintype.card V := by
      simpa only [t, hs.card_eq, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    have hcard_real : (t.card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hcard
    have ht : (t.card : ℝ) = (Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ) := by
      linarith
    have hbound : (G.edgeFinset.card : ℝ) ≤ (t.card : ℝ) * (G.maxDegree : ℝ) := by
      exact_mod_cast hn
    rw [ht] at hbound
    exact hbound

theorem hull3d_max_degree_le_1_0_size_chromatic_number_0_is_bipartite_19bc4d43570a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Colorable 2)) :
    (G.maxDegree : ℝ) ≤ (G.edgeFinset.card : ℝ) := by
  have h : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le _ (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast h

theorem hull3d_size_ge_1_0_max_degree_normalized_laplacian_spectral_gap_0_is_connected_9b83028c151a {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.Connected)) :
    (G.edgeFinset.card : ℝ) ≥ (G.maxDegree : ℝ) := by
  classical
  have hn : G.maxDegree ≤ G.edgeFinset.card :=
    G.maxDegree_le_of_forall_degree_le G.edgeFinset.card
      (fun v => G.degree_le_card_edgeFinset v)
  exact_mod_cast hn

theorem model_255bb4d9cb35aa834f3d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.CliqueFree 3)) :
    (G.edgeFinset.card : ℝ) ≤ ((Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ))) := by
  classical
    obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
    have hi : G.IsIndepSet (s : Set V) := (G.isClique_compl).mp hs.isClique
    have hdeg : ∀ v : V, G.degree v ≤ Gᶜ.cliqueNum := by
      intro v
      have hn : Gᶜ.IsClique (G.neighborFinset v : Set V) := by
        rw [G.isClique_compl, G.coe_neighborFinset]
        exact G.isIndepSet_neighborSet_of_triangleFree h_guard v
      exact hn.card_le_cliqueNum
    have hcover : G.edgeFinset ⊆ (sᶜ).biUnion (fun v => G.incidenceFinset v) := by
      intro e he
      have he' : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨v, hv, hve⟩ :=
        SimpleGraph.IsIndepSet.nonempty_mem_compl_mem_edge G hi he'
      refine Finset.mem_biUnion.mpr ⟨v, Finset.mem_compl.mpr hv, ?_⟩
      exact SimpleGraph.mem_incidenceFinset.mpr ⟨he', hve⟩
    have hnat : G.edgeFinset.card ≤ (sᶜ).card * Gᶜ.cliqueNum := by
      calc
        G.edgeFinset.card ≤ ((sᶜ).biUnion (fun v => G.incidenceFinset v)).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ v ∈ sᶜ, (G.incidenceFinset v).card := Finset.card_biUnion_le
        _ = ∑ v ∈ sᶜ, G.degree v := by
          simp only [G.card_incidenceFinset_eq_degree]
        _ ≤ ∑ _v ∈ sᶜ, Gᶜ.cliqueNum := Finset.sum_le_sum (fun v _ => hdeg v)
        _ = (sᶜ).card * Gᶜ.cliqueNum := by simp
    have hc : ((sᶜ).card : ℝ) + (Gᶜ.cliqueNum : ℝ) = (Fintype.card V : ℝ) := by
      have hn := Finset.card_compl_add_card s
      rw [hs.card_eq] at hn
      exact_mod_cast hn
    calc
      (G.edgeFinset.card : ℝ) ≤ ((sᶜ).card : ℝ) * (Gᶜ.cliqueNum : ℝ) := by
        exact_mod_cast hnat
      _ = (Gᶜ.cliqueNum : ℝ) * ((Fintype.card V : ℝ) - (Gᶜ.cliqueNum : ℝ)) := by
        rw [← hc]
        ring
theorem model_0a01f6ea5c2542c96796 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) ≤ (G.edgeFinset.card : ℝ) := by
  classical
  have hmax : G.maxDegree ≤ 2 := by
    have hh : (G.maxDegree : ℝ) < 3 := by
      linarith only [h_guard.1]
    have hn : G.maxDegree < 3 := by exact_mod_cast hh
    omega
  have hmin : 1 ≤ G.minDegree := by
    have hh : (0 : ℝ) < (G.minDegree : ℝ) := by
      linarith only [h_guard.2.1]
    have hn : 0 < G.minDegree := by exact_mod_cast hh
    omega
  have hdeg (v : V) : G.degree v = 1 ∨ G.degree v = 2 := by
    have hlo := hmin.trans (G.minDegree_le_degree v)
    have hhi := (G.degree_le_maxDegree v).trans hmax
    omega
  let K : Submodule (ZMod 2) (V → ZMod 2) :=
    LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin
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
  have hbound (q : Q) : d ≤ (fiber q).card := by
    let c : V → ZMod 2 := fun v => if E v = q.val then 1 else 0
    have hc0 : c ≠ 0 := by
      intro hc
      have hh := congrFun hc (rep q)
      simpa [c, hrep q] using hh
    have hker : (G.adjMatrix (ZMod 2)).mulVecLin c = 0 := by
      funext v
      rcases hdeg v with hv | hv
      · rcases hleaf v hv with ⟨a, hs, ha⟩
        have hne : E a ≠ q.val := by
          intro hh
          exact q.property.1 (hh.symm.trans ha)
        have hca : c a = 0 := by simp [c, hne]
        simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
          hs, Finset.sum_singleton, Pi.zero_apply] using hca
      · rcases hpairs v hv with ⟨a, b, hab, hs, he⟩
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
  let s : Finset V := (Finset.univ : Finset V).filter (fun v => E v ≠ 0)
  let t : Finset V := sᶜ
  have hdisj : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint fiber := by
    intro q _ z _ hqz
    apply Finset.disjoint_left.mpr
    intro v hvq hvz
    apply hqz
    apply Subtype.ext
    have heq : E v = q.val := (Finset.mem_filter.mp hvq).2
    have hez : E v = z.val := (Finset.mem_filter.mp hvz).2
    exact heq.symm.trans hez
  have hunion : (Finset.univ : Finset Q).biUnion fiber = s := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_biUnion.mp hv with ⟨q, _, hq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
      intro hz
      have heq : E v = q.val := (Finset.mem_filter.mp hq).2
      exact q.property.1 (heq.symm.trans hz)
    · intro hv
      have hz : E v ≠ 0 := (Finset.mem_filter.mp hv).2
      let q : Q := ⟨E v, hz, ⟨v, rfl⟩⟩
      exact Finset.mem_biUnion.mpr
        ⟨q, Finset.mem_univ q, Finset.mem_filter.mpr ⟨Finset.mem_univ v, rfl⟩⟩
  have hsum : (∑ q : Q, (fiber q).card) = s.card := by
    rw [← Finset.card_biUnion hdisj, hunion]
  have hnat : Module.finrank (ZMod 2) K * d ≤ s.card := by
    calc
      _ ≤ Fintype.card Q * d := Nat.mul_le_mul_right d hkdim
      _ = ∑ _q : Q, d := by simp [Nat.nsmul_eq_mul]
      _ ≤ ∑ q : Q, (fiber q).card :=
        Finset.sum_le_sum (fun q _ => hbound q)
      _ = s.card := hsum
  have hlocal (v : V) (hv : v ∈ s) :
      2 ≤ G.degree v + (t.filter (fun w => G.Adj v w)).card := by
    rcases hdeg v with hv1 | hv2
    · rcases hleaf v hv1 with ⟨a, hs, ha⟩
      have hat : a ∈ t := by simp [t, s, ha]
      have hvan : a ∈ G.neighborFinset v := by rw [hs]; simp
      have hva : G.Adj v a := by
        simpa only [SimpleGraph.mem_neighborFinset] using hvan
      have hc : 0 < (t.filter (fun w => G.Adj v w)).card :=
        Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨hat, hva⟩⟩
      omega
    · omega
  have hcross :
      (∑ v ∈ s, (t.filter (fun w => G.Adj v w)).card) ≤
        ∑ w ∈ t, G.degree w := by
    calc
      _ = ∑ w ∈ t, (s.filter (fun v => G.Adj v w)).card := by
        simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow] using
          (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
            (s := s) (t := t) G.Adj)
      _ ≤ ∑ w ∈ t, G.degree w := by
        apply Finset.sum_le_sum
        intro w hw
        calc
          (s.filter (fun v => G.Adj v w)).card ≤ (G.neighborFinset w).card := by
            apply Finset.card_le_card
            intro v hv
            have hvw : G.Adj v w := (Finset.mem_filter.mp hv).2
            simpa only [SimpleGraph.mem_neighborFinset] using hvw.symm
          _ = G.degree w := by simp only [SimpleGraph.card_neighborFinset_eq_degree]
  have hsplit :
      (∑ v ∈ s, G.degree v) + (∑ v ∈ t, G.degree v) =
        2 * G.edgeFinset.card := by
    calc
      _ = ∑ v : V, G.degree v := by
        simpa only [t] using Finset.sum_add_sum_compl s (fun v => G.degree v)
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have htwice : 2 * s.card ≤ 2 * G.edgeFinset.card := by
    calc
      _ = ∑ _v ∈ s, 2 := by simp [Nat.nsmul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ v ∈ s, (G.degree v + (t.filter (fun w => G.Adj v w)).card) :=
        Finset.sum_le_sum (fun v hv => hlocal v hv)
      _ = (∑ v ∈ s, G.degree v) +
          (∑ v ∈ s, (t.filter (fun w => G.Adj v w)).card) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ v ∈ s, G.degree v) + (∑ v ∈ t, G.degree v) :=
        Nat.add_le_add_left hcross _
      _ = 2 * G.edgeFinset.card := hsplit
  have hsedges : s.card ≤ G.edgeFinset.card := by omega
  change (Module.finrank (ZMod 2) K : ℝ) * (d : ℝ) ≤ (G.edgeFinset.card : ℝ)
  exact_mod_cast (hnat.trans hsedges)
