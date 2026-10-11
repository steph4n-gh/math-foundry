import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic









open scoped BigOperators

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem model_498663d70c6a4882faec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ (|(G.minDegree : ℝ) - (2 : ℝ)| ≤ (1 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = ((2 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ)))) := by
  classical
  have hconn : G.Connected := h_guard.1
  letI : Nonempty V := hconn.nonempty
  have hlo : (1 : ℝ) < (G.minDegree : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).1
    linarith
  have hhi : (G.minDegree : ℝ) < (3 : ℝ) := by
    have h := (abs_le.mp h_guard.2.2).2
    linarith
  have hlo' : 1 < G.minDegree := by exact_mod_cast hlo
  have hhi' : G.minDegree < 3 := by exact_mod_cast hhi
  have hmin : G.minDegree = 2 := by omega
  obtain ⟨d, hreg⟩ := h_guard.2.1
  have hd : d = 2 := hreg.minDegree_eq.symm.trans hmin
  have hdeg (u : V) : G.degree u = 2 := (hreg.degree_eq u).trans hd
  have hnotacyc : ¬ G.IsAcyclic := by
    intro hac
    have htree : G.IsTree := ⟨hconn, hac⟩
    have hedges := htree.card_edgeFinset
    have hsum : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
      simpa [hdeg, Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges
    omega
  have hexcycle : ∃ a, ∃ p : G.Walk a a, p.IsCycle := by
    by_contra h
    apply hnotacyc
    intro a p hp
    exact h ⟨a, p, hp⟩
  obtain ⟨a, p, hp⟩ := hexcycle
  have hn : 2 < p.length := by
    have h := hp.three_le_length
    omega
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff hn).mpr ⟨a, p, hp, rfl⟩
  have hcycledeg : ∀ i : Fin p.length,
      (SimpleGraph.cycleGraph p.length).degree i = 2 := by
    have hn3 : p.length - 3 + 3 = p.length := by omega
    rw [← hn3]
    exact fun i => SimpleGraph.cycleGraph_degree_three_le
  have hns (i : Fin p.length) : Function.Surjective (f.mapNeighborSet i) := by
    have hbij : Function.Bijective (f.mapNeighborSet i) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨(f.mapNeighborSet i).injective, by
          simp only [SimpleGraph.card_neighborSet_eq_degree, hcycledeg, hdeg]⟩
    exact hbij.2
  have hclosed {i : Fin p.length} {w : V} (hw : G.Adj (f i) w) :
      ∃ j : Fin p.length, f j = w := by
    obtain ⟨j, hj⟩ := hns i ⟨w, hw⟩
    exact ⟨j.1, congrArg Subtype.val hj⟩
  have hreach {u w : V} (q : G.Walk u w) :
      (∃ i : Fin p.length, f i = u) → (∃ i : Fin p.length, f i = w) := by
    induction q with
    | nil => exact fun h => h
    | @cons u t w hut q ih =>
      rintro ⟨i, rfl⟩
      exact ih (hclosed hut)
  let i0 : Fin p.length := ⟨0, by omega⟩
  have hfs : Function.Surjective f := by
    intro w
    exact hreach (hconn (f i0) w).some ⟨i0, rfl⟩
  let e : SimpleGraph.cycleGraph p.length ≃g G :=
    { toEquiv := Equiv.ofBijective f ⟨f.injective, hfs⟩
      map_rel_iff' := by
        intro i j
        change G.Adj (f i) (f j) ↔ (SimpleGraph.cycleGraph p.length).Adj i j
        constructor
        · intro hij
          obtain ⟨k, hk⟩ := hns i ⟨f j, hij⟩
          have hval : f k.1 = f j := congrArg Subtype.val hk
          have hkval : k.1 = j := f.injective hval
          simpa only [SimpleGraph.mem_neighborSet, hkval] using k.property
        · intro hij
          exact f.toHom.map_adj hij }
  have hcard : p.length = Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.toEquiv
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker A
  have hpairs (u : V) : ∃ v w, v ≠ w ∧ G.neighborFinset u = {v, w} := by
    apply Finset.card_eq_two.mp
    exact hdeg u
  have htwo (t : ZMod 2) : t + t = 0 := by
    simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel t
  have hrows (x : K) (u : V) : (∑ w ∈ G.neighborFinset u, x.1 w) = 0 := by
    have hx : A x.1 = 0 := LinearMap.mem_ker.mp x.property
    have h := congrFun hx u
    simpa only [A, Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
      Pi.zero_apply] using h
  have hneighbors (x : K) {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) :
      x.1 v = x.1 w := by
    obtain ⟨s, t, hst, hs⟩ := hpairs u
    have hsum : x.1 s + x.1 t = 0 := by
      simpa [hs, hst] using hrows x u
    have heq : x.1 s = x.1 t := by
      have h : x.1 s = -x.1 t := eq_neg_of_add_eq_zero_left hsum
      simpa only [ZMod.neg_eq_self_mod_two] using h
    have hv : v = s ∨ v = t := by
      simpa [hs] using ((G.mem_neighborFinset u v).mpr huv)
    have hw : w = s ∨ w = t := by
      simpa [hs] using ((G.mem_neighborFinset u w).mpr huw)
    rcases hv with rfl | rfl
    · rcases hw with rfl | rfl
      · rfl
      · exact heq
    · rcases hw with rfl | rfl
      · exact heq.symm
      · rfl
  have hprop (x : K) {u w : V} (q : G.Walk u w) :
      ∀ z, G.Adj z u → x.1 z = 0 → x.1 u = 0 → x.1 w = 0 := by
    induction q with
    | nil =>
      intro z hz hz0 hu0
      exact hu0
    | @cons u t w hut q ih =>
      intro z hzu hz0 hu0
      exact ih u hut hu0 ((hneighbors x hzu.symm hut).symm.trans hz0)
  have hzero (x : K) {u v : V} (huv : G.Adj u v)
      (hu : x.1 u = 0) (hv : x.1 v = 0) : x = 0 := by
    apply Subtype.ext
    funext w
    exact hprop x (hconn v w).some u huv hu hv
  obtain ⟨b, b', hbb', hnb⟩ := hpairs a
  have hab : G.Adj a b := by
    apply (G.mem_neighborFinset a b).mp
    simp [hnb]
  let C0 : (ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := LinearMap.const
  have hC0 (t : ZMod 2) : C0 t ∈ K := by
    rw [LinearMap.mem_ker]
    funext u
    change Matrix.mulVec (G.adjMatrix (ZMod 2)) (C0 t) u = 0
    obtain ⟨v, w, hvw, hs⟩ := hpairs u
    rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
    change t + t = 0
    exact htwo t
  let C : (ZMod 2) →ₗ[ZMod 2] K := C0.codRestrict K hC0
  have hCi : Function.Injective C := by
    intro x y hxy
    have h := congrArg (fun z : K => z.1 a) hxy
    change x = y at h
    exact h
  have hge1 : 1 ≤ Module.finrank (ZMod 2) K := by
    simpa only [CommSemiring.finrank_self] using
      LinearMap.finrank_le_finrank_of_injective hCi
  let T : K →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi fun i =>
      if i = 0 then (LinearMap.proj a).domRestrict K
      else (LinearMap.proj b).domRestrict K
  have hTi : Function.Injective T := by
    intro x y hxy
    have h0 : x.1 a = y.1 a := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (0 : Fin 2)
    have h1 : x.1 b = y.1 b := by
      simpa [T, LinearMap.proj_apply] using congrFun hxy (1 : Fin 2)
    apply sub_eq_zero.mp
    apply hzero (x - y) hab
    · change x.1 a - y.1 a = 0
      exact sub_eq_zero.mpr h0
    · change x.1 b - y.1 b = 0
      exact sub_eq_zero.mpr h1
  have hle2 : Module.finrank (ZMod 2) K ≤ 2 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      LinearMap.finrank_le_finrank_of_injective hTi
  change (Module.finrank (ZMod 2) K : ℝ) = _
  rw [← hcard]
  by_cases hEven : Even p.length
  · have hcolor : G.Colorable 2 :=
      (SimpleGraph.IsBipartite.cycleGraph_of_even hEven).of_hom e.symm.toHom
    obtain ⟨c⟩ := hcolor
    have hcsurj : Function.Surjective c := by
      intro i
      have hne : (c a).val ≠ (c b).val := by
        intro h
        exact c.valid hab (Fin.ext h)
      have ha2 := (c a).isLt
      have hb2 := (c b).isLt
      have hi2 := i.isLt
      have hi : i = c a ∨ i = c b := by
        by_cases hia : i = c a
        · exact Or.inl hia
        · right
          apply Fin.ext
          have hia' : i.val ≠ (c a).val := by
            intro h
            exact hia (Fin.ext h)
          omega
      rcases hi with hi | hi
      · exact ⟨a, hi.symm⟩
      · exact ⟨b, hi.symm⟩
    have hcolors {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) : c v = c w := by
      apply Fin.ext
      have hv : (c u).val ≠ (c v).val := by
        intro h
        exact c.valid huv (Fin.ext h)
      have hw : (c u).val ≠ (c w).val := by
        intro h
        exact c.valid huw (Fin.ext h)
      have hu2 := (c u).isLt
      have hv2 := (c v).isLt
      have hw2 := (c w).isLt
      omega
    let D0 : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
      LinearMap.pi fun u => LinearMap.proj (c u)
    have hD0 (t : Fin 2 → ZMod 2) : D0 t ∈ K := by
      rw [LinearMap.mem_ker]
      funext u
      change Matrix.mulVec (G.adjMatrix (ZMod 2)) (D0 t) u = 0
      obtain ⟨v, w, hvw, hs⟩ := hpairs u
      have huv : G.Adj u v := by
        apply (G.mem_neighborFinset u v).mp
        simp [hs]
      have huw : G.Adj u w := by
        apply (G.mem_neighborFinset u w).mp
        simp [hs]
      have heq := hcolors huv huw
      rw [SimpleGraph.adjMatrix_mulVec_apply, hs, Finset.sum_pair hvw]
      change t (c v) + t (c w) = 0
      rw [heq]
      exact htwo _
    let D : (Fin 2 → ZMod 2) →ₗ[ZMod 2] K := D0.codRestrict K hD0
    have hDi : Function.Injective D := by
      intro x y hxy
      funext i
      obtain ⟨u, hu⟩ := hcsurj i
      have h := congrArg (fun z : K => z.1 u) hxy
      change x (c u) = y (c u) at h
      simpa only [hu] using h
    have hge2 : 2 ≤ Module.finrank (ZMod 2) K := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        LinearMap.finrank_le_finrank_of_injective hDi
    have hdim : Module.finrank (ZMod 2) K = 2 := le_antisymm hle2 hge2
    obtain ⟨k, hk⟩ := hEven
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      rw [hquot, Int.floor_natCast]
    rw [hdim, hfloor, hk]
    push_cast <;> ring
  · have hOdd : Odd p.length := Nat.not_even_iff_odd.mp hEven
    have hnotcolor : ¬ G.Colorable 2 := by
      intro hc
      have hc' := hc.of_hom f.toHom
      have hchrom := SimpleGraph.chromaticNumber_cycleGraph_of_odd p.length
        (by omega) hOdd
      have hle := hc'.chromaticNumber_le
      rw [hchrom] at hle
      norm_num at hle
    have hsame (x : K) : x.1 a = x.1 b := by
      by_contra hx
      let c : G.Coloring (ZMod 2) :=
        SimpleGraph.Coloring.mk x.1 (by
          intro u w huw heq
          have hxconst : x = C (x.1 u) := by
            apply sub_eq_zero.mp
            apply hzero (x - C (x.1 u)) huw
            · change x.1 u - x.1 u = 0
              exact sub_self _
            · change x.1 w - x.1 u = 0
              exact sub_eq_zero.mpr heq.symm
          apply hx
          rw [hxconst]
          rfl)
      exact hnotcolor (by simpa only [ZMod.card] using c.colorable)
    let S : K →ₗ[ZMod 2] (ZMod 2) := (LinearMap.proj a).domRestrict K
    have hSi : Function.Injective S := by
      intro x y hxy
      have h : x.1 a = y.1 a := by
        simpa [S, LinearMap.proj_apply] using hxy
      have hz : (x - y).1 a = 0 := by
        change x.1 a - y.1 a = 0
        exact sub_eq_zero.mpr h
      apply sub_eq_zero.mp
      exact hzero (x - y) hab hz ((hsame (x - y)).symm.trans hz)
    have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
      simpa only [CommSemiring.finrank_self] using
        LinearMap.finrank_le_finrank_of_injective hSi
    have hdim : Module.finrank (ZMod 2) K = 1 := le_antisymm hle1 hge1
    obtain ⟨k, hk⟩ := hOdd
    have hquot : (p.length : ℝ) / 2 = (k : ℝ) + (1 / 2 : ℝ) := by
      rw [hk]
      push_cast
      ring
    have hfloor : Int.floor ((p.length : ℝ) / 2) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      rw [hquot]
      constructor <;> push_cast <;> linarith
    rw [hdim, hfloor, hk]
    push_cast <;> ring

theorem model_86d5f85f179c31163952 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := (Gᶜ).exists_isNClique_cliqueNum
  let A := (G.adjMatrix (ZMod 2)).mulVecLin
  let E : (s → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x v => if hv : v ∈ s then x ⟨v, hv⟩ else 0
      map_add' := by
        intro x y
        funext v
        by_cases hv : v ∈ s <;> simp [hv]
      map_smul' := by
        intro c x
        funext v
        by_cases hv : v ∈ s <;> simp [hv] }
  have hE : Function.Injective E := by
    intro x y hxy
    funext v
    have h := congrFun hxy (v : V)
    simpa [E, v.property] using h
  have hzero (x : s → ZMod 2) (v : V) (hv : v ∈ s) :
      A (E x) v = 0 := by
    change (∑ w : V, G.adjMatrix (ZMod 2) v w * E x w) = 0
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hws : w ∈ s
    · have hnot : ¬ G.Adj v w := by
        intro hadj
        exact ((SimpleGraph.compl_adj G v w).mp
          (hs.isClique hv hws hadj.ne)).2 hadj
      simp [SimpleGraph.adjMatrix_apply, hnot]
    · simp [E, hws]
  let f : (s → ZMod 2) →ₗ[ZMod 2] (↥(sᶜ) → ZMod 2) :=
    { toFun := fun x v => A (E x) (v : V)
      map_add' := by
        intro x y
        funext v
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext v
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  have hker : ∀ x : LinearMap.ker f,
      E (x : s → ZMod 2) ∈ LinearMap.ker A := by
    intro x
    rw [LinearMap.mem_ker]
    funext v
    change A (E (x : s → ZMod 2)) v = 0
    by_cases hv : v ∈ s
    · exact hzero (x : s → ZMod 2) v hv
    · have hx := congrFun (LinearMap.mem_ker.mp x.property)
        (⟨v, Finset.mem_compl.mpr hv⟩ : ↥(sᶜ))
      exact hx
  let e : LinearMap.ker f →ₗ[ZMod 2] LinearMap.ker A :=
    (E.domRestrict (LinearMap.ker f)).codRestrict (LinearMap.ker A) hker
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply hE
    exact congrArg (fun z : LinearMap.ker A => (z : V → ZMod 2)) hxy
  have hk : Module.finrank (ZMod 2) (LinearMap.ker f) ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hr : Module.finrank (ZMod 2) (LinearMap.range f) ≤ sᶜ.card := by
    calc
      _ ≤ Module.finrank (ZMod 2) (↥(sᶜ) → ZMod 2) := Submodule.finrank_le _
      _ = sᶜ.card := by
        simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) +
      Module.finrank (ZMod 2) (LinearMap.ker f) = s.card := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker f
  have hcards : s.card + sᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hsize : s.card = Gᶜ.cliqueNum := hs.card_eq
  have hnat : 2 * Gᶜ.cliqueNum ≤
      Module.finrank (ZMod 2) (LinearMap.ker A) + Fintype.card V := by
    omega
  have hreal : (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) ≤
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) + (Fintype.card V : ℝ) := by
    exact_mod_cast hnat
  change (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) ≥
    (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) - (Fintype.card V : ℝ)
  linarith

theorem model_6c69a9fac94e8d24072f {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((2 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ))) + (max (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) (((2 : ℝ) * (G.minDegree : ℝ)) - (2 : ℝ)))) ≤ (Fintype.card V : ℝ) := by
  let d := G.minDegree
  have hd : 2 ≤ d := by
    by_contra h
    have hn : G.minDegree ≤ 1 := by
      change d ≤ 1
      omega
    have hr : (G.minDegree : ℝ) ≤ 1 := by exact_mod_cast hn
    linarith [h_guard.2.2.1]
  haveI : Nonempty V := by
    rcases isEmpty_or_nonempty V with h | h
    · letI : IsEmpty V := h
      have hz : d = 0 := by
        change G.minDegree = 0
        simp
      omega
    · exact h
  obtain ⟨C⟩ := h_guard.1
  have htwo : ∀ c : Fin 2, c = 0 ∨ c = 1 := by
    intro c
    fin_cases c <;> simp
  have hcolor : ∀ a b c : Fin 2, a ≠ b → a ≠ c → b = c := by
    intro a b c hab hac
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hac' : a.val ≠ c.val := fun h => hac (Fin.ext h)
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    apply Fin.ext
    omega
  have hsame : ∀ {v w u : V}, G.Adj v w → G.Adj v u → C w = C u := by
    intro v w u hvw hvu
    exact hcolor _ _ _ (C.valid hvw) (C.valid hvu)
  let Stop : Finset V → Prop := fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w)
  let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter Stop).image Finset.card
  have hW : weights.Nonempty := by simp [weights]
  let s := weights.min' hW
  let k := s - 1
  have hs : 1 ≤ s := by
    change 1 ≤ weights.min' hW
    refine Finset.le_min' weights hW 1 ?_
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have he : a = Fintype.card V + 1 := Finset.mem_singleton.mp ha
      omega
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp ha
      have hStop : Stop S := (Finset.mem_filter.mp hS).2
      exact Finset.card_pos.mpr hStop.1
  have hk : k + 1 = s := by
    change s - 1 + 1 = s
    omega
  have hstop : ∀ S : Finset V, Stop S → s ≤ S.card := by
    intro S hS
    change weights.min' hW ≤ S.card
    apply Finset.min'_le
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩, rfl⟩)
  have hsmall : ∀ S : Finset V, S.Nonempty → S.card ≤ k → ∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w := by
    intro S hne hcard
    by_contra h
    have hh := hstop S ⟨hne, h⟩
    omega
  let A : Fin 2 → Finset V := fun c => Finset.univ.filter (fun v => C v = c)
  have hmem : ∀ (c : Fin 2) (v : V), v ∈ A c ↔ C v = c := by
    intro c v
    simp [A]
  have hdisj : Disjoint (A 0) (A 1) := by
    refine Finset.disjoint_left.mpr ?_
    intro v h0 h1
    have he : (0 : Fin 2) = 1 := ((hmem 0 v).mp h0).symm.trans ((hmem 1 v).mp h1)
    exact (by decide : (0 : Fin 2) ≠ 1) he
  have hcover : A 0 ∪ A 1 = Finset.univ := by
    ext v
    simp only [Finset.mem_union, hmem, Finset.mem_univ, iff_true]
    exact htwo (C v)
  have hpart : (A 0).card + (A 1).card = Fintype.card V := by
    calc
      (A 0).card + (A 1).card = (A 0 ∪ A 1).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = Fintype.card V := by rw [hcover, Finset.card_univ]
  have hbig : ∀ c : Fin 2, d ≤ (A c).card := by
    intro c
    obtain ⟨v⟩ := ‹Nonempty V›
    have hv : 0 < G.degree v := by
      have hh := G.minDegree_le_degree v
      change d ≤ G.degree v at hh
      omega
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
    have hex : ∃ z : V, C z ≠ c := by
      by_cases hc : C v = c
      · refine ⟨w, ?_⟩
        intro h
        exact C.valid hw (hc.trans h.symm)
      · exact ⟨v, hc⟩
    obtain ⟨z, hz⟩ := hex
    calc
      d ≤ G.degree z := G.minDegree_le_degree z
      _ = (G.neighborFinset z).card := (G.card_neighborFinset_eq_degree z).symm
      _ ≤ (A c).card := Finset.card_le_card (by
        intro u hu
        exact (hmem c u).mpr (hcolor _ _ _ (C.valid ((G.mem_neighborFinset z u).mp hu)) hz))
  have hbound : ∀ c : Fin 2, k + (d - 1) ≤ (A c).card := by
    intro c
    obtain ⟨D, hD, hDc⟩ := Finset.exists_subset_card_eq (show d - 2 ≤ (A c).card by
      have hh := hbig c
      omega)
    let S : Finset V := A c \ D
    have hSc : S.card = (A c).card - (d - 2) := by
      change (A c \ D).card = (A c).card - (d - 2)
      rw [Finset.card_sdiff_of_subset hD, hDc]
    have hSne : S.Nonempty := Finset.card_pos.mp (by
      have hh := hbig c
      omega)
    have hStop : Stop S := by
      refine ⟨hSne, ?_⟩
      rintro ⟨v, w, hw, hvw, huniq⟩
      have hwc : C w = c := (hmem c w).mp (Finset.mem_sdiff.mp hw).1
      have hsub : G.neighborFinset v ⊆ insert w D := by
        intro u hu
        have hvu := (G.mem_neighborFinset v u).mp hu
        have huc : C u = c := (hsame hvw hvu).symm.trans hwc
        by_cases huD : u ∈ D
        · exact Finset.mem_insert_of_mem huD
        · have huS : u ∈ S := Finset.mem_sdiff.mpr ⟨(hmem c u).mpr huc, huD⟩
          have hue : u = w := huniq u huS hvu
          simp [hue]
      have hcard : G.degree v ≤ D.card + 1 := by
        rw [← G.card_neighborFinset_eq_degree v]
        exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      have hh := G.minDegree_le_degree v
      change d ≤ G.degree v at hh
      omega
    have hle := hstop S hStop
    have hh := hbig c
    omega
  have hdegreeNat : 2 * k + 2 * (d - 1) ≤ Fintype.card V := by
    have h0 := hbound 0
    have h1 := hbound 1
    omega
  have hdegree : (2 : ℝ) * (k : ℝ) + (2 * (d : ℝ) - 2) ≤ (Fintype.card V : ℝ) := by
    have hr : (2 : ℝ) * (k : ℝ) + 2 * ((d - 1 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hdegreeNat
    rw [Nat.cast_sub (by omega : 1 ≤ d)] at hr
    norm_num at hr
    linarith
  obtain ⟨T0, hT0, hT0c⟩ := Finset.exists_subset_card_eq (show k ≤ (A 0).card by
    have hh := hbound 0
    omega)
  obtain ⟨T1, hT1, hT1c⟩ := Finset.exists_subset_card_eq (show k ≤ (A 1).card by
    have hh := hbound 1
    omega)
  let T := T0 ∪ T1
  have hTdisj : Disjoint T0 T1 := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv0 hv1
    exact (Finset.disjoint_left.mp hdisj) (hT0 hv0) (hT1 hv1)
  have hTc : T.card = 2 * k := by
    change (T0 ∪ T1).card = 2 * k
    rw [Finset.card_union_of_disjoint hTdisj, hT0c, hT1c]
    omega
  have hTcolor0 : ∀ v : V, v ∈ T0 → C v = 0 := fun v hv => (hmem 0 v).mp (hT0 hv)
  have hTcolor1 : ∀ v : V, v ∈ T1 → C v = 1 := fun v hv => (hmem 1 v).mp (hT1 hv)
  have hcap : ∀ c : Fin 2, (T.filter (fun v => C v = c)).card ≤ k := by
    intro c
    rcases htwo c with rfl | rfl
    · have hsub : T.filter (fun v => C v = 0) ⊆ T0 := by
        intro v hv
        obtain ⟨hvT, hc⟩ := Finset.mem_filter.mp hv
        rcases Finset.mem_union.mp hvT with h | h
        · exact h
        · have he : (0 : Fin 2) = 1 := hc.symm.trans (hTcolor1 v h)
          exact ((by decide : (0 : Fin 2) ≠ 1) he).elim
      exact (Finset.card_le_card hsub).trans_eq hT0c
    · have hsub : T.filter (fun v => C v = 1) ⊆ T1 := by
        intro v hv
        obtain ⟨hvT, hc⟩ := Finset.mem_filter.mp hv
        rcases Finset.mem_union.mp hvT with h | h
        · have he : (1 : Fin 2) = 0 := hc.symm.trans (hTcolor0 v h)
          exact ((by decide : (1 : Fin 2) ≠ 0) he).elim
        · exact h
      exact (Finset.card_le_card hsub).trans_eq hT1c
  let L := (G.adjMatrix (ZMod 2)).mulVecLin
  let K := LinearMap.ker L
  have hzero : ∀ x : K, (∀ v : V, v ∉ T → x.1 v = 0) → x.1 = 0 := by
    intro x hx
    by_contra hneq
    have hex : ∃ w : V, x.1 w ≠ 0 := by
      by_contra h
      apply hneq
      funext w
      have hh : ¬ x.1 w ≠ 0 := fun hw => h ⟨w, hw⟩
      exact not_not.mp hh
    obtain ⟨w, hw⟩ := hex
    let S : Finset V := Finset.univ.filter (fun u => x.1 u ≠ 0 ∧ C u = C w)
    have hSne : S.Nonempty := ⟨w, by simp [S, hw]⟩
    have hScard : S.card ≤ k := by
      calc
        S.card ≤ (T.filter (fun u => C u = C w)).card := Finset.card_le_card (by
          intro u hu
          have hup : x.1 u ≠ 0 ∧ C u = C w := (Finset.mem_filter.mp hu).2
          refine Finset.mem_filter.mpr ⟨?_, hup.2⟩
          by_contra hut
          exact hup.1 (hx u hut))
        _ ≤ k := hcap (C w)
    obtain ⟨v, u, hu, hvu, huniq⟩ := hsmall S hSne hScard
    have hxu : x.1 u ≠ 0 := (Finset.mem_filter.mp hu).2.1
    have huc : C u = C w := (Finset.mem_filter.mp hu).2.2
    have heval : L x.1 v = x.1 u := by
      change (∑ t : V, G.adjMatrix (ZMod 2) v t * x.1 t) = x.1 u
      rw [Finset.sum_eq_single u]
      · simp [hvu]
      · intro t ht htu
        by_cases hvt : G.Adj v t
        · have hxt : x.1 t = 0 := by
            by_contra hh
            have htc : C t = C w := (hsame hvu hvt).symm.trans huc
            have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ t, hh, htc⟩
            exact htu (huniq t htS hvt)
          simp [hxt]
        · simp [hvt]
      · intro h
        exact (h (Finset.mem_univ u)).elim
    have hz : L x.1 = 0 := LinearMap.mem_ker.mp x.2
    exact hxu (heval.symm.trans (congrFun hz v))
  let P : K →ₗ[ZMod 2] ({v : V // v ∉ T} → ZMod 2) :=
    { toFun := fun x v => x.1 v.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hP : Function.Injective P := by
    intro x y hxy
    apply Subtype.ext
    have hz : (x - y).1 = 0 := hzero (x - y) (by
      intro v hv
      have he := congrFun hxy ⟨v, hv⟩
      change x.1 v = y.1 v at he
      change x.1 v - y.1 v = 0
      exact sub_eq_zero.mpr he)
    change x.1 - y.1 = 0 at hz
    exact sub_eq_zero.mp hz
  have hdim : Module.finrank (ZMod 2) K ≤ Fintype.card V - 2 * k := by
    calc
      _ ≤ Module.finrank (ZMod 2) ({v : V // v ∉ T} → ZMod 2) := LinearMap.finrank_le_finrank_of_injective hP
      _ = Fintype.card {v : V // v ∉ T} := Module.finrank_fintype_fun_eq_card (ZMod 2)
      _ = Fintype.card V - 2 * k := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, hTc]
  have hkn : 2 * k ≤ Fintype.card V := by
    rw [← hTc]
    exact Finset.card_le_univ T
  have hnullNat : 2 * k + Module.finrank (ZMod 2) K ≤ Fintype.card V := by omega
  have hnull : (2 : ℝ) * (k : ℝ) + (Module.finrank (ZMod 2) K : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hnullNat
  change (2 : ℝ) * (k : ℝ) + max (Module.finrank (ZMod 2) K : ℝ) (2 * (d : ℝ) - 2) ≤ (Fintype.card V : ℝ)
  rcases le_total (Module.finrank (ZMod 2) K : ℝ) (2 * (d : ℝ) - 2) with h | h
  · rw [max_eq_right h]
    exact hdegree
  · rw [max_eq_left h]
    exact hnull

theorem model_5e76b721dff9cc8391a8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) * ((1 : ℝ) - (Real.exp (((-(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) K
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (4 : ℝ) * (d : ℝ) *
    (1 - Real.exp ((-(k : ℝ) / 2) * Real.log (1 + (1 : ℝ)))) ≤
      (Fintype.card V : ℝ)
  rw [show (1 + (1 : ℝ)) = 2 by norm_num]
  have hkg : (9999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.2
  have hkpos : 0 < k := by
    have hh : (0 : ℝ) < (k : ℝ) := by linarith only [hkg]
    exact_mod_cast hh
  have hkn : k ≤ Fintype.card V := by
    calc
      k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le K
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hn : 0 < Fintype.card V := lt_of_lt_of_le hkpos hkn
  letI : Nonempty V := Fintype.card_pos_iff.mp hn
  obtain ⟨r, hr⟩ := h_guard.2.1
  have hrpos : 0 < r := by
    have hh : (9999999 / 10000000 : ℝ) ≤ (r : ℝ) := by
      simpa only [hr.minDegree_eq] using h_guard.2.2.1
    have hh' : (0 : ℝ) < (r : ℝ) := by linarith only [hh]
    exact_mod_cast hh'
  obtain ⟨c⟩ := h_guard.1
  let s : Finset V := Finset.univ.filter (fun v => c v = 0)
  have hcolors : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ b ≠ 0) := by decide
  have hopp {v w : V} (hvw : G.Adj v w) : v ∈ s ↔ w ∉ s := by
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
      hcolors (c v) (c w) (c.valid hvw)
  have hB : G.IsBipartiteWith (s : Set V) ((sᶜ : Finset V) : Set V) := by
    refine ⟨?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro v hv ht
      exact (Finset.mem_compl.mp ht) hv
    · intro v w hvw
      by_cases hv : v ∈ s
      · exact Or.inl ⟨hv, Finset.mem_compl.mpr ((hopp hvw).mp hv)⟩
      · exact Or.inr ⟨Finset.mem_compl.mpr hv, (hopp hvw.symm).mpr hv⟩
  have heq : s.card * r = (sᶜ).card * r := by
    simpa only [hr.degree_eq, Finset.sum_const, Nat.nsmul_eq_mul] using
      (SimpleGraph.isBipartiteWith_sum_degrees_eq hB)
  have hcard : s.card = (sᶜ).card := mul_right_cancel₀ hrpos.ne' heq
  have htotal : s.card + (sᶜ).card = Fintype.card V :=
    Finset.card_add_card_compl s
  have hside : 2 * s.card = Fintype.card V := by omega
  have hside' : 2 * (sᶜ).card = Fintype.card V := by omega
  have hproj (x : K) :
      A (fun v => if v ∈ s then (x : V → ZMod 2) v else 0) = 0 := by
    apply funext
    intro v
    change ((G.adjMatrix (ZMod 2)).mulVecLin
      (fun w => if w ∈ s then (x : V → ZMod 2) w else 0)) v = 0
    rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
    by_cases hv : v ∈ s
    · apply Finset.sum_eq_zero
      intro w hw'
      have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
      have hw'' : w ∉ s := (hopp hadj).mp hv
      simp only [if_neg hw'']
    · calc
        _ = ∑ w ∈ G.neighborFinset v, (x : V → ZMod 2) w := by
          apply Finset.sum_congr rfl
          intro w hw'
          have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
          have hw'' : w ∈ s := (hopp hadj.symm).mpr hv
          simp only [if_pos hw'']
        _ = 0 := by
          have hx : A (x : V → ZMod 2) = 0 := x.property
          simpa only [A, Matrix.mulVecLin_apply,
            SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using congrFun hx v
  let T : K →ₗ[ZMod 2] K :=
    { toFun := fun x =>
        ⟨(fun v => if v ∈ s then (x : V → ZMod 2) v else 0), hproj x⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        funext v
        change (if v ∈ s then (x : V → ZMod 2) v + (y : V → ZMod 2) v else 0) =
          (if v ∈ s then (x : V → ZMod 2) v else 0) +
            (if v ∈ s then (y : V → ZMod 2) v else 0)
        by_cases hv : v ∈ s <;> simp [hv]
      map_smul' := by
        intro a x
        apply Subtype.ext
        funext v
        change (if v ∈ s then a • ((x : V → ZMod 2) v) else 0) =
          a • (if v ∈ s then (x : V → ZMod 2) v else 0)
        by_cases hv : v ∈ s <;> simp [hv] }
  have hchoice : ∃ (S : Finset V) (D : Submodule (ZMod 2) K),
      2 * S.card = Fintype.card V ∧
      k ≤ 2 * Module.finrank (ZMod 2) D ∧
      ∀ (x : D) (v : V), v ∉ S → (x.val : V → ZMod 2) v = 0 := by
    have hsplit : Module.finrank (ZMod 2) (LinearMap.range T) +
        Module.finrank (ZMod 2) (LinearMap.ker T) = k :=
      LinearMap.finrank_range_add_finrank_ker T
    by_cases hm : Module.finrank (ZMod 2) (LinearMap.range T) ≤
        Module.finrank (ZMod 2) (LinearMap.ker T)
    · refine ⟨sᶜ, LinearMap.ker T, hside', ?_, ?_⟩
      · omega
      · intro x v hv
        have hv' : v ∈ s := by simpa using hv
        have hh : T x.val = 0 := LinearMap.mem_ker.mp x.property
        have hh' := congrArg (fun z : K => (z : V → ZMod 2) v) hh
        change (if v ∈ s then (x.val : V → ZMod 2) v else 0) = 0 at hh'
        simpa only [if_pos hv'] using hh'
    · refine ⟨s, LinearMap.range T, hside, ?_, ?_⟩
      · omega
      · intro x v hv
        obtain ⟨y, hy⟩ := x.property
        have hh := congrArg (fun z : K => (z : V → ZMod 2) v) hy
        change (if v ∈ s then (y : V → ZMod 2) v else 0) =
          (x.val : V → ZMod 2) v at hh
        simpa only [if_neg hv] using hh.symm
  obtain ⟨S, D, hS, hkD, hsupp⟩ := hchoice
  letI : Fintype D := Fintype.ofFinite D
  let e : D →ₗ[ZMod 2] (V → ZMod 2) := K.subtype.comp D.subtype
  have hd (x : D) (hx : x ≠ 0) : d ≤ hammingNorm (e x) := by
    have hxne : e x ≠ 0 := by
      intro heq'
      apply hx
      apply Subtype.ext
      apply Subtype.ext
      exact heq'
    have hxker : A (e x) = 0 := x.val.property
    have hxmem : e x ∈ (Finset.univ : Finset (V → ZMod 2)).filter
        (fun z => z ≠ 0 ∧ A z = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne, hxker⟩
    have hmem : hammingNorm (e x) ∈ weights :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e x, hxmem, rfl⟩))
    exact Finset.min'_le weights (hammingNorm (e x)) hmem
  have hbit : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
  have hcoord (v : V) :
      2 * (Finset.univ.filter (fun x : D => e x v ≠ 0)).card ≤ Fintype.card D := by
    let U : Finset D := Finset.univ.filter (fun x => e x v ≠ 0)
    let W : Finset D := Finset.univ.filter (fun x => e x v = 0)
    change 2 * U.card ≤ Fintype.card D
    by_cases hU : U.Nonempty
    · obtain ⟨a, ha⟩ := hU
      have ha1 : e a v = 1 := hbit _ (Finset.mem_filter.mp ha).2
      have hUW : U.card ≤ W.card := by
        apply Finset.card_le_card_of_injOn (fun x : D => x + a)
        · intro x hx
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hx1 : e x v = 1 := hbit _ (Finset.mem_filter.mp hx).2
          change e (x + a) v = 0
          rw [map_add, Pi.add_apply, hx1, ha1]
          decide
        · intro x hx y hy hxy
          exact add_right_cancel hxy
      have hpartition : U.card + W.card = Fintype.card D := by
        simpa [U, W] using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset D)) (fun x : D => e x v ≠ 0))
      omega
    · have hzero : U.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU)
      simp [hzero]
  have hsum : (∑ x : D, hammingNorm (e x)) =
      ∑ v : V, (Finset.univ.filter (fun x : D => e x v ≠ 0)).card := by
    simp only [hammingNorm, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hupper : 2 * (∑ x : D, hammingNorm (e x)) ≤
      S.card * Fintype.card D := by
    rw [hsum, Finset.mul_sum]
    calc
      _ ≤ ∑ v : V, if v ∈ S then Fintype.card D else 0 := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvS : v ∈ S
        · simpa only [if_pos hvS] using hcoord v
        · have hzero : Finset.univ.filter (fun x : D => e x v ≠ 0) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro x hx
            exact fun h => h (hsupp x v hvS)
          simp [hvS, hzero]
      _ = S.card * Fintype.card D := by
        rw [Finset.sum_ite]
        simp [Finset.filter_mem_eq_inter, Nat.nsmul_eq_mul]
  have hlower : (Fintype.card D - 1) * d ≤ ∑ x : D, hammingNorm (e x) := by
    calc
      _ = ∑ x ∈ (Finset.univ : Finset D).erase 0, d := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ (0 : D)), Finset.card_univ]
      _ ≤ ∑ x ∈ (Finset.univ : Finset D).erase 0, hammingNorm (e x) :=
        Finset.sum_le_sum (fun x hx => hd x ((Finset.mem_erase.mp hx).1))
      _ = ∑ x : D, hammingNorm (e x) :=
        Finset.sum_erase (Finset.univ : Finset D)
          (f := fun x : D => hammingNorm (e x)) (a := (0 : D)) (by simp)
  have hbound : 4 * (Fintype.card D - 1) * d ≤
      Fintype.card V * Fintype.card D := by
    calc
      _ = 2 * (2 * ((Fintype.card D - 1) * d)) := by ring
      _ ≤ 2 * (2 * (∑ x : D, hammingNorm (e x))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hlower)
      _ ≤ 2 * (S.card * Fintype.card D) := Nat.mul_le_mul_left 2 hupper
      _ = Fintype.card V * Fintype.card D := by rw [← mul_assoc, hS]
  have hboundR : (4 : ℝ) * ((Fintype.card D - 1 : ℕ) : ℝ) * (d : ℝ) ≤
      (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := by
    exact_mod_cast hbound
  have hm1 : 1 ≤ Fintype.card D := Fintype.card_pos
  rw [Nat.cast_sub hm1, Nat.cast_one] at hboundR
  have hmpos : (0 : ℝ) < (Fintype.card D : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have hscaled :
      (4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹)) * (Fintype.card D : ℝ) ≤
        (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := by
    calc
      _ = 4 * (d : ℝ) *
          ((1 - (Fintype.card D : ℝ)⁻¹) * (Fintype.card D : ℝ)) := by ring
      _ = 4 * ((Fintype.card D : ℝ) - 1) * (d : ℝ) := by
        rw [sub_mul, one_mul, inv_mul_cancel₀ hmpos.ne']
        ring
      _ ≤ (Fintype.card V : ℝ) * (Fintype.card D : ℝ) := hboundR
  have hsmall : 4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹) ≤
      (Fintype.card V : ℝ) := by
    by_contra! h
    exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_right h hmpos)
  letI : Module.Free (ZMod 2) D := Module.Free.of_divisionRing (ZMod 2) D
  have hm : Fintype.card D = 2 ^ Module.finrank (ZMod 2) D := by
    simpa only [ZMod.card, Fintype.card_fin] using
      (Module.card_fintype (Module.finBasis (ZMod 2) D))
  have hmreal : (Fintype.card D : ℝ) =
      (2 : ℝ) ^ Module.finrank (ZMod 2) D := by
    exact_mod_cast hm
  have hexp : Real.exp (-(Module.finrank (ZMod 2) D : ℝ) * Real.log 2) =
      (Fintype.card D : ℝ)⁻¹ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), ← hmreal]
  have hdimR : (k : ℝ) / 2 ≤ (Module.finrank (ZMod 2) D : ℝ) := by
    have hh : (k : ℝ) ≤ 2 * (Module.finrank (ZMod 2) D : ℝ) := by
      exact_mod_cast hkD
    linarith only [hh]
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexple : Real.exp (-(Module.finrank (ZMod 2) D : ℝ) * Real.log 2) ≤
      Real.exp ((-(k : ℝ) / 2) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    have hh : -(Module.finrank (ZMod 2) D : ℝ) ≤ -(k : ℝ) / 2 := by
      linarith only [hdimR]
    exact mul_le_mul_of_nonneg_right hh hlog
  rw [hexp] at hexple
  calc
    (4 : ℝ) * (d : ℝ) * (1 - Real.exp ((-(k : ℝ) / 2) * Real.log 2)) ≤
        4 * (d : ℝ) * (1 - (Fintype.card D : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hexple 1)
        (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    _ ≤ (Fintype.card V : ℝ) := hsmall

theorem model_ceb714b3b8492a9c6002 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (29999999 / 10000000 : ℝ)))) :
    (((4 : ℝ) * (let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ))) * ((1 : ℝ) - (((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ))) * (Real.exp (((-(Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ)))))))) ≤ (Fintype.card V : ℝ) := by
  classical
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    (G.adjMatrix (ZMod 2)).mulVecLin
  let C : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) C
  let n : ℕ := Fintype.card V
  let weights : Finset ℕ := {n + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hw : weights.Nonempty := by simp [weights]
  let d : ℕ := weights.min' hw
  change (4 : ℝ) * (d : ℝ) *
    (1 - ((G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ)) *
      Real.exp ((-(k : ℝ) / 2) * Real.log (1 + (1 : ℝ)))) ≤ (n : ℝ)
  let q : ℕ := G.minDegree / 2
  have hd : G.minDegree = 2 * q + G.minDegree % 2 := by
    dsimp [q]
    omega
  have hdr : (G.minDegree : ℝ) =
      2 * (q : ℝ) + ((G.minDegree % 2 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ ((G.minDegree % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrlt : ((G.minDegree % 2 : ℕ) : ℝ) < 2 := by
    exact_mod_cast (Nat.mod_lt G.minDegree (by decide : 0 < (2 : ℕ)))
  have hfloor : Int.floor ((G.minDegree : ℝ) / 2) = (q : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith only [hdr, hr0, hrlt]
  have hrem : (G.minDegree : ℝ) -
      2 * (Int.floor ((G.minDegree : ℝ) / 2) : ℝ) =
      ((G.minDegree % 2 : ℕ) : ℝ) := by
    rw [hfloor]
    push_cast
    linarith only [hdr]
  rw [hrem]
  rcases Nat.mod_two_eq_zero_or_one G.minDegree with he | ho
  · simp only [he, Nat.cast_zero, zero_mul, sub_zero, mul_one]
    have hkreal : (29999999 / 10000000 : ℝ) ≤ (k : ℝ) := h_guard.2.2.2
    have hk : 3 ≤ k := by
      by_contra h
      have hle : (k : ℝ) ≤ 2 := by
        exact_mod_cast (show k ≤ 2 by omega)
      linarith only [hkreal, hle]
    have hkn : k ≤ n := by
      calc
        k ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le C
        _ = n := Module.finrank_fintype_fun_eq_card (ZMod 2)
    have hn : 0 < Fintype.card V := by
      change 0 < n
      omega
    letI : Nonempty V := Fintype.card_pos_iff.mp hn
    obtain ⟨r, hr⟩ := h_guard.2.1
    have hrpos : 0 < r := by
      have hg : (19999999 / 10000000 : ℝ) ≤ (r : ℝ) := by
        simpa only [hr.minDegree_eq] using h_guard.2.2.1
      have hg' : (0 : ℝ) < (r : ℝ) := by linarith only [hg]
      exact_mod_cast hg'
    have hdeg : ∀ v, G.degree v = G.minDegree :=
      fun v => (hr v).trans hr.minDegree_eq.symm
    have hz : (G.minDegree : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr he)
    have hone : A (1 : V → ZMod 2) = 0 := by
      ext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2))
        (Function.const V (1 : ZMod 2))) v = 0
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hdeg v, hz, mul_one]
    obtain ⟨c⟩ := h_guard.1
    let s : Finset V := Finset.univ.filter (fun v => c v = 0)
    have hcolors : ∀ a b : Fin 2, a ≠ b → (a = 0 ↔ b ≠ 0) := by decide
    have hopp {v w : V} (hvw : G.Adj v w) : v ∈ s ↔ w ∉ s := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
        hcolors (c v) (c w) (c.valid hvw)
    have hB : G.IsBipartiteWith (s : Set V) ((sᶜ : Finset V) : Set V) := by
      refine ⟨?_, ?_⟩
      · apply Set.disjoint_left.mpr
        intro v hv ht
        exact (Finset.mem_compl.mp ht) hv
      · intro v w hvw
        by_cases hv : v ∈ s
        · exact Or.inl ⟨hv, Finset.mem_compl.mpr ((hopp hvw).mp hv)⟩
        · exact Or.inr ⟨Finset.mem_compl.mpr hv, (hopp hvw.symm).mpr hv⟩
    have heq : s.card * r = (sᶜ).card * r := by
      simpa only [hr.degree_eq, Finset.sum_const, Nat.nsmul_eq_mul] using
        (SimpleGraph.isBipartiteWith_sum_degrees_eq hB)
    have hcard : s.card = (sᶜ).card := mul_right_cancel₀ hrpos.ne' heq
    have htotal : s.card + (sᶜ).card = n := Finset.card_add_card_compl s
    have hside : 2 * s.card = n := by omega
    have hside' : 2 * (sᶜ).card = n := by omega
    have hoppc {v w : V} (hvw : G.Adj v w) : v ∈ sᶜ ↔ w ∉ sᶜ := by
      simpa only [Finset.mem_compl, not_not] using (not_congr (hopp hvw))
    have hproj (S : Finset V)
        (hSopp : ∀ {v w : V}, G.Adj v w → (v ∈ S ↔ w ∉ S))
        (z : V → ZMod 2) (hzA : A z = 0) :
        A (fun v => if v ∈ S then z v else 0) = 0 := by
      funext v
      change ((G.adjMatrix (ZMod 2)).mulVecLin
        (fun w => if w ∈ S then z w else 0)) v = 0
      rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
      by_cases hv : v ∈ S
      · apply Finset.sum_eq_zero
        intro w hw'
        have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
        have hw'' : w ∉ S := (hSopp hadj).mp hv
        simp only [if_neg hw'']
      · calc
          _ = ∑ w ∈ G.neighborFinset v, z w := by
            apply Finset.sum_congr rfl
            intro w hw'
            have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw'
            have hw'' : w ∈ S := (hSopp hadj.symm).mpr hv
            simp only [if_pos hw'']
          _ = 0 := by
            simpa only [A, Matrix.mulVecLin_apply,
              SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply] using congrFun hzA v
    have hmin (z : V → ZMod 2) (hz0 : z ≠ 0) (hzA : A z = 0) :
        d ≤ hammingNorm z := by
      have hm : hammingNorm z ∈ weights := by
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz0, hzA⟩, rfl⟩))
      exact Finset.min'_le weights (hammingNorm z) hm
    have hbit : ∀ a : ZMod 2,
        (if a ≠ 0 then (1 : ℕ) else 0) +
          (if 1 - a ≠ 0 then 1 else 0) = 1 := by decide
    have hbound (S : Finset V) (hS : 2 * S.card = n)
        (hSopp : ∀ {v w : V}, G.Adj v w → (v ∈ S ↔ w ∉ S))
        (z : V → ZMod 2) (hz0 : z ≠ 0)
        (hz1 : z ≠ (fun v => if v ∈ S then 1 else 0))
        (hzA : A z = 0) (hzsupp : ∀ v, v ∉ S → z v = 0) :
        (4 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by
      let b : V → ZMod 2 := fun v => if v ∈ S then 1 else 0
      have hbA : A b = 0 := by
        simpa only [b, Pi.one_apply] using hproj S hSopp (1 : V → ZMod 2) hone
      have hy0 : b - z ≠ 0 := by
        intro hy
        apply hz1
        exact (sub_eq_zero.mp hy).symm
      have hyA : A (b - z) = 0 := by
        rw [map_sub, hbA, hzA, sub_self]
      have hpoint (v : V) :
          (if z v ≠ 0 then (1 : ℕ) else 0) +
            (if (b - z) v ≠ 0 then 1 else 0) =
            if v ∈ S then 1 else 0 := by
        by_cases hv : v ∈ S
        · simpa only [b, Pi.sub_apply, if_pos hv] using hbit (z v)
        · simp [b, hv, hzsupp v hv]
      have hsum : hammingNorm z + hammingNorm (b - z) = S.card := by
        calc
          _ = ∑ v : V,
              ((if z v ≠ 0 then (1 : ℕ) else 0) +
                (if (b - z) v ≠ 0 then 1 else 0)) := by
            simp only [hammingNorm, Finset.card_filter, Finset.sum_add_distrib]
          _ = ∑ v : V, if v ∈ S then (1 : ℕ) else 0 :=
            Finset.sum_congr rfl (fun v _ => hpoint v)
          _ = S.card := by
            rw [← Finset.card_filter]
            simp [Finset.filter_mem_eq_inter]
      have hfirst := hmin z hz0 hzA
      have hsecond := hmin (b - z) hy0 hyA
      have htwo : 2 * d ≤ S.card := by omega
      have hfour : 4 * d ≤ n := by omega
      exact_mod_cast hfour
    let l : V → ZMod 2 := fun v => if v ∈ s then 1 else 0
    let rcode : V → ZMod 2 := fun v => if v ∈ sᶜ then 1 else 0
    let L : Submodule (ZMod 2) (V → ZMod 2) :=
      Submodule.span (ZMod 2) (Set.range ![l, rcode])
    have hLdim : Module.finrank (ZMod 2) L ≤ 2 := by
      simpa only [L, Set.finrank, Fintype.card_fin] using
        (finrank_range_le_card (R := ZMod 2) ![l, rcode])
    have hlL : l ∈ L := Submodule.subset_span ⟨(0 : Fin 2), by simp⟩
    have hrL : rcode ∈ L := Submodule.subset_span ⟨(1 : Fin 2), by simp⟩
    obtain ⟨x, hxC, hxL⟩ : ∃ x : V → ZMod 2, x ∈ C ∧ x ∉ L := by
      by_contra h
      have hCL : C ≤ L := by
        intro x hx
        by_contra hxL
        exact h ⟨x, hx, hxL⟩
      have hdim := Submodule.finrank_mono hCL
      change k ≤ Module.finrank (ZMod 2) L at hdim
      omega
    have hxA : A x = 0 := hxC
    let xL : V → ZMod 2 := fun v => if v ∈ s then x v else 0
    let xR : V → ZMod 2 := fun v => if v ∈ sᶜ then x v else 0
    have hxsum : xL + xR = x := by
      funext v
      by_cases hv : v ∈ s <;> simp [xL, xR, hv]
    have hchoice : (xL ≠ 0 ∧ xL ≠ l) ∨ (xR ≠ 0 ∧ xR ≠ rcode) := by
      by_contra h
      have hxLL : xL ∈ L := by
        by_cases hzero : xL = 0
        · rw [hzero]
          exact L.zero_mem
        · by_cases heql : xL = l
          · rw [heql]
            exact hlL
          · exact False.elim (h (Or.inl ⟨hzero, heql⟩))
      have hxRL : xR ∈ L := by
        by_cases hzero : xR = 0
        · rw [hzero]
          exact L.zero_mem
        · by_cases heqr : xR = rcode
          · rw [heqr]
            exact hrL
          · exact False.elim (h (Or.inr ⟨hzero, heqr⟩))
      apply hxL
      rw [← hxsum]
      exact L.add_mem hxLL hxRL
    rcases hchoice with ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩
    · apply hbound s hside hopp xL hx0 hx1 (hproj s hopp x hxA)
      intro v hv
      simp only [xL, if_neg hv]
    · apply hbound sᶜ hside' hoppc xR hx0 hx1 (hproj sᶜ hoppc x hxA)
      intro v hv
      simp only [xR, if_neg hv]
  · simp only [ho, Nat.cast_one, one_mul]
    exact model_5e76b721dff9cc8391a8 G
      ⟨h_guard.1, h_guard.2.1,
        by linarith only [h_guard.2.2.1],
        by linarith only [h_guard.2.2.2]⟩

theorem model_639525f7a46b1b3dbd00 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Colorable 2) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (V → ZMod 2)).filter (fun x => x ≠ 0 ∧ (G.adjMatrix (ZMod 2)).mulVecLin x = 0)).image hammingNorm; (weights.min' (by simp [weights]) : ℝ)) ≥ (39999999 / 10000000 : ℝ)))) :
    (Fintype.card V : ℝ) ≤ (Real.exp ((((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) / (2 : ℝ)) * (Real.log (1 + (1 : ℝ))))) := by
  classical
  let M := G.adjMatrix (ZMod 2)
  let A := M.mulVecLin
  let E (u : Finset V) : (u → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) :=
    { toFun := fun x v => if hv : v ∈ u then x ⟨v, hv⟩ else 0
      map_add' := by
        intro x y
        funext v
        by_cases hv : v ∈ u <;> simp [hv]
      map_smul' := by
        intro c x
        funext v
        by_cases hv : v ∈ u <;> simp [hv] }
  have hE (u : Finset V) : Function.Injective (E u) := by
    intro x y hxy
    funext v
    have h := congrFun hxy (v : V)
    simpa [E, v.property] using h
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (V → ZMod 2)).filter
      (fun x => x ≠ 0 ∧ A x = 0)).image hammingNorm
  have hwne : weights.Nonempty := by simp [weights]
  have hmin : (weights.min' hwne : ℝ) ≥ (39999999 / 10000000 : ℝ) := by
    simpa only [weights, A, M] using h_guard.2.2
  have hsmall (x : V → ZMod 2) (hx : A x = 0)
      (hn : hammingNorm x ≤ 3) : x = 0 := by
    by_contra hx0
    have hm : hammingNorm x ∈ weights := by
      dsimp only [weights]
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx0, hx⟩, rfl⟩))
    have hle : weights.min' hwne ≤ hammingNorm x :=
      Finset.min'_le weights _ hm
    have hleR : (weights.min' hwne : ℝ) ≤ 3 := by
      exact_mod_cast hle.trans hn
    linarith only [hmin, hleR]
  have hpack (u : Finset V) :
      (2 : ℝ) * (u.card : ℝ) ≤
        (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (A.comp (E u))) := by
    by_cases hu : u.Nonempty
    · obtain ⟨a, ha⟩ := hu
      let x : (u × ZMod 2) → V → ZMod 2 := fun p v =>
        (if v = (p.1 : V) then 1 else 0) + (if v = a then p.2 else 0)
      let f : (u × ZMod 2) → LinearMap.range (A.comp (E u)) := fun p =>
        ⟨A (x p), by
          refine ⟨(fun v : u => x p (v : V)), ?_⟩
          change A (E u (fun v : u => x p (v : V))) = A (x p)
          apply congrArg A
          funext v
          by_cases hv : v ∈ u
          · simp [E, hv]
          · have hvp : v ≠ (p.1 : V) := by
              intro h
              apply hv
              rw [h]
              exact p.1.property
            have hva : v ≠ a := by
              intro h
              exact hv (h.symm ▸ ha)
            simp [E, x, hv, hvp, hva]⟩
      have hf : Function.Injective f := by
        rintro ⟨v, b⟩ ⟨w, c⟩ hxy
        have hsy : A (x (v, b)) = A (x (w, c)) :=
          congrArg (fun z : LinearMap.range (A.comp (E u)) =>
            (z : V → ZMod 2)) hxy
        have hk : A (x (v, b) - x (w, c)) = 0 := by
          rw [map_sub, hsy, sub_self]
        have hn : hammingNorm (x (v, b) - x (w, c)) ≤ 3 := by
          calc
            _ ≤ ({a, (v : V), (w : V)} : Finset V).card := by
              unfold hammingNorm
              apply Finset.card_le_card
              intro i hi
              by_contra hnot
              have hia : i ≠ a := by
                intro h
                apply hnot
                simp [h]
              have hiv : i ≠ (v : V) := by
                intro h
                apply hnot
                simp [h]
              have hiw : i ≠ (w : V) := by
                intro h
                apply hnot
                simp [h]
              exact (Finset.mem_filter.mp hi).2
                (by simp [x, Pi.sub_apply, hia, hiv, hiw])
            _ ≤ 3 := Finset.card_le_three
        have heq : x (v, b) = x (w, c) :=
          sub_eq_zero.mp (hsmall _ hk hn)
        have heq' (i : V) :
            (if i = (v : V) then (1 : ZMod 2) else 0) +
              (if i = a then b else 0) =
            (if i = (w : V) then (1 : ZMod 2) else 0) +
              (if i = a then c else 0) := congrFun heq i
        have hvw : v = w := by
          apply Subtype.ext
          by_contra hne
          by_cases hva : (v : V) = a
          · have hwa : (w : V) ≠ a := by
              intro hwa
              exact hne (hva.trans hwa.symm)
            have hwv : (w : V) ≠ (v : V) := Ne.symm hne
            have hh := heq' (w : V)
            simp only [if_neg hwv, if_pos rfl, if_neg hwa,
              zero_add, add_zero] at hh
            exact zero_ne_one hh
          · have hh := heq' (v : V)
            simp only [if_pos rfl, if_neg hne, if_neg hva, add_zero] at hh
            exact one_ne_zero hh
        have hbc : b = c := by
          have hh := heq' a
          rw [hvw] at hh
          simp only [if_pos rfl] at hh
          exact add_left_cancel hh
        exact Prod.ext hvw hbc
      have hc : u.card * 2 ≤ 2 ^ Module.finrank (ZMod 2)
          (LinearMap.range (A.comp (E u))) := by
        calc
          _ = Fintype.card (u × ZMod 2) := by
            rw [Fintype.card_prod, Fintype.card_coe, ZMod.card]
          _ ≤ Fintype.card (LinearMap.range (A.comp (E u))) :=
            Fintype.card_le_of_injective f hf
          _ = _ := by
            rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      have hcR : (u.card : ℝ) * 2 ≤
          (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (A.comp (E u))) := by
        exact_mod_cast hc
      linarith only [hcR]
    · have hu0 : u = ∅ := by
        apply Finset.ext
        intro v
        constructor
        · intro hv
          exact (hu ⟨v, hv⟩).elim
        · intro hv
          simp at hv
      have hcard : u.card = 0 := by simp [hu0]
      rw [hcard, Nat.cast_zero, mul_zero]
      exact pow_nonneg (by norm_num) _
  obtain ⟨c⟩ := h_guard.1
  let s : Finset V := Finset.univ.filter (fun v => c v = 0)
  let t : Finset V := sᶜ
  have hs0 (v : V) (hv : v ∈ s) : c v = 0 :=
    (Finset.mem_filter.mp hv).2
  have ht1 (v : V) (hv : v ∈ t) : c v = 1 := by
    have hv0 : c v ≠ 0 := by
      intro h
      have hvs : v ∈ s := by simp [s, h]
      exact (Finset.mem_compl.mp hv) hvs
    have hval : (c v).val ≠ 0 := by
      intro h
      exact hv0 (Fin.ext h)
    have hlt := (c v).isLt
    apply Fin.ext
    change (c v).val = 1
    omega
  have hs_zero (v w : V) (hv : v ∈ s) (hw : w ∈ s) : M v w = 0 := by
    have hnot : ¬ G.Adj v w := by
      intro h
      exact c.valid h ((hs0 v hv).trans (hs0 w hw).symm)
    simp [M, SimpleGraph.adjMatrix_apply, hnot]
  have ht_zero (v w : V) (hv : v ∈ t) (hw : w ∈ t) : M v w = 0 := by
    have hnot : ¬ G.Adj v w := by
      intro h
      exact c.valid h ((ht1 v hv).trans (ht1 w hw).symm)
    simp [M, SimpleGraph.adjMatrix_apply, hnot]
  have hsym (v w : V) : M v w = M w v :=
    (G.isAdjMatrix_adjMatrix (ZMod 2)).symm.apply w v
  have hrow (u : Finset V) (x : u → ZMod 2) (v : V) :
      A (E u x) v = ∑ w : u, M v (w : V) * x w := by
    change (∑ w : V, M v w * (E u x) w) = _
    calc
      _ = ∑ w ∈ u, M v w * (E u x) w := by
        symm
        apply Finset.sum_subset (Finset.subset_univ u)
        intro w _ hw
        simp [E, hw]
      _ = ∑ w : u, M v (w : V) * (E u x) (w : V) :=
        (Finset.sum_coe_sort u (fun w => M v w * (E u x) w)).symm
      _ = ∑ w : u, M v (w : V) * x w := by
        apply Finset.sum_congr rfl
        intro w _
        simp [E, w.property]
  let B : Matrix t s (ZMod 2) := fun v w => M (v : V) (w : V)
  have hAs : A.comp (E s) = (E t).comp B.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext v
    change A (E s x) v = (E t (B.mulVecLin x)) v
    rw [hrow]
    by_cases hv : v ∈ s
    · rw [show (E t (B.mulVecLin x)) v = 0 by simp [E, t, hv]]
      apply Finset.sum_eq_zero
      intro w _
      rw [hs_zero v (w : V) hv w.property, zero_mul]
    · have hvt : v ∈ t := Finset.mem_compl.mpr hv
      rw [show (E t (B.mulVecLin x)) v = B.mulVecLin x ⟨v, hvt⟩ by
        simp [E, hvt]]
      rfl
  have hAt : A.comp (E t) = (E s).comp B.transpose.mulVecLin := by
    apply LinearMap.ext
    intro x
    funext v
    change A (E t x) v = (E s (B.transpose.mulVecLin x)) v
    rw [hrow]
    by_cases hv : v ∈ s
    · rw [show (E s (B.transpose.mulVecLin x)) v =
          B.transpose.mulVecLin x ⟨v, hv⟩ by simp [E, hv]]
      change (∑ w : t, M v (w : V) * x w) =
        ∑ w : t, M (w : V) v * x w
      apply Finset.sum_congr rfl
      intro w _
      rw [hsym v (w : V)]
    · rw [show (E s (B.transpose.mulVecLin x)) v = 0 by simp [E, hv]]
      have hvt : v ∈ t := Finset.mem_compl.mpr hv
      apply Finset.sum_eq_zero
      intro w _
      rw [ht_zero v (w : V) hvt w.property, zero_mul]
  have hrs : Module.finrank (ZMod 2) (LinearMap.range (A.comp (E s))) = B.rank := by
    rw [hAs, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective (E t) (hE t)
      (LinearMap.range B.mulVecLin)).finrank_eq.symm
  have hrt : Module.finrank (ZMod 2) (LinearMap.range (A.comp (E t))) = B.rank := by
    calc
      _ = B.transpose.rank := by
        rw [hAt, LinearMap.range_comp]
        exact (Submodule.equivMapOfInjective (E s) (hE s)
          (LinearMap.range B.transpose.mulVecLin)).finrank_eq.symm
      _ = B.rank := Matrix.rank_transpose B
  have hrange : LinearMap.range A =
      LinearMap.range (A.comp (E s)) ⊔ LinearMap.range (A.comp (E t)) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have hx : x = E s (fun v : s => x (v : V)) +
          E t (fun v : t => x (v : V)) := by
        funext v
        by_cases hv : v ∈ s <;> simp [E, t, hv]
      rw [hx, map_add]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · exact sup_le (LinearMap.range_comp_le_range (E s) A)
        (LinearMap.range_comp_le_range (E t) A)
  have hdisjoint : Disjoint (LinearMap.range (A.comp (E s)))
      (LinearMap.range (A.comp (E t))) := by
    rw [Submodule.disjoint_def]
    intro x hx hy
    rcases hx with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    rw [hAs] at ha
    rw [hAt] at hb
    funext v
    by_cases hv : v ∈ s
    · have h := congrFun ha v
      change (E t (B.mulVecLin a)) v = x v at h
      simpa [E, t, hv] using h.symm
    · have h := congrFun hb v
      change (E s (B.transpose.mulVecLin b)) v = x v at h
      simpa [E, hv] using h.symm
  have hArank : Module.finrank (ZMod 2) (LinearMap.range A) = 2 * B.rank := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (A.comp (E s))) (LinearMap.range (A.comp (E t)))
    rw [← hrange, hdisjoint.eq_bot, finrank_bot, add_zero, hrs, hrt] at hdim
    omega
  have hp := hpack s
  have hq := hpack t
  rw [hrs] at hp
  rw [hrt] at hq
  have hcardN : s.card + t.card = Fintype.card V := Finset.card_add_card_compl s
  have hcardR : (s.card : ℝ) + (t.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcardN
  have hbound : (Fintype.card V : ℝ) ≤ (2 : ℝ) ^ B.rank := by
    linarith only [hp, hq, hcardR]
  have hn : 2 * B.rank + Module.finrank (ZMod 2) (LinearMap.ker A) =
      Fintype.card V := by
    simpa only [hArank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker A
  have hnR : (2 : ℝ) * (B.rank : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hn
  have hreal : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ) = (2 : ℝ) * (B.rank : ℝ) := by
    linarith only [hnR]
  have hexp : Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 *
      Real.log (1 + (1 : ℝ))) = (2 : ℝ) ^ B.rank := by
    rw [hreal]
    have hh : (2 : ℝ) * (B.rank : ℝ) / 2 = (B.rank : ℝ) := by ring
    rw [hh, show (1 : ℝ) + 1 = 2 by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  change (Fintype.card V : ℝ) ≤
    Real.exp (((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A) : ℝ)) / 2 * Real.log (1 + (1 : ℝ)))
  rw [hexp]
  exact hbound
theorem model_de47993e34075cfd3cba {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((∃ d : ℕ, G.IsRegularOfDegree d)) ∧ ((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (((1 : ℝ) - ((G.minDegree : ℝ) - ((2 : ℝ) * ((Int.floor ((G.minDegree : ℝ) / (2 : ℝ))) : ℝ)))) * ((2 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))))) := by
  classical
  let n : ℕ := Fintype.card V
  let d : ℕ := G.minDegree
  let M : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let A : (V → ZMod 2) →ₗ[ZMod 2] (V → ZMod 2) := M.mulVecLin
  let K : Submodule (ZMod 2) (V → ZMod 2) := LinearMap.ker A
  let k : ℕ := Module.finrank (ZMod 2) K
  change (k : ℝ) ≥ (1 - ((d : ℝ) - 2 * (Int.floor ((d : ℝ) / 2) : ℝ))) *
    (2 - ((n : ℝ) - 2 * (Int.floor ((n : ℝ) / 2) : ℝ)))
  have hrem (m : ℕ) : (m : ℝ) - 2 * (Int.floor ((m : ℝ) / 2) : ℝ) =
      ((m % 2 : ℕ) : ℝ) := by
    let q : ℕ := m / 2
    have hm : m = 2 * q + m % 2 := by
      dsimp [q]
      omega
    have hmr : (m : ℝ) = 2 * (q : ℝ) + ((m % 2 : ℕ) : ℝ) := by
      exact_mod_cast hm
    have hr0 : (0 : ℝ) ≤ ((m % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hrlt : ((m % 2 : ℕ) : ℝ) < 2 := by
      exact_mod_cast (Nat.mod_lt m (by decide : 0 < (2 : ℕ)))
    have hfloor : Int.floor ((m : ℝ) / 2) = (q : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hmr, hr0, hrlt]
    rw [hfloor]
    push_cast
    linarith only [hmr]
  rw [hrem d, hrem n]
  rcases Nat.mod_two_eq_zero_or_one d with he | ho
  · simp only [he, Nat.cast_zero, sub_zero, one_mul]
    have hdpos : 0 < d := by
      have h : (0 : ℝ) < (d : ℝ) := by
        change (0 : ℝ) < (G.minDegree : ℝ)
        linarith only [h_guard.2]
      exact_mod_cast h
    haveI : Nonempty V := by
      rcases isEmpty_or_nonempty V with h | h
      · letI : IsEmpty V := h
        have hz : d = 0 := by simp [d]
        omega
      · exact h
    obtain ⟨a⟩ := ‹Nonempty V›
    have hnpos : 0 < n := Fintype.card_pos
    obtain ⟨r, hr⟩ := h_guard.1
    have hdegree (v : V) : G.degree v = d :=
      (hr.degree_eq v).trans hr.minDegree_eq.symm
    have hd0 : (d : ZMod 2) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_iff.mpr he)
    have hone : A (1 : V → ZMod 2) = 0 := by
      funext v
      change (Matrix.mulVec (G.adjMatrix (ZMod 2))
        (Function.const V (1 : ZMod 2))) v = 0
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hdegree v, hd0, mul_one]
    let c : K := ⟨(1 : V → ZMod 2), hone⟩
    have hc : c ≠ 0 := by
      intro h
      have hh := congrArg (fun z : K => z.1 a) h
      change (1 : ZMod 2) = 0 at hh
      exact one_ne_zero hh
    have hge1 : 1 ≤ k := by
      have hpos : 0 < Module.finrank (ZMod 2) K :=
        Module.finrank_pos_iff_exists_ne_zero.mpr ⟨c, hc⟩
      change 1 ≤ Module.finrank (ZMod 2) K
      omega
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have hge2 : 2 ≤ k := by
        by_contra h
        have hk1 : Module.finrank (ZMod 2) K = 1 := by
          change k = 1
          omega
        let s : Finset V := ({a} : Finset V)ᶜ
        have hscard : Fintype.card s = n - 1 := by
          simp only [Fintype.card_coe, s, Finset.card_compl,
            Finset.card_singleton, n]
        have hsodd : Odd (Fintype.card s) := by
          apply Nat.not_even_iff_odd.mp
          intro hs
          have hmod : Fintype.card s % 2 = 0 := Nat.even_iff.mp hs
          omega
        let B : Matrix s s (ZMod 2) := fun i j => M (i : V) (j : V)
        have hM : M.IsSymm := G.isSymm_adjMatrix
        have hBsymm (i j : s) : B i j = B j i :=
          hM.apply (j : V) (i : V)
        have hBdiag (i : s) : B i i = 0 := by simp [B, M]
        have htwo (t : ZMod 2) : t + t = 0 := by
          simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel t
        have hdet : B.det = 0 := by
          let F : Equiv.Perm s → ZMod 2 := fun σ =>
            Equiv.Perm.sign σ • ∏ i : s, B (σ i) i
          have hFinv (σ : Equiv.Perm s) : F σ⁻¹ = F σ := by
            dsimp only [F]
            rw [Equiv.Perm.sign_inv]
            apply congrArg (fun z : ZMod 2 => Equiv.Perm.sign σ • z)
            apply Fintype.prod_equiv σ.symm
            intro i
            simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using
              hBsymm (σ.symm i) i
          have hFzero (σ : Equiv.Perm s) (hσ : σ⁻¹ = σ) : F σ = 0 := by
            have hfix : ∃ i : s, σ i = i := by
              by_contra hno
              have hnf (i : s) : σ i ≠ i := fun hi => hno ⟨i, hi⟩
              have hinvol (i : s) : σ (σ i) = i := by
                calc
                  σ (σ i) = σ⁻¹ (σ i) :=
                    congrArg (fun τ : Equiv.Perm s => τ (σ i)) hσ.symm
                  _ = i := σ.symm_apply_apply i
              have hsum : (∑ i : s, (1 : ZMod 2)) = 0 := by
                apply Finset.sum_ninvolution (fun i : s => σ i)
                · intro i
                  exact htwo 1
                · intro i hi
                  exact hnf i
                · intro i
                  exact Finset.mem_univ _
                · exact hinvol
              have hcard : (Fintype.card s : ZMod 2) = 0 := by
                simpa using hsum
              exact (Nat.not_even_iff_odd.mpr hsodd)
                (ZMod.natCast_eq_zero_iff_even.mp hcard)
            obtain ⟨i, hi⟩ := hfix
            have hprod : (∏ j : s, B (σ j) j) = 0 := by
              apply Finset.prod_eq_zero (Finset.mem_univ i)
              rw [hi]
              exact hBdiag i
            dsimp only [F]
            rw [hprod, smul_zero]
          rw [Matrix.det_apply]
          change (∑ σ : Equiv.Perm s, F σ) = 0
          apply Finset.sum_ninvolution (fun σ : Equiv.Perm s => σ⁻¹)
          · intro σ
            rw [hFinv]
            exact htwo _
          · intro σ hne hfix
            exact hne (hFzero σ hfix)
          · intro σ
            exact Finset.mem_univ _
          · intro σ
            exact inv_inv σ
        have htrivial (z : s → ZMod 2) (hz : B.mulVecLin z = 0) : z = 0 := by
          let y : V → ZMod 2 := fun v =>
            if hv : v ∈ s then z ⟨v, hv⟩ else 0
          have hya : y a = 0 := by simp [y, s]
          have hrow (v : s) : A y (v : V) = B.mulVecLin z v := by
            change (∑ w : V, M (v : V) w * y w) =
              ∑ w : s, M (v : V) (w : V) * z w
            calc
              _ = ∑ w ∈ s, M (v : V) w * y w := by
                symm
                apply Finset.sum_subset (Finset.subset_univ s)
                intro w hw hws
                simp [y, hws]
              _ = ∑ w : s, M (v : V) (w : V) * y (w : V) :=
                (Finset.sum_coe_sort s (fun w => M (v : V) w * y w)).symm
              _ = ∑ w : s, M (v : V) (w : V) * z w := by
                apply Finset.sum_congr rfl
                intro w hw
                simp [y, w.property]
          have hrows (v : s) : A y (v : V) = 0 :=
            (hrow v).trans (congrFun hz v)
          have hsum : (∑ v : V, A y v) = 0 := by
            have hh := hM.dotProduct_mulVec_comm
              (x := (1 : V → ZMod 2)) (y := y)
            change dotProduct (1 : V → ZMod 2) (A y) =
              dotProduct y (A (1 : V → ZMod 2)) at hh
            simpa only [hone, one_dotProduct, dotProduct_zero] using hh
          have hsuma : (∑ v : V, A y v) = A y a := by
            apply Finset.sum_eq_single a
            · intro v hv hva
              exact hrows ⟨v, by simp [s, hva]⟩
            · intro ha
              exact (ha (Finset.mem_univ a)).elim
          have hrowa : A y a = 0 := hsuma.symm.trans hsum
          have hyA : A y = 0 := by
            funext v
            change A y v = 0
            by_cases hva : v = a
            · simpa only [hva] using hrowa
            · exact hrows ⟨v, by simp [s, hva]⟩
          obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one hk1 hc (⟨y, hyA⟩ : K)
          have ht0 : t = 0 := by
            have hh := congrArg (fun z : K => z.1 a) ht
            change t • (1 : ZMod 2) = y a at hh
            simpa only [smul_eq_mul, mul_one, hya] using hh
          have hyzero : y = 0 := by
            have hh := congrArg (fun z : K => z.1) ht
            change t • (1 : V → ZMod 2) = y at hh
            simpa only [ht0, zero_smul] using hh.symm
          funext v
          have hh := congrFun hyzero (v : V)
          simpa [y, v.property] using hh
        have hBi : Function.Injective B.mulVec := by
          intro z w hzw
          apply sub_eq_zero.mp
          apply htrivial
          change Matrix.mulVec B (z - w) = 0
          rw [Matrix.mulVec_sub, hzw, sub_self]
        have hunit : IsUnit B.det :=
          (Matrix.isUnit_iff_isUnit_det B).mp
            (Matrix.mulVec_injective_iff_isUnit.mp hBi)
        rw [hdet] at hunit
        exact not_isUnit_zero hunit
      have hR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge2
      simpa only [hn0, Nat.cast_zero, sub_zero] using hR
    · have hR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge1
      simp only [hn1, Nat.cast_one]
      linarith only [hR]
  · simp only [ho, Nat.cast_one, sub_self, zero_mul]
    exact Nat.cast_nonneg k
