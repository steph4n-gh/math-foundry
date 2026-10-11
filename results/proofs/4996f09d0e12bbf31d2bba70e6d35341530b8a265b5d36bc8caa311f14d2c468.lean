import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.ZMod.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic










open scoped BigOperators

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

theorem pilot_independence_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  classical
  exact composed_2cd2dd810fbb9720 (Gᶜ)

theorem hull3d_independence_number_le_1_0_order_clique_number_0_is_regular_9d665c9d4a4d {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((∃ d : ℕ, G.IsRegularOfDegree d))) :
    (Gᶜ.cliqueNum : ℝ) ≤ (Fintype.card V : ℝ) := by
  have h := pilot_independence_le_order G; nlinarith [(show (0 : ℝ) ≤ (Fintype.card V : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.edgeFinset.card : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.maxDegree : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.cliqueNum : ℝ) from Nat.cast_nonneg _), (show (0 : ℝ) ≤ (G.chromaticNumber.toNat : ℝ) from Nat.cast_nonneg _)]

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
theorem model_fcf51e36faf8ebb9be9b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (G.IsAcyclic)) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  let H (s : Finset V) : SimpleGraph s := G.induce (s : Set V)
  let A (s : Finset V) : (s → ZMod 2) →ₗ[ZMod 2] (s → ZMod 2) :=
    (H s).adjMatrix (ZMod 2) |>.mulVecLin
  let K (s : Finset V) : Submodule (ZMod 2) (s → ZMod 2) := LinearMap.ker (A s)
  let E (s : Finset V) (x : s → ZMod 2) (v : V) : ZMod 2 :=
    if hv : v ∈ s then x ⟨v, hv⟩ else 0
  have hrow (s : Finset V) (x : s → ZMod 2) (v : s) :
      A s x v = ∑ w ∈ s, G.adjMatrix (ZMod 2) (v : V) w * E s x w := by
    change (∑ w : s, G.adjMatrix (ZMod 2) (v : V) (w : V) * x w) = _
    calc
      _ = ∑ w : s, G.adjMatrix (ZMod 2) (v : V) (w : V) * E s x (w : V) := by
        apply Finset.sum_congr rfl
        intro w hw
        simp [E, w.property]
      _ = _ := Finset.sum_coe_sort s
        (fun w => G.adjMatrix (ZMod 2) (v : V) w * E s x w)
  have aux : ∀ s : Finset V, ∃ r : Finset V,
      r ⊆ s ∧ G.IsIndepSet (r : Set V) ∧
        Module.finrank (ZMod 2) (K s) + s.card ≤ 2 * r.card := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih
    by_cases hnone : ∀ u v : s, ¬ (H s).Adj u v
    · refine ⟨s, (fun _ h => h), ?_, ?_⟩
      · intro u hu v hv huv
        exact hnone ⟨u, hu⟩ ⟨v, hv⟩
      · have hk : Module.finrank (ZMod 2) (K s) ≤ s.card := by
          calc
            _ ≤ Module.finrank (ZMod 2) (s → ZMod 2) := Submodule.finrank_le _
            _ = s.card := by
              simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
        omega
    · push_neg at hnone
      obtain ⟨u0, v0, h0⟩ := hnone
      letI : Nonempty s := ⟨u0⟩
      have hac : (H s).IsAcyclic := h_guard.induce (s : Set V)
      obtain ⟨u, v, p, hp, hmax⟩ :=
        SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (H s)
      have hlen : 1 ≤ p.length := by
        have hm := hmax u0 v0 h0.toWalk h0.isPath_toWalk
        simpa only [SimpleGraph.Adj.length_toWalk] using hm
      have hnil : ¬ p.Nil := by
        intro hn
        have hz := SimpleGraph.Walk.length_eq_zero_iff.mpr hn
        omega
      let b : s := p.snd
      have hab : (H s).Adj u b := p.adj_snd hnil
      have habG : G.Adj (u : V) (b : V) := hab
      have hleaf (w : s) (hw : (H s).Adj u w) : w = b := by
        apply hac.eq_snd_of_adj_start hp hw
        by_contra hn
        have hp' : (p.cons hw.symm).IsPath := hp.cons hn
        have hm := hmax w v (p.cons hw.symm) hp'
        simp only [SimpleGraph.Walk.length_cons] at hm
        omega
      have hub : (u : V) ≠ (b : V) := habG.ne
      let t : Finset V := (s.erase (u : V)).erase (b : V)
      have hts : t ⊆ s := by
        intro w hw
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2
      have hut : (u : V) ∉ t := by simp [t]
      have hbt : (b : V) ∉ t := by simp [t]
      have hlt : t ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hts, ?_⟩
        intro h
        exact hut (h.symm ▸ u.property)
      have hbmem : (b : V) ∈ s.erase (u : V) :=
        Finset.mem_erase.mpr ⟨hub.symm, b.property⟩
      have hcard : t.card + 2 = s.card := by
        have hc1 := Finset.card_erase_add_one u.property
        have hc2 := Finset.card_erase_add_one hbmem
        change t.card + 1 = (s.erase (u : V)).card at hc2
        omega
      have hno (w : V) (hw : w ∈ t) : ¬ G.Adj (u : V) w := by
        intro hadj
        have heq : w = (b : V) :=
          congrArg Subtype.val (hleaf ⟨w, hts hw⟩ hadj)
        exact hbt (heq ▸ hw)
      have hxb (x : K s) : x.1 b = 0 := by
        have hx := congrFun (LinearMap.mem_ker.mp x.property) u
        change (∑ w : s, G.adjMatrix (ZMod 2) (u : V) (w : V) * x.1 w) = 0 at hx
        have hs : (∑ w : s, G.adjMatrix (ZMod 2) (u : V) (w : V) * x.1 w) = x.1 b := by
          calc
            _ = G.adjMatrix (ZMod 2) (u : V) (b : V) * x.1 b := by
              apply Finset.sum_eq_single b
              · intro w hw hwb
                have hn : ¬ G.Adj (u : V) (w : V) := by
                  intro hadj
                  exact hwb (hleaf w hadj)
                simp [SimpleGraph.adjMatrix_apply, hn]
              · simp
            _ = x.1 b := by simp [SimpleGraph.adjMatrix_apply, habG]
        exact hs.symm.trans hx
      let R : (s → ZMod 2) →ₗ[ZMod 2] (t → ZMod 2) :=
        { toFun := fun x w => x ⟨(w : V), hts w.property⟩
          map_add' := by intro x y; rfl
          map_smul' := by intro c x; rfl }
      have hR (x : K s) : R x.1 ∈ K t := by
        change A t (R x.1) = 0
        funext w
        change A t (R x.1) w = 0
        let ws : s := ⟨(w : V), hts w.property⟩
        have hx : A s x.1 ws = 0 :=
          congrFun (LinearMap.mem_ker.mp x.property) ws
        calc
          _ = ∑ i ∈ t, G.adjMatrix (ZMod 2) (w : V) i * E t (R x.1) i :=
            hrow t (R x.1) w
          _ = ∑ i ∈ t, G.adjMatrix (ZMod 2) (w : V) i * E s x.1 i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [E, R, hi, hts hi]
          _ = ∑ i ∈ s, G.adjMatrix (ZMod 2) (w : V) i * E s x.1 i := by
            apply Finset.sum_subset hts
            intro i his hit
            have hrem : i = (u : V) ∨ i = (b : V) := by
              by_contra h
              have hiu : i ≠ (u : V) := fun hiu => h (Or.inl hiu)
              have hib : i ≠ (b : V) := fun hib => h (Or.inr hib)
              exact hit (Finset.mem_erase.mpr
                ⟨hib, Finset.mem_erase.mpr ⟨hiu, his⟩⟩)
            rcases hrem with rfl | rfl
            · have hn : ¬ G.Adj (w : V) (u : V) :=
                fun hadj => hno (w : V) w.property hadj.symm
              simp [SimpleGraph.adjMatrix_apply, hn]
            · simp [E, b.property, hxb x]
          _ = A s x.1 ws := (hrow s x.1 ws).symm
          _ = 0 := hx
      let f : K s →ₗ[ZMod 2] K t :=
        (R.domRestrict (K s)).codRestrict (K t) hR
      have hf : Function.Injective f := by
        intro x y hxy
        let z : K s := x - y
        have hzR : R z.1 = 0 := by
          have hxy' := congrArg (fun k : K t => (k : t → ZMod 2)) hxy
          change R x.1 = R y.1 at hxy'
          change R (x.1 - y.1) = 0
          rw [map_sub, hxy', sub_self]
        have hzval (w : s) (hwu : w ≠ u) : z.1 w = 0 := by
          by_cases hwb : w = b
          · subst w
            exact hxb z
          · have hiu : (w : V) ≠ (u : V) := fun h => hwu (Subtype.ext h)
            have hib : (w : V) ≠ (b : V) := fun h => hwb (Subtype.ext h)
            have hwt : (w : V) ∈ t :=
              Finset.mem_erase.mpr ⟨hib, Finset.mem_erase.mpr ⟨hiu, w.property⟩⟩
            have hh := congrFun hzR (⟨(w : V), hwt⟩ : t)
            change z.1 w = 0 at hh
            exact hh
        have hzrow := congrFun (LinearMap.mem_ker.mp z.property) b
        change (∑ w : s, G.adjMatrix (ZMod 2) (b : V) (w : V) * z.1 w) = 0 at hzrow
        have hs : (∑ w : s, G.adjMatrix (ZMod 2) (b : V) (w : V) * z.1 w) = z.1 u := by
          calc
            _ = G.adjMatrix (ZMod 2) (b : V) (u : V) * z.1 u := by
              apply Finset.sum_eq_single u
              · intro w hw hwu
                rw [hzval w hwu, mul_zero]
              · simp
            _ = z.1 u := by simp [SimpleGraph.adjMatrix_apply, habG.symm]
        have hzu : z.1 u = 0 := hs.symm.trans hzrow
        apply sub_eq_zero.mp
        apply Subtype.ext
        funext w
        change z.1 w = 0
        by_cases hwu : w = u
        · subst w
          exact hzu
        · exact hzval w hwu
      have hk : Module.finrank (ZMod 2) (K s) ≤ Module.finrank (ZMod 2) (K t) :=
        LinearMap.finrank_le_finrank_of_injective hf
      obtain ⟨r, hrs, hir, hdim⟩ := ih t hlt
      have hur : (u : V) ∉ r := fun hu => hut (hrs hu)
      refine ⟨insert (u : V) r, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact u.property
        · exact hts (hrs hw)
      · intro w hw z hz hwz hadj
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hadj.ne rfl
          · exact hno z (hrs hz) hadj
        · rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hno w (hrs hw) hadj.symm
          · exact hir hw hz hwz hadj
      · rw [Finset.card_insert_of_notMem hur]
        omega
  obtain ⟨r, hrs, hir, hdim⟩ := aux (Finset.univ : Finset V)
  have hr : r.card ≤ Gᶜ.cliqueNum := by
    simpa only [SimpleGraph.cliqueNum_compl] using hir.card_le_indepNum
  let B := (G.adjMatrix (ZMod 2)).mulVecLin
  let q : (V → ZMod 2) →ₗ[ZMod 2] (↥(Finset.univ : Finset V) → ZMod 2) :=
    { toFun := fun x v => x (v : V)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hq (x : LinearMap.ker B) : q x.1 ∈ K (Finset.univ : Finset V) := by
    change A (Finset.univ : Finset V) (q x.1) = 0
    funext v
    change A (Finset.univ : Finset V) (q x.1) v = 0
    have he : E (Finset.univ : Finset V) (q x.1) = x.1 := by
      funext w
      simp [E, q]
    rw [hrow, he]
    have hx := congrFun (LinearMap.mem_ker.mp x.property) (v : V)
    change (∑ w : V, G.adjMatrix (ZMod 2) (v : V) w * x.1 w) = 0 at hx
    exact hx
  let e : LinearMap.ker B →ₗ[ZMod 2] K (Finset.univ : Finset V) :=
    (q.domRestrict (LinearMap.ker B)).codRestrict (K (Finset.univ : Finset V)) hq
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    funext v
    have h := congrArg
      (fun k : K (Finset.univ : Finset V) => k.1 ⟨v, Finset.mem_univ v⟩) hxy
    change x.1 v = y.1 v at h
    exact h
  have hk : Module.finrank (ZMod 2) (LinearMap.ker B) ≤
      Module.finrank (ZMod 2) (K (Finset.univ : Finset V)) :=
    LinearMap.finrank_le_finrank_of_injective he
  have hn : Module.finrank (ZMod 2) (LinearMap.ker B) + Fintype.card V ≤
      2 * Gᶜ.cliqueNum := by
    calc
      _ ≤ Module.finrank (ZMod 2) (K (Finset.univ : Finset V)) + Fintype.card V :=
        Nat.add_le_add_right hk _
      _ ≤ 2 * r.card := by simpa only [Finset.card_univ] using hdim
      _ ≤ 2 * Gᶜ.cliqueNum := Nat.mul_le_mul_left 2 hr
  have hnR : (Module.finrank (ZMod 2) (LinearMap.ker B) : ℝ) +
      (Fintype.card V : ℝ) ≤ (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) := by
    exact_mod_cast hn
  change (Module.finrank (ZMod 2) (LinearMap.ker B) : ℝ) ≤
    (2 : ℝ) * (Gᶜ.cliqueNum : ℝ) - (Fintype.card V : ℝ)
  linarith only [hnR]
