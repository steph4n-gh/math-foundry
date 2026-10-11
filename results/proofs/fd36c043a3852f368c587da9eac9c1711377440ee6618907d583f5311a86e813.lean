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

theorem parity_code_dimension_le_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ (Fintype.card V : ℝ) := by
  have hn : Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤ Fintype.card V := by
    calc
      _ ≤ Module.finrank (ZMod 2) (V → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card (ZMod 2)
  exact_mod_cast hn

theorem model_c0b68b8f55a47e0a3735 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) * (G.edgeFinset.card : ℝ)) ≤ (((Fintype.card V : ℝ) - (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) * ((G.maxDegree : ℝ) ^ 2)) := by
  classical
  let A := G.adjMatrix (ZMod 2)
  let r := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A.col))
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range A.col)
  choose a ha using hf
  have hspan' : Submodule.span (ZMod 2) (Set.range (A.col ∘ a)) =
      Submodule.span (ZMod 2) (Set.range A.col) := by
    have hfun : A.col ∘ a = f := by
      funext i
      exact ha i
    rw [hfun]
    exact hspan
  let T : Finset V := Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
  have hz : ∀ v : V, v ∉ T → G.degree v = 0 := by
    intro v hv
    have hbase (i : Fin r) : A.col (a i) v = 0 := by
      have hnot : ¬ G.Adj v (a i) := by
        intro h
        apply hv
        change v ∈ Finset.univ.biUnion (fun i : Fin r => G.neighborFinset (a i))
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ i, (G.mem_neighborFinset (a i) v).mpr h.symm⟩
      simp [Matrix.col_apply, A, hnot]
    have hzero : ∀ x ∈ Submodule.span (ZMod 2) (Set.range (A.col ∘ a)), x v = 0 := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x v = 0) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        exact hbase i
      · rfl
      · intro x y _ _ hx hy
        change x v + y v = 0
        rw [hx, hy, add_zero]
      · intro b x _ hx
        change b * x v = 0
        rw [hx, mul_zero]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hpos
    have hwzero : A.col w v = 0 := hzero (A.col w) (by
      rw [hspan']
      exact Submodule.subset_span ⟨w, rfl⟩)
    simpa [Matrix.col_apply, A, hw] using hwzero
  have hT : T.card ≤ r * G.maxDegree := by
    calc
      T.card ≤ ∑ i : Fin r, (G.neighborFinset (a i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin r, G.maxDegree := Finset.sum_le_sum (fun i _ => by
        simpa only [G.card_neighborFinset_eq_degree] using G.degree_le_maxDegree (a i))
      _ = r * G.maxDegree := by simp
  have he : 2 * G.edgeFinset.card ≤ r * G.maxDegree ^ 2 := by
    calc
      2 * G.edgeFinset.card = ∑ v, G.degree v := G.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ v ∈ T, G.degree v := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro v _ hv
        exact hz v hv
      _ ≤ ∑ _v ∈ T, G.maxDegree :=
        Finset.sum_le_sum (fun v _ => G.degree_le_maxDegree v)
      _ = T.card * G.maxDegree := by simp
      _ ≤ (r * G.maxDegree) * G.maxDegree := Nat.mul_le_mul_right _ hT
      _ = r * G.maxDegree ^ 2 := by ring
  have hr : r + Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) = Fintype.card V := by
    have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at h
    exact h
  have hrreal : (r : ℝ) +
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) =
      (Fintype.card V : ℝ) := by
    exact_mod_cast hr
  have hrsub : (Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ) = (r : ℝ) := by
    linarith
  change (2 : ℝ) * (G.edgeFinset.card : ℝ) ≤
    ((Fintype.card V : ℝ) -
      (Module.finrank (ZMod 2) (LinearMap.ker A.mulVecLin) : ℝ)) *
      (G.maxDegree : ℝ) ^ 2
  rw [hrsub]
  exact_mod_cast he

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

theorem model_7378e4999b7091aa506b {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) = (((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ))) + (((2 : ℝ) * (((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) + (1 : ℝ))) * ((1 : ℝ) - ((Fintype.card V : ℝ) - ((2 : ℝ) * ((Int.floor ((Fintype.card V : ℝ) / (2 : ℝ))) : ℝ)))))) := by
  classical
  have hconn : G.Connected := h_guard.1
  letI : Nonempty V := hconn.nonempty
  have hmax : G.maxDegree ≤ 2 := by
    have hlt : (G.maxDegree : ℝ) < 3 := by
      linarith [h_guard.2]
    have hlt' : G.maxDegree < 3 := by exact_mod_cast hlt
    omega
  have hdeg (u : V) : G.degree u ≤ 2 :=
    (G.degree_le_maxDegree u).trans hmax
  by_cases hreg : G.IsRegularOfDegree 2
  · have hmin : G.minDegree = 2 := hreg.minDegree_eq
    have hdim := model_498663d70c6a4882faec G
      ⟨hconn, ⟨2, hreg⟩, by rw [hmin]; norm_num⟩
    have hregular (u : V) : G.degree u = 2 := hreg.degree_eq u
    have hsum : 2 * Fintype.card V = 2 * G.edgeFinset.card := by
      simpa [hregular, Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges
    have he : G.edgeFinset.card = Fintype.card V := by omega
    rw [he]
    nlinarith only [hdim]
  · have hlow : ∃ a : V, G.degree a < 2 := by
      by_contra h
      apply hreg
      intro v
      have hv := hdeg v
      have hnv : ¬ G.degree v < 2 := by
        intro hv'
        exact h ⟨v, hv'⟩
      omega
    obtain ⟨a, ha⟩ := hlow
    have hsum : (∑ v : V, G.degree v) < ∑ _v : V, (2 : ℕ) :=
      Finset.sum_lt_sum (fun v _ => hdeg v) ⟨a, Finset.mem_univ a, ha⟩
    have hsum' : 2 * G.edgeFinset.card < 2 * Fintype.card V := by
      simpa [G.sum_degrees_eq_twice_card_edges, Nat.mul_comm] using hsum
    have hconncard : Fintype.card V ≤ G.edgeFinset.card + 1 := by
      simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
        hconn.card_vert_le_card_edgeSet_add_one
    have hsize : G.edgeFinset.card + 1 = Fintype.card V := by omega
    have htree : G.IsTree :=
      (SimpleGraph.isTree_iff_connected_and_card (G := G)).mpr
        ⟨hconn, by
          simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using hsize⟩
    let M := G.adjMatrix (ZMod 2)
    let A := M.mulVecLin
    let K := LinearMap.ker A
    have hrows (x : K) (u : V) : (∑ w ∈ G.neighborFinset u, x.1 w) = 0 := by
      have hx : A x.1 = 0 := LinearMap.mem_ker.mp x.property
      have h := congrFun hx u
      simpa only [A, M, Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
        Pi.zero_apply] using h
    have hneighbors (x : K) {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) :
        x.1 v = x.1 w := by
      by_cases hvw : v = w
      · exact congrArg x.1 hvw
      have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          SimpleGraph.mem_neighborFinset]
        exact ⟨huv, huw⟩
      have hcard : (G.neighborFinset u).card ≤ ({v, w} : Finset V).card := by
        rw [G.card_neighborFinset_eq_degree]
        simpa [hvw] using hdeg u
      have he : ({v, w} : Finset V) = G.neighborFinset u :=
        Finset.eq_of_subset_of_card_le hsub hcard
      have hsum : x.1 v + x.1 w = 0 := by
        simpa only [← he, Finset.sum_pair hvw] using hrows x u
      have hneg : x.1 v = -x.1 w := eq_neg_of_add_eq_zero_left hsum
      simpa only [ZMod.neg_eq_self_mod_two] using hneg
    have hprop (x : K) {u w : V} (q : G.Walk u w) :
        ∀ z, G.Adj z u → x.1 z = 0 → x.1 u = 0 → x.1 w = 0 := by
      induction q with
      | nil =>
        intro z hz hz0 hu0
        exact hu0
      | @cons u t w hut q ih =>
        intro z hzu hz0 hu0
        exact ih u hut hu0 ((hneighbors x hzu.symm hut).symm.trans hz0)
    have hzero (x : K) (hx : x.1 a = 0) : x = 0 := by
      by_cases ha0 : G.degree a = 0
      · apply Subtype.ext
        funext w
        have haw : a = w := by
          by_contra hne
          exact SimpleGraph.not_reachable_of_left_degree_zero hne ha0 (hconn a w)
        subst w
        exact hx
      · have ha1 : G.degree a = 1 := by omega
        obtain ⟨b, hnb⟩ := Finset.card_eq_one.mp
          (show (G.neighborFinset a).card = 1 from by
            rw [G.card_neighborFinset_eq_degree, ha1])
        have hab : G.Adj a b := by
          apply (G.mem_neighborFinset a b).mp
          rw [hnb]
          exact Finset.mem_singleton_self b
        have hb : x.1 b = 0 := by
          simpa only [hnb, Finset.sum_singleton] using hrows x a
        apply Subtype.ext
        funext w
        exact hprop x (hconn b w).some a hab hx hb
    let S : K →ₗ[ZMod 2] (ZMod 2) := (LinearMap.proj a).domRestrict K
    have hSi : Function.Injective S := by
      intro x y hxy
      have h : x.1 a = y.1 a := by
        simpa [S, LinearMap.proj_apply] using hxy
      apply sub_eq_zero.mp
      apply hzero (x - y)
      change x.1 a - y.1 a = 0
      exact sub_eq_zero.mpr h
    have hle1 : Module.finrank (ZMod 2) K ≤ 1 := by
      simpa only [CommSemiring.finrank_self] using
        LinearMap.finrank_le_finrank_of_injective hSi
    obtain ⟨c⟩ := htree.colorable_two
    let s : Finset V := Finset.univ.filter (fun v => c v = 0)
    let t : Finset V := sᶜ
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
    have hn : 2 * B.rank + Module.finrank (ZMod 2) K = Fintype.card V := by
      simpa only [hArank, Module.finrank_fintype_fun_eq_card] using
        LinearMap.finrank_range_add_finrank_ker A
    have hnR : (2 : ℝ) * (B.rank : ℝ) +
        (Module.finrank (ZMod 2) K : ℝ) = (Fintype.card V : ℝ) := by
      exact_mod_cast hn
    have hk0 : (0 : ℝ) ≤ (Module.finrank (ZMod 2) K : ℝ) := Nat.cast_nonneg _
    have hle1R : (Module.finrank (ZMod 2) K : ℝ) ≤ 1 := by
      exact_mod_cast hle1
    have hfloor : Int.floor ((Fintype.card V : ℝ) / 2) = (B.rank : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> push_cast <;> linarith only [hnR, hk0, hle1R]
    have hsizeR : (G.edgeFinset.card : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast hsize
    have hcorrection : (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ) + 1 = 0 := by
      linarith only [hsizeR]
    change (Module.finrank (ZMod 2) K : ℝ) = _
    rw [hcorrection]
    simp only [mul_zero, zero_mul, add_zero]
    rw [hfloor]
    push_cast
    linarith only [hnR]

theorem model_9d72068d4e2555d140e4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.IsAcyclic) ∧ ((G.maxDegree : ℝ) ≤ (20000001 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (G.edgeFinset.card : ℝ)) ≤ (Fintype.card V : ℝ) := by
  classical
  have hrow :
      ∀ (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj]
        (S : Set W) [DecidablePred (fun w => w ∈ S)]
        (x : W → ZMod 2) (z : S),
        (∀ w : W, w ∉ S → H.adjMatrix (ZMod 2) (z : W) w * x w = 0) →
        ((H.induce S).adjMatrix (ZMod 2)).mulVecLin (fun w : S => x (w : W)) z =
          (H.adjMatrix (ZMod 2)).mulVecLin x (z : W) := by
    intro W _ _ H _ S _ x z hz
    change (∑ w : S, (H.induce S).adjMatrix (ZMod 2) z w * x (w : W)) =
      ∑ w : W, H.adjMatrix (ZMod 2) (z : W) w * x w
    symm
    apply Finset.sum_congr_set S
    · intro w hw
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.induce_adj]
    · exact hz
  have haux :
      ∀ (n : ℕ) (W : Type _) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj],
        Fintype.card W = n → H.IsAcyclic → (∀ w, H.degree w ≤ 2) →
        Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) +
          H.edgeFinset.card ≤ Fintype.card W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H _ hcard hac hdeg
      by_cases hadj : ∃ a b : W, H.Adj a b
      · obtain ⟨a, b, hab⟩ := hadj
        letI : Nonempty W := ⟨a⟩
        obtain ⟨u, z, p, hp, hmax⟩ :=
          SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
        have hnil : ¬ p.Nil := by
          intro hn
          have hh := hmax a b (SimpleGraph.Walk.cons hab .nil) (by simp [hab.ne])
          have hzero : p.length = 0 := hn.length_eq_zero
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, hzero] at hh
          omega
        let v : W := p.snd
        have huv : H.Adj u v := p.adj_snd hnil
        have hleaf (w : W) (hw : H.Adj u w) : w = v := by
          apply hac.eq_snd_of_adj_start hp hw
          by_contra hnot
          have hpath : (p.cons hw.symm).IsPath := hp.cons hnot
          have hh := hmax w z (p.cons hw.symm) hpath
          simp only [SimpleGraph.Walk.length_cons] at hh
          omega
        have hnu : H.neighborFinset u = {v} := by
          ext w
          constructor
          · intro hw
            exact Finset.mem_singleton.mpr
              (hleaf w ((H.mem_neighborFinset u w).mp hw))
          · intro hw
            have hwv : w = v := Finset.mem_singleton.mp hw
            rw [hwv]
            exact (H.mem_neighborFinset u v).mpr huv
        let W1 := ↥(({v} : Set W)ᶜ)
        let H1 : SimpleGraph W1 := H.induce ({v} : Set W)ᶜ
        let u1 : W1 := ⟨u, by simpa using huv.ne⟩
        let W2 := ↥(({u1} : Set W1)ᶜ)
        let H2 : SimpleGraph W2 := H1.induce ({u1} : Set W1)ᶜ
        have hnone (w : W1) : ¬ H1.Adj u1 w := by
          intro hw
          have heq : (w : W) = v := hleaf (w : W) hw
          exact w.property (Set.mem_singleton_iff.mpr heq)
        have hu1deg : H1.degree u1 = 0 := by
          rw [← H1.card_neighborFinset_eq_degree u1]
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro w hw
          exact hnone w ((H1.mem_neighborFinset u1 w).mp hw)
        have hc1 : Fintype.card W1 = Fintype.card W - 1 := by
          dsimp only [W1]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hc2 : Fintype.card W2 = Fintype.card W1 - 1 := by
          dsimp only [W2]
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos1 : 0 < Fintype.card W1 := Fintype.card_pos_iff.mpr ⟨u1⟩
        have hcards : Fintype.card W2 + 2 = Fintype.card W := by omega
        have hlt : Fintype.card W2 < n := by omega
        let K := LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin
        let K2 := LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin
        have hxv (x : K) : (x : W → ZMod 2) v = 0 := by
          have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
            x.property
          have hh := congrFun hxA u
          simpa only [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply,
            hnu, Finset.sum_singleton, Pi.zero_apply] using hh
        have hres (x : K) :
            (H2.adjMatrix (ZMod 2)).mulVecLin
              (fun w : W2 => (x : W → ZMod 2) w.val.val) = 0 := by
          funext w
          have hz1 (j : W) (hj : j ∉ ({v} : Set W)ᶜ) :
              H.adjMatrix (ZMod 2) w.val.val j * (x : W → ZMod 2) j = 0 := by
            have heq : j = v := by simpa using hj
            subst j
            rw [hxv x, mul_zero]
          have hz2 (j : W1) (hj : j ∉ ({u1} : Set W1)ᶜ) :
              H1.adjMatrix (ZMod 2) w.val j * (x : W → ZMod 2) j.val = 0 := by
            have heq : j = u1 := by simpa using hj
            subst j
            have hn : ¬ H1.Adj w.val u1 := fun h => hnone w.val h.symm
            change (if H1.Adj w.val u1 then (1 : ZMod 2) else 0) *
              (x : W → ZMod 2) (u1 : W) = 0
            rw [if_neg hn, zero_mul]
          calc
            (H2.adjMatrix (ZMod 2)).mulVecLin
                (fun j : W2 => (x : W → ZMod 2) j.val.val) w =
                (H1.adjMatrix (ZMod 2)).mulVecLin
                  (fun j : W1 => (x : W → ZMod 2) j.val) w.val :=
              hrow W1 H1 ({u1} : Set W1)ᶜ
                (fun j : W1 => (x : W → ZMod 2) j.val) w hz2
            _ = (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) w.val.val :=
              hrow W H ({v} : Set W)ᶜ (x : W → ZMod 2) w.val hz1
            _ = 0 := congrFun
              (show (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 from
                x.property) w.val.val
        let R : K →ₗ[ZMod 2] K2 :=
          { toFun := fun x => ⟨fun w => (x : W → ZMod 2) w.val.val, hres x⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              rfl
            map_smul' := by
              intro c x
              apply Subtype.ext
              rfl }
        have hRinj : Function.Injective R := by
          have hzero (x : K) (hx : R x = 0) : x = 0 := by
            have hrest (j : W) (hju : j ≠ u) (hjv : j ≠ v) :
                (x : W → ZMod 2) j = 0 := by
              let j1 : W1 := ⟨j, by simpa using hjv⟩
              let j2 : W2 := ⟨j1, by
                change j1 ≠ u1
                intro heq
                exact hju (congrArg (fun t : W1 => (t : W)) heq)⟩
              have hh := congrArg (fun t : K2 => (t : W2 → ZMod 2) j2) hx
              change (x : W → ZMod 2) j = 0 at hh
              exact hh
            have hxu : (x : W → ZMod 2) u = 0 := by
              have hxA : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) = 0 :=
                x.property
              have hr : (H.adjMatrix (ZMod 2)).mulVecLin (x : W → ZMod 2) v =
                  (x : W → ZMod 2) u := by
                rw [Matrix.mulVecLin_apply, SimpleGraph.adjMatrix_mulVec_apply]
                apply Finset.sum_eq_single u
                · intro j hj hju
                  by_cases hjv : j = v
                  · simpa only [hjv] using hxv x
                  · exact hrest j hju hjv
                · intro hnot
                  exact (hnot ((H.mem_neighborFinset v u).mpr huv.symm)).elim
              exact hr.symm.trans (congrFun hxA v)
            apply Subtype.ext
            funext j
            change (x : W → ZMod 2) j = 0
            by_cases hju : j = u
            · simpa only [hju] using hxu
            by_cases hjv : j = v
            · simpa only [hjv] using hxv x
            exact hrest j hju hjv
          intro x y hxy
          apply sub_eq_zero.mp
          apply hzero
          rw [map_sub, hxy, sub_self]
        have hdim : Module.finrank (ZMod 2) K ≤ Module.finrank (ZMod 2) K2 :=
          LinearMap.finrank_le_finrank_of_injective hRinj
        change Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) ≤
          Module.finrank (ZMod 2) (LinearMap.ker (H2.adjMatrix (ZMod 2)).mulVecLin) at hdim
        have hdeg2 (w : W2) : H2.degree w ≤ 2 := by
          calc
            H2.degree w ≤ H1.degree w.val :=
              (SimpleGraph.Copy.induce H1 ({u1} : Set W1)ᶜ).degree_le w
            _ ≤ H.degree w.val.val :=
              (SimpleGraph.Copy.induce H ({v} : Set W)ᶜ).degree_le w.val
            _ ≤ 2 := hdeg w.val.val
        have hI := ih (Fintype.card W2) hlt W2 H2 rfl
          ((hac.induce ({v} : Set W)ᶜ).induce ({u1} : Set W1)ᶜ) hdeg2
        have hm1 : H1.edgeFinset.card = H.edgeFinset.card - H.degree v := by
          dsimp only [H1]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet]
        have hm2 : H2.edgeFinset.card = H1.edgeFinset.card := by
          dsimp only [H2]
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet, hu1deg, Nat.sub_zero]
        have hdv := hdeg v
        have hem := H.degree_le_card_edgeFinset v
        omega
      · have hbot : H = ⊥ := by
          apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
          intro a b hab
          exact hadj ⟨a, b, hab⟩
        have hm : H.edgeFinset.card = 0 := by simp [hbot]
        rw [hm, Nat.add_zero]
        calc
          _ ≤ Module.finrank (ZMod 2) (W → ZMod 2) := Submodule.finrank_le _
          _ = Fintype.card W := Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hmax : G.maxDegree ≤ 2 := by
    by_contra h
    have hh : 3 ≤ G.maxDegree := by omega
    have hhR : (3 : ℝ) ≤ (G.maxDegree : ℝ) := by exact_mod_cast hh
    linarith only [h_guard.2.1, hhR]
  have h := haux (Fintype.card V) V G rfl h_guard.1
    (fun v => (G.degree_le_maxDegree v).trans hmax)
  exact_mod_cast h

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

theorem model_63cbbf2849b9c52dbcc9 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : ((G.Connected) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)))) :
    (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤ ((((2 : ℝ) * (Gᶜ.cliqueNum : ℝ)) - (Fintype.card V : ℝ)) + ((2 : ℝ) * (((G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)) + (1 : ℝ)))) := by
  classical
  obtain ⟨T, hTG, hT⟩ := h_guard.1.exists_isTree_le
  let d : Finset (Sym2 V) := G.edgeFinset \ T.edgeFinset
  let r : Finset V := d.image (fun e : Sym2 V => e.out.1)
  let s : Finset V := rᶜ
  let H : SimpleGraph s := G.induce (s : Set V)
  have hTcard : T.edgeFinset.card + 1 = Fintype.card V :=
    hT.card_edgeFinset
  have hdcard : d.card + T.edgeFinset.card = G.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hTG)
  have hrcard : r.card ≤ d.card := Finset.card_image_le
  have hscard : s.card + r.card = Fintype.card V :=
    Finset.card_compl_add_card r
  have hremoved : r.card + Fintype.card V ≤ G.edgeFinset.card + 1 := by
    omega
  have hle : H ≤ T.induce (s : Set V) := by
    intro u v huv
    change G.Adj (u : V) (v : V) at huv
    change T.Adj (u : V) (v : V)
    by_contra hn
    have hmem : s((u : V), (v : V)) ∈ d := by
      simp only [d, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨huv, hn⟩
    have hout : (s((u : V), (v : V))).out.1 ∈ r :=
      Finset.mem_image.mpr ⟨s((u : V), (v : V)), hmem, rfl⟩
    have hends : (s((u : V), (v : V))).out.1 = (u : V) ∨
        (s((u : V), (v : V))).out.1 = (v : V) :=
      Sym2.mem_iff.mp (Sym2.out_fst_mem _)
    rcases hends with hu | hv
    · have hun : (u : V) ∉ r := Finset.mem_compl.mp u.property
      exact hun (hu ▸ hout)
    · have hvn : (v : V) ∉ r := Finset.mem_compl.mp v.property
      exact hvn (hv ▸ hout)
  have hforest : H.IsAcyclic :=
    SimpleGraph.IsAcyclic.anti hle (hT.isAcyclic.induce (s : Set V))
  have hcompl : Hᶜ = (Gᶜ).induce (s : Set V) := by
    ext u v
    simp only [H, SimpleGraph.compl_adj, SimpleGraph.induce_adj,
      ne_eq, Subtype.val_inj]
  have hclique : Hᶜ.cliqueNum ≤ Gᶜ.cliqueNum := by
    rw [hcompl]
    exact (Gᶜ).cliqueNum_induce_le (s : Set V)
  have hmatrix : (G.adjMatrix (ZMod 2)).submatrix
      (fun v : s => (v : V)) (fun v : s => (v : V)) =
      H.adjMatrix (ZMod 2) := by
    ext u v
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
      H, SimpleGraph.induce_adj]
  have hrank : (H.adjMatrix (ZMod 2)).rank ≤
      (G.adjMatrix (ZMod 2)).rank := by
    have h := Matrix.rank_submatrix_le (G.adjMatrix (ZMod 2))
      (fun v : s => (v : V)) (fun v : s => (v : V))
    rw [hmatrix] at h
    exact h
  have hdimG : (G.adjMatrix (ZMod 2)).rank +
      Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) =
      Fintype.card V := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_range_add_finrank_ker (G.adjMatrix (ZMod 2)).mulVecLin
  have hdimH : (H.adjMatrix (ZMod 2)).rank +
      Module.finrank (ZMod 2) (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) =
      s.card := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] using
      LinearMap.finrank_range_add_finrank_ker (H.adjMatrix (ZMod 2)).mulVecLin
  have hker : Module.finrank (ZMod 2)
      (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) ≤
      Module.finrank (ZMod 2)
        (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) + r.card := by
    omega
  have hkerR : (Module.finrank (ZMod 2)
      (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤
      (Module.finrank (ZMod 2)
        (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) : ℝ) + (r.card : ℝ) := by
    exact_mod_cast hker
  have hforestBound : (Module.finrank (ZMod 2)
      (LinearMap.ker (H.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≤
      (2 : ℝ) * (Hᶜ.cliqueNum : ℝ) - (s.card : ℝ) := by
    simpa only [Fintype.card_coe] using model_fcf51e36faf8ebb9be9b H hforest
  have hcliqueR : (Hᶜ.cliqueNum : ℝ) ≤ (Gᶜ.cliqueNum : ℝ) := by
    exact_mod_cast hclique
  have hremovedR : (r.card : ℝ) + (Fintype.card V : ℝ) ≤
      (G.edgeFinset.card : ℝ) + 1 := by
    exact_mod_cast hremoved
  have hscardR : (s.card : ℝ) + (r.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hscard
  linarith only [hkerR, hforestBound, hcliqueR, hremovedR, hscardR]
theorem model_cfda7a879c33977862b8 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h_guard : (((G.minDegree : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((G.maxDegree : ℝ) ≥ (19999999 / 10000000 : ℝ)) ∧ ((Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ) ≥ (9999999 / 10000000 : ℝ)) ∧ ((let weights : Finset ℕ := {Fintype.card V + 1} ∪ ((Finset.univ : Finset (Finset V)).filter (fun S => S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧ ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card; ((weights.min' (by simp [weights]) - 1 : ℕ) : ℝ)) ≥ (19999999 / 10000000 : ℝ)))) :
    (((G.minDegree : ℝ) + (1 : ℝ)) * (Module.finrank (ZMod 2) (LinearMap.ker (G.adjMatrix (ZMod 2)).mulVecLin) : ℝ)) ≤ (((2 : ℝ) * (G.edgeFinset.card : ℝ)) - (Fintype.card V : ℝ)) := by
  classical
  let weights : Finset ℕ := {Fintype.card V + 1} ∪
    ((Finset.univ : Finset (Finset V)).filter (fun S =>
      S.Nonempty ∧ ¬ (∃ v w, w ∈ S ∧ G.Adj v w ∧
        ∀ u ∈ S, G.Adj v u → u = w))).image Finset.card
  have hw : weights.Nonempty := by simp [weights]
  have hradius : 2 ≤ weights.min' hw - 1 := by
    have hg := h_guard.2.2.2
    change (((weights.min' hw - 1 : ℕ) : ℝ)) ≥
      (19999999 / 10000000 : ℝ) at hg
    have hh : (1 : ℝ) < ((weights.min' hw - 1 : ℕ) : ℝ) := by
      linarith only [hg]
    have hh' : 1 < weights.min' hw - 1 := by exact_mod_cast hh
    omega
  have hunique (U : Finset V) (hU : U.Nonempty) (hc : U.card ≤ 2) :
      ∃ v w, w ∈ U ∧ G.Adj v w ∧ ∀ u ∈ U, G.Adj v u → u = w := by
    by_contra h
    have hm : U.card ∈ weights := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ U, hU, h⟩, rfl⟩
    have hmin : weights.min' hw ≤ U.card := Finset.min'_le weights U.card hm
    omega
  let M : Matrix V V (ZMod 2) := G.adjMatrix (ZMod 2)
  let r : ℕ := Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2) (Set.range M.col))
  let k : ℕ := Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin)
  obtain ⟨f, hf, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (Set.range M.col)
  choose a ha using hf
  have hspan' : Submodule.span (ZMod 2) (Set.range (M.col ∘ a)) =
      Submodule.span (ZMod 2) (Set.range M.col) := by
    have hfun : M.col ∘ a = f := by
      funext i
      exact ha i
    rw [hfun]
    exact hspan
  have hai : Function.Injective a := by
    intro i j hij
    apply hli.injective
    rw [← ha i, ← ha j, hij]
  let S : Finset V := Finset.univ.image a
  have hScard : S.card = r := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hai]
    simp only [Finset.card_univ, Fintype.card_fin, r]
  have haS (i : Fin r) : a i ∈ S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hspanzero (l : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (hl : ∀ i : Fin r, l (M.col (a i)) = 0) (w : V) : l (M.col w) = 0 := by
    have hs : Submodule.span (ZMod 2) (Set.range (M.col ∘ a)) ≤
        LinearMap.ker l := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hl i
    have hm : M.col w ∈ Submodule.span (ZMod 2) (Set.range (M.col ∘ a)) := by
      rw [hspan']
      exact Submodule.subset_span ⟨w, rfl⟩
    exact hs hm
  have hentry (v w : V) : M.col w v = 0 ↔ ¬ G.Adj v w := by
    by_cases h : G.Adj v w <;>
      simp [M, Matrix.col_apply, SimpleGraph.adjMatrix_apply, h]
  let N (v : V) : Finset V := S.filter (G.Adj v)
  have hNne (v : V) : (N v).Nonempty := by
    by_contra hn
    have hbase (i : Fin r) : M.col (a i) v = 0 := by
      apply (hentry v (a i)).mpr
      intro h
      exact hn ⟨a i, Finset.mem_filter.mpr ⟨haS i, h⟩⟩
    obtain ⟨z, w, hmem, hzw, _⟩ := hunique ({v} : Finset V) (by simp) (by simp)
    have hwv : w = v := Finset.mem_singleton.mp hmem
    subst w
    have hz : M.col z v = 0 := hspanzero (LinearMap.proj v) hbase z
    exact ((hentry v z).mp hz) hzw.symm
  have hNi : Function.Injective N := by
    intro v w hvw
    have hbase (i : Fin r) : M.col (a i) v - M.col (a i) w = 0 := by
      have hmem : a i ∈ N v ↔ a i ∈ N w := by rw [hvw]
      have hiff : G.Adj v (a i) ↔ G.Adj w (a i) := by
        simpa only [N, Finset.mem_filter, haS i, true_and] using hmem
      apply sub_eq_zero.mpr
      simp only [M, Matrix.col_apply, SimpleGraph.adjMatrix_apply]
      simp only [hiff]
    have hrows (z : V) : G.Adj z v ↔ G.Adj z w := by
      let l : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun x => x v - x w
          map_add' := by
            intro x y
            change (x v + y v) - (x w + y w) = (x v - x w) + (y v - y w)
            abel
          map_smul' := by
            intro c x
            change c * x v - c * x w = c * (x v - x w)
            exact (mul_sub c (x v) (x w)).symm }
      have hz : M.col z v - M.col z w = 0 := hspanzero l hbase z
      have he : M.col z v = M.col z w := sub_eq_zero.mp hz
      have hniff : ¬ G.Adj v z ↔ ¬ G.Adj w z := by
        rw [← hentry v z, ← hentry w z, he]
      exact (G.adj_comm z v).trans
        ((not_iff_not.mp hniff).trans (G.adj_comm w z))
    by_contra hne
    obtain ⟨z, t, ht, hzt, hu⟩ :=
      hunique ({v, w} : Finset V) (by simp) (by simp [hne])
    rcases (show t = v ∨ t = w by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ht) with rfl | rfl
    · exact hne (hu w (by simp) ((hrows z).mp hzt)).symm
    · exact hne (hu v (by simp) ((hrows z).mpr hzt))
  let L : Finset V := Finset.univ.filter (fun v => (N v).card = 1)
  have hLcard : L.card ≤ S.card := by
    calc
      L.card = (L.image N).card := (Finset.card_image_of_injective L hNi).symm
      _ ≤ (S.image (fun v : V => ({v} : Finset V))).card := by
        apply Finset.card_le_card
        intro U hU
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
        have hv1 : (N v).card = 1 := (Finset.mem_filter.mp hv).2
        obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hv1
        have hum : u ∈ N v := by
          rw [hu]
          exact Finset.mem_singleton_self u
        have hus : u ∈ S := (Finset.mem_filter.mp hum).1
        exact Finset.mem_image.mpr ⟨u, hus, hu.symm⟩
      _ ≤ S.card := Finset.card_image_le
  have hsmall : (∑ v ∈ L, (N v).card) = L.card := by
    calc
      _ = ∑ _v ∈ L, (1 : ℕ) := Finset.sum_congr rfl
        (fun v hv => (Finset.mem_filter.mp hv).2)
      _ = L.card := by simp
  have hlarge : 2 * (Lᶜ).card ≤ ∑ v ∈ Lᶜ, (N v).card := by
    calc
      2 * (Lᶜ).card = ∑ _v ∈ Lᶜ, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ Lᶜ, (N v).card := by
        apply Finset.sum_le_sum
        intro v hv
        have hp : 0 < (N v).card := Finset.card_pos.mpr (hNne v)
        have hn : (N v).card ≠ 1 := by
          intro h
          exact (Finset.mem_compl.mp hv)
            (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
        omega
  have hcount : 2 * Fintype.card V ≤ (∑ v : V, (N v).card) + S.card := by
    have hsplit := Finset.sum_add_sum_compl L (fun v => (N v).card)
    have hcards := Finset.card_compl_add_card L
    omega
  have hsumN : (∑ v : V, (N v).card) = ∑ u ∈ S, G.degree u := by
    calc
      _ = ∑ v : V, ∑ u ∈ S, if G.Adj v u then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        change (S.filter (G.Adj v)).card = _
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = ∑ u ∈ S, ∑ v : V, if G.Adj v u then (1 : ℕ) else 0 :=
        Finset.sum_comm
      _ = ∑ u ∈ S, G.degree u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [← G.card_neighborFinset_eq_degree u, G.neighborFinset_eq_filter,
          Finset.card_eq_sum_ones, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v _
        simp only [G.adj_comm v u]
  have hr : r + k = Fintype.card V := by
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at h
    exact h
  have hSc : (Sᶜ).card = k := by
    have h := Finset.card_compl_add_card S
    rw [hScard] at h
    omega
  have hcomp : G.minDegree * k ≤ ∑ v ∈ Sᶜ, G.degree v := by
    calc
      G.minDegree * k = ∑ _v ∈ Sᶜ, G.minDegree := by simp [hSc, Nat.mul_comm]
      _ ≤ ∑ v ∈ Sᶜ, G.degree v :=
        Finset.sum_le_sum (fun v _ => G.minDegree_le_degree v)
  have hn : (G.minDegree + 1) * k + Fintype.card V ≤ 2 * G.edgeFinset.card := by
    have hsplit := Finset.sum_add_sum_compl S (fun v => G.degree v)
    rw [G.sum_degrees_eq_twice_card_edges] at hsplit
    rw [hsumN, hScard] at hcount
    rw [add_mul, one_mul]
    omega
  have hnR : ((G.minDegree : ℝ) + 1) * (k : ℝ) + (Fintype.card V : ℝ) ≤
      (2 : ℝ) * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hn
  change ((G.minDegree : ℝ) + 1) * (k : ℝ) ≤
    (2 : ℝ) * (G.edgeFinset.card : ℝ) - (Fintype.card V : ℝ)
  linarith only [hnR]
