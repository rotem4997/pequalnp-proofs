import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators Sym2

-- The dense-reader case is the checked single-input deletion bound L-meta-1743.
-- The live-wire count follows the argument in L-meta-1975.
-- After pinning one vertex, the second deletion avoids its three deficient neighbors.
theorem PEqualNP.Outside.R_meta_3997_1
    (dense : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (v : Fin n),
      FanInTwo C → circuitFun n C = f →
      (∀ k, HasCircuitSize n f k → C.size ≤ k) →
      (∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) →
      (let readers := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
       4 ≤ readers.length ∨ readers.length = 3 ∧ ∃ g ∈ readers, g.op ≠ .or) →
      ∃ t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (live : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      ∀ j : ℕ, j < C.gates.length → n + j ∈ C.output :: C.gates.flatMap Gate.inputs)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit),
      30 ≤ n → G.Colorable 2 → (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      circuitFun n C = f → IsMinimalCircuit n C → C.size + 1 < 2 * n →
      (∀ v : Fin n, let readers := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = .or)) →
      (∃ v : Fin n, (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      ∃ v t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (nextPin : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (z : Fin n) (T : Set (Fin n))
      (f : (Fin n → Bool) → Bool),
      30 ≤ n → Even n → H.Colorable 2 →
      (∀ v (w : H.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (H.neighborSet z).ncard = 0 → T.ncard = 3 → z ∉ T →
      (∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∀ p : H.Walk a b, p.IsPath → 5 ≤ p.length) →
      (∀ v ∈ T, (H.neighborSet v).ncard = 2) →
      (∀ v, v ≠ z → v ∉ T → (H.neighborSet v).ncard = 3) →
      (∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      ∀ s, s + 5 < 2 * n → HasCircuitSize n f s →
      ∃ v, v ≠ z ∧ v ∉ T ∧ ∃ t, t + 4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  classical
  intro n G f hn heven hcolor hdeg hgirth hedge hfun s hs hsize
  have sizes : ∃ m, HasCircuitSize n f m := ⟨s, hsize⟩
  obtain ⟨C, hfan, hsmall, hc⟩ := Nat.find_spec sizes
  have hcomp : circuitFun n C = f := funext hc
  have hmin (m : ℕ) (hm : HasCircuitSize n f m) : C.size ≤ m :=
    hsmall.trans (Nat.find_min' sizes hm)
  have hminimal : IsMinimalCircuit n C := by
    refine ⟨hfan, fun D hD heq => hmin D.size ⟨D, hD, le_rfl, ?_⟩⟩
    intro x
    exact congrFun (heq.trans hcomp) x
  have hbudget := hmin s hsize
  let reads (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  have nonconstant (z : Fin n) :
      ∃ x y, f (Function.update x z false) ≠ f (Function.update y z false) := by
    obtain ⟨a, b, hab⟩ := hedge
    obtain ⟨u, hu⟩ : ∃ u, u ≠ z := by
      by_cases ha : a = z
      · exact ⟨b, fun hb => hab.ne (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    obtain ⟨v, hv, huv⟩ : ∃ v, v ≠ z ∧ G.Adj u v := by
      by_contra h
      have sub : G.neighborSet u ⊆ ({z} : Set (Fin n)) := by
        intro w hw
        by_contra hwz
        exact h ⟨w, fun e => hwz (Set.mem_singleton_iff.mpr e), hw⟩
      have bound := Set.ncard_le_ncard sub
      rw [hdeg, Set.ncard_singleton] at bound
      omega
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have one : f (Function.update (fun _ => true) z false) = true :=
      (hfun _).mpr ⟨u, v, huv, by simp [Function.update_of_ne hu], by
        simp [Function.update_of_ne hv]⟩
    rw [one]
    intro h
    obtain ⟨i, _, _, hi, _⟩ := (hfun _).mp h
    by_cases hix : i = z
    · simp [hix] at hi
    · simp [Function.update_of_ne hix] at hi
  have fewReaders : ∃ v : Fin n, (reads v).length ≤ 1 := by
    by_contra none
    have atLeastTwo (v : Fin n) : 2 ≤ (reads v).length := by
      have h : ¬ (reads v).length ≤ 1 := fun h => none ⟨v, h⟩
      omega
    let gateReads (v : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
    have filterCount (v : ℕ) (gs : List Gate) :
        (gs.filter (gateReads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons, List.count_append, List.filter_cons]
        split
        next hv =>
          have mem : v ∈ g.inputs :=
            List.mem_of_mem_take (List.contains_iff_mem.mp hv)
          have positive := List.count_pos_iff.mpr mem
          simp only [List.length_cons]
          omega
        next => omega
    have gateSlots (gs : List Gate) (good : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have gh := good g List.mem_cons_self
        have th := ih (fun e he => good e (List.mem_cons_of_mem g he))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have sumCount (xs : List ℕ) (S : Finset ℕ) : ∑ i ∈ S, xs.count i ≤ xs.length := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        by_cases ha : a ∈ S <;> simp [ha, Finset.sum_ite_eq] <;> omega
    let slots := C.output :: C.gates.flatMap Gate.inputs
    have inputUse : 2 * n ≤ ∑ i ∈ Finset.range n, slots.count i := by
      calc
        2 * n = ∑ _i ∈ Finset.range n, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ i ∈ Finset.range n, slots.count i := by
          apply Finset.sum_le_sum
          intro i hi
          have hf := filterCount i C.gates
          have hr := atLeastTwo ⟨i, Finset.mem_range.mp hi⟩
          change 2 ≤ (C.gates.filter (gateReads i)).length at hr
          simp only [slots, List.count_cons]
          omega
    have gateUse : C.gates.length ≤ ∑ i ∈ Finset.range C.gates.length, slots.count (n + i) := by
      calc
        C.gates.length = ∑ _i ∈ Finset.range C.gates.length, (1 : ℕ) := by simp
        _ ≤ ∑ i ∈ Finset.range C.gates.length, slots.count (n + i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact List.count_pos_iff.mpr (live n C hminimal i (Finset.mem_range.mp hi))
    have countTotal := sumCount slots (Finset.range (n + C.gates.length))
    rw [Finset.sum_range_add] at countTotal
    have slotLength : slots.length = (C.gates.flatMap Gate.inputs).length + 1 := rfl
    rw [slotLength] at countTotal
    have lengthBound := gateSlots C.gates (fun g hg => (hfan g hg).2)
    change C.gates.length ≤ s at hbudget
    omega
  have firstPin : ∃ v k, k + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) k := by
    by_cases ht : ∃ v : Fin n, 4 ≤ (reads v).length ∨
        (reads v).length = 3 ∧ ∃ g ∈ reads v, g.op ≠ .or
    · obtain ⟨v, hv⟩ := ht
      obtain ⟨t, ht, hb⟩ := dense n f C v hfan hcomp hmin (nonconstant v) hv
      exact ⟨v, t, ht, hb⟩
    · apply sparse n G f C hn hcolor hdeg hgirth hfun hcomp hminimal (by omega)
      · intro v
        change (reads v).length ≤ 3 ∧ ((reads v).length = 3 → ∀ g ∈ reads v, g.op = .or)
        constructor
        · by_contra h
          exact ht ⟨v, Or.inl (by omega)⟩
        · intro h g hg
          by_contra he
          exact ht ⟨v, Or.inr ⟨h, g, hg, he⟩⟩
      · exact fewReaders
  obtain ⟨z, k, hk, hfirst⟩ := firstPin
  let H := G.deleteEdges (G.incidenceSet z)
  let T := G.neighborSet z
  let cofactor := fun x : Fin n → Bool => f (Function.update x z false)
  have hAdj (a b : Fin n) : H.Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z :=
    SimpleGraph.deleteIncidenceSet_adj
  have hsub : H ≤ G := SimpleGraph.deleteEdges_le _
  have hcycles (v : Fin n) (w : H.Walk v v) (cyc : w.IsCycle) : 7 ≤ w.length := by
    simpa using hgirth v (w.mapLe hsub) (cyc.mapLe hsub)
  have hzero : (H.neighborSet z).ncard = 0 := by
    have eq : H.neighborSet z = ∅ := by
      ext b
      change H.Adj z b ↔ False
      simp [hAdj]
    rw [eq]
    exact Set.ncard_empty (Fin n)
  have hneighbors (v : Fin n) (hv : v ≠ z) :
      H.neighborSet v = G.neighborSet v \ {z} := by
    ext b
    change H.Adj v b ↔ G.Adj v b ∧ b ∉ ({z} : Set (Fin n))
    simp [hAdj, hv]
  have hzn : z ∉ T := G.irrefl
  have avoids {a b : Fin n} (p : H.Walk a b) : a ≠ z → z ∉ p.support := by
    induction p with
    | nil =>
      intro ha
      simp [Ne.symm ha]
    | @cons a b c adj rest ih =>
      intro _
      obtain ⟨_, ha, hb⟩ := (hAdj a b).mp adj
      simpa [SimpleGraph.Walk.support_cons, Ne.symm ha] using ih hb
  have separated (a : Fin n) (ha : a ∈ T) (b : Fin n) (hb : b ∈ T)
      (hab : a ≠ b) (p : H.Walk a b) (hp : p.IsPath) : 5 ≤ p.length := by
    have haz : a ≠ z := fun h => hzn (h ▸ ha)
    have hza : G.Adj z a := ha
    have hzb : G.Adj z b := hb
    have missing : z ∉ (p.mapLe hsub).support := by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      exact avoids p haz
    let q := (p.mapLe hsub).concat hzb.symm
    have qpath : q.IsPath := (hp.mapLe hsub).concat missing hzb.symm
    have edgeAbsent : s(z,a) ∉ q.edges := by
      change s(z,a) ∉ ((p.mapLe hsub).concat hzb.symm).edges
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append]
      intro hm
      rcases List.mem_append.mp hm with old | last
      · exact missing ((p.mapLe hsub).fst_mem_support_of_mem_edges old)
      · have e := (Sym2.mk_eq_mk_iff (p := (z,a)) (q := (b,z))).mp (List.mem_singleton.mp last)
        rcases e with same | swapped
        · have bz : b = z := (congrArg Prod.fst same).symm
          exact hzn (bz ▸ hb)
        · exact hab (congrArg Prod.snd swapped)
    have cycle := (SimpleGraph.Walk.cons_isCycle_iff q hza).mpr ⟨qpath, edgeAbsent⟩
    have hlen := hgirth z _ cycle
    change 7 ≤ (SimpleGraph.Walk.cons hza ((p.mapLe hsub).concat hzb.symm)).length at hlen
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.length_mapLe] at hlen
    omega
  have hdegreeTwo (v : Fin n) (hv : v ∈ T) : (H.neighborSet v).ncard = 2 := by
    have ne : v ≠ z := fun eq => hzn (eq ▸ hv)
    have mem : z ∈ G.neighborSet v := G.adj_symm hv
    rw [hneighbors v ne, Set.ncard_sdiff_singleton_of_mem mem, hdeg v]
  have hdegreeThree (v : Fin n) (hv : v ≠ z) (hvn : v ∉ T) :
      (H.neighborSet v).ncard = 3 := by
    have eq : G.neighborSet v \ {z} = G.neighborSet v := by
      ext b
      change (G.Adj v b ∧ b ∉ ({z} : Set (Fin n))) ↔ G.Adj v b
      refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
      intro hb
      have e : b = z := Set.mem_singleton_iff.mp hb
      subst b
      exact hvn h.symm
    rw [hneighbors v hv, eq, hdeg v]
  have hcofactor (x : Fin n → Bool) :
      cofactor x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
    change f (Function.update x z false) = true ↔ _
    rw [hfun]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have haz : a ≠ z := by
        rintro rfl
        simp at ha
      have hbz : b ≠ z := by
        rintro rfl
        simp at hb
      exact ⟨a, b, (hAdj a b).2 ⟨hab, haz, hbz⟩,
        by simpa only [Function.update_of_ne haz] using ha,
        by simpa only [Function.update_of_ne hbz] using hb⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      obtain ⟨hab, haz, hbz⟩ := (hAdj a b).1 hab
      exact ⟨a, b, hab, by simpa only [Function.update_of_ne haz] using ha,
        by simpa only [Function.update_of_ne hbz] using hb⟩
  obtain ⟨v, hv, hvn, t, ht, hnext⟩ := nextPin n H z T cofactor hn heven
    (hcolor.mono_left hsub) hcycles hzero (hdeg z) hzn separated hdegreeTwo hdegreeThree hcofactor
    k (by omega) hfirst
  refine ⟨z, v, hv.symm, hvn, t, by omega, ?_⟩
  have exchange : (fun x => cofactor (Function.update x v false)) =
      (fun x => f (Function.update (Function.update x z false) v false)) := by
    funext x
    change f (Function.update (Function.update x v false) z false) = _
    rw [Function.update_comm hv.symm]
  exact exchange ▸ hnext
