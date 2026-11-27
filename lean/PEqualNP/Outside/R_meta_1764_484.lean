import Mathlib
import PEqualNP.Defs

-- The disjoint nonedge argument follows R_meta_1764_2.
-- Count small deletion sets by averaging over vertex subsets.
-- Thin the disjoint tests so their endpoints form one independent set.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_1764_484
    (h_slice : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (walk : G.Walk v v), walk.IsCycle → 5 ≤ walk.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (A : Finset (Fin n)) (D : Finset (Sym2 (Fin n))), D ⊆ G.edgeFinset →
      (∀ e ∈ D, ∃ u ∈ A, ∃ v ∈ A, e = s(u,v) ∧
        ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧
          ∀ p ∈ A, ∀ q ∈ A,
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q) →
      D.card ≤ C.size)
    (h_pack : ∃ m c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (walk : G.Walk v v), walk.IsCycle → 5 ≤ walk.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset,
        (∀ e ∈ T, ∀ u v : Fin n, e = s(u,v) → ∀ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v →
          let onPair := fun p q : Fin n => PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true
          let support (t : Fin n × Fin n) : Finset (Fin n) := {t.1, t.2}
          let outside := fun t : Fin n × Fin n => support t \ {u,v}
          onPair u u ∨ onPair v v ∨ ∃ F : Finset (Fin n × Fin n), F.card = m ∧
            (∀ t ∈ F, onPair t.1 t.2 ∧ ¬ G.Adj t.1 t.2) ∧
            (∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w)) ∧
            let vertices := F.biUnion support
            ∀ a ∈ vertices, ∀ b ∈ vertices, ¬ G.Adj a b) →
        T.card ≤ c*(C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  have orderedHomogeneous {α β : Type} [DecidableEq α] [DecidableEq β]
      [Fintype β] [Nonempty β] (color : α → α → β) (r : ℕ) (F : Finset α)
      (large : (Fintype.card β + 1) ^ (Fintype.card β * r) ≤ F.card) :
      ∃ c : β, ∃ L : List α, L.length = r ∧ L.Nodup ∧
        (∀ x ∈ L, x ∈ F) ∧ L.Pairwise (fun x y => color x y = c) := by
    let b := Fintype.card β
    let P (x y : α × β) : Prop := x.1 ≠ y.1 ∧ color x.1 y.1 = x.2
    have tagged : ∀ k : ℕ, ∀ S : Finset α, (b + 1) ^ k ≤ S.card →
        ∃ L : List (α × β), L.length = k ∧ (∀ x ∈ L, x.1 ∈ S) ∧ L.Pairwise P := by
      intro k
      induction k with
      | zero => exact fun _ _ => ⟨[], by simp⟩
      | succ k ih =>
        intro S enough
        have pos : 0 < (b + 1) ^ k := by positivity
        have notEmpty : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by positivity) enough)
        obtain ⟨x, hx⟩ := notEmpty
        have enoughErase : (Finset.univ : Finset β).card * ((b + 1) ^ k) ≤ (S.erase x).card := by
          have big := enough
          rw [pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_comm ((b + 1) ^ k) b] at big
          rw [Finset.card_univ, Finset.card_erase_of_mem hx]
          change b * (b + 1) ^ k ≤ S.card - 1
          omega
        obtain ⟨c, _, fiber⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
          (f := color x) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty enoughErase
        obtain ⟨L, len, mem, order⟩ := ih _ fiber
        refine ⟨(x, c) :: L, by simp [len], ?_, List.pairwise_cons.mpr ⟨?_, order⟩⟩
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hx
          · exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (mem _ hq)).1
        · intro q hq
          obtain ⟨hm, hc⟩ := Finset.mem_filter.mp (mem _ hq)
          exact ⟨(Finset.mem_erase.mp hm).1.symm, hc⟩
    obtain ⟨L, len, mem, order⟩ := tagged (b * r) F large
    have nd : L.Nodup := order.imp (fun h eq => h.1 (congrArg Prod.fst eq))
    have enough : (Finset.univ : Finset β).card * r ≤ L.toFinset.card := by
      rw [Finset.card_univ, List.toFinset_card_of_nodup nd, len]
    obtain ⟨c, _, fiber⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := Prod.snd) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty enough
    let H := L.filter (fun q => decide (q.2 = c))
    have many : r ≤ H.length := by
      rw [← List.toFinset_card_of_nodup (nd.filter _ : H.Nodup)]
      simpa [H, List.toFinset_filter] using fiber
    let K := H.take r
    have subH : ∀ q ∈ K, q ∈ H := fun _ hq => List.mem_of_mem_take hq
    have colH : ∀ q ∈ K, q.2 = c := fun _ hq => of_decide_eq_true (List.mem_filter.mp (subH _ hq)).2
    have memL : ∀ q ∈ K, q ∈ L := fun _ hq => (List.mem_filter.mp (subH _ hq)).1
    have pairK : K.Pairwise (fun x y => x.1 ≠ y.1 ∧ color x.1 y.1 = c) := by
      have pairSub : K.Pairwise P :=
        (order.filter (fun q : α × β => decide (q.2 = c))).take (i := r)
      apply pairSub.imp_of_mem
      intro x y hx _ hxy
      exact ⟨hxy.1, hxy.2.trans (colH x hx)⟩
    refine ⟨c, K.map Prod.fst, by simp [K, Nat.min_eq_left many], ?_, ?_, ?_⟩
    · exact List.pairwise_map.mpr (pairK.imp fun h => h.1)
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact mem q (memL q hq)
    · exact List.pairwise_map.mpr (pairK.imp fun h => h.2)

  have thin : ∀ m : ℕ, ∃ M : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 5 ≤ w.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), G.Adj u v → M ≤ F.card →
      (∀ t ∈ F, ¬ G.Adj t.1 t.2) →
      let support (t : Fin n × Fin n) : Finset (Fin n) := {t.1, t.2}
      let outside (t : Fin n × Fin n) : Finset (Fin n) := support t \ {u, v}
      (∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w)) →
      ∃ E ⊆ F, E.card = m ∧
        let vertices := E.biUnion support
        ∀ a ∈ vertices, ∀ b ∈ vertices, ¬ G.Adj a b := by
    classical
    intro m
    let r := max m 4
    refine ⟨4 * 6 ^ (5 * r), ?_⟩
    intro n G girth u v F _ enough independent
    dsimp only
    intro disjoint
    let support (t : Fin n × Fin n) : Finset (Fin n) := {t.1, t.2}
    let outside (t : Fin n × Fin n) : Finset (Fin n) := support t \ {u, v}
    let tag (t : Fin n × Fin n) : Bool × Bool :=
      (decide (u ∈ support t), decide (v ∈ support t))
    have tagCount : (Finset.univ : Finset (Bool × Bool)).card * 6 ^ (5 * r) ≤ F.card := by
      simpa [Fintype.card_prod] using enough
    obtain ⟨tagValue, _, tagFiber⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := tag) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty tagCount
    let T := F.filter (fun t => tag t = tagValue)
    have fixedEndpoint {a : Fin n} {t w : Fin n × Fin n} (same : tag t = tag w)
        (ht : a ∈ support t) (atEnd : a ∈ ({u, v} : Finset (Fin n))) : a ∈ support w := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at atEnd
      rcases atEnd with rfl | rfl
      · exact of_decide_eq_true ((congrArg Prod.fst same).symm.trans (decide_eq_true ht))
      · exact of_decide_eq_true ((congrArg Prod.snd same).symm.trans (decide_eq_true ht))
    have oneTest {t : Fin n × Fin n} (ht : t ∈ F) {a b : Fin n}
        (ha : a ∈ support t) (hb : b ∈ support t) : ¬ G.Adj a b := by
      change a ∈ ({t.1, t.2} : Finset (Fin n)) at ha
      change b ∈ ({t.1, t.2} : Finset (Fin n)) at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.loopless.irrefl _
      · exact independent t ht
      · exact fun h => independent t ht h.symm
      · exact G.loopless.irrefl _
    let vertex (t : Fin n × Fin n) (i : Fin 2) := if i = 0 then t.1 else t.2
    have ofSupport {a : Fin n} {t : Fin n × Fin n} (ha : a ∈ support t) :
        ∃ i : Fin 2, vertex t i = a := by
      simp only [support, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact ⟨0, by simp [vertex]⟩
      · exact ⟨1, by simp [vertex]⟩
    let cross (t w : Fin n × Fin n) (p : Fin 2 × Fin 2) : Prop :=
      vertex t p.1 ∈ outside t ∧ vertex w p.2 ∈ outside w ∧ G.Adj (vertex t p.1) (vertex w p.2)
    let pairs (t w : Fin n × Fin n) := (Finset.univ : Finset (Fin 2 × Fin 2)).filter (cross t w)
    let color (t w : Fin n × Fin n) : Option (Fin 2 × Fin 2) :=
      if h : (pairs t w).Nonempty then some (Classical.choose h) else none
    have positive {t w : Fin n × Fin n} {p : Fin 2 × Fin 2} (h : color t w = some p) : cross t w p := by
      by_cases hn : (pairs t w).Nonempty
      · have eq : Classical.choose hn = p := by simpa [color, hn] using h
        exact (Finset.mem_filter.mp (eq ▸ Classical.choose_spec hn)).2
      · simp [color, hn] at h
    have negative {t w : Fin n × Fin n} (h : color t w = none) : ∀ p, ¬ cross t w p := by
      intro p hp
      have hn : (pairs t w).Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
      simp [color, hn] at h
    have colorCount : (Fintype.card (Option (Fin 2 × Fin 2)) + 1) ^
        (Fintype.card (Option (Fin 2 × Fin 2)) * r) ≤ T.card := by
      simpa [T, Fintype.card_prod] using tagFiber
    obtain ⟨c, L, len, nd, subset, sameColor⟩ := orderedHomogeneous color r T colorCount
    have allFalse : c = none := by
      cases c with
      | none => rfl
      | some p =>
        exfalso
        have four : 4 ≤ L.length := by rw [len]; exact Nat.le_max_right _ _
        let t₀ := L[0]'(by omega)
        let t₁ := L[1]'(by omega)
        let t₂ := L[2]'(by omega)
        let t₃ := L[3]'(by omega)
        have h02 : cross t₀ t₂ p := positive (List.pairwise_iff_getElem.mp sameColor 0 2 (by omega) (by omega) (by omega))
        have h03 : cross t₀ t₃ p := positive (List.pairwise_iff_getElem.mp sameColor 0 3 (by omega) (by omega) (by omega))
        have h12 : cross t₁ t₂ p := positive (List.pairwise_iff_getElem.mp sameColor 1 2 (by omega) (by omega) (by omega))
        have h13 : cross t₁ t₃ p := positive (List.pairwise_iff_getElem.mp sameColor 1 3 (by omega) (by omega) (by omega))
        have inF {i : Nat} (hi : i < L.length) : L[i] ∈ F :=
          (Finset.mem_filter.mp (subset _ (List.getElem_mem hi))).1
        have t01 : t₀ ≠ t₁ := List.pairwise_iff_getElem.mp nd 0 1 (by omega) (by omega) (by omega)
        have t23 : t₂ ≠ t₃ := List.pairwise_iff_getElem.mp nd 2 3 (by omega) (by omega) (by omega)
        have ac : vertex t₀ p.1 ≠ vertex t₁ p.1 := by
          intro eq
          exact Finset.disjoint_left.mp (disjoint t₀ (inF (by omega)) t₁ (inF (by omega)) t01)
            h02.1 (eq.symm ▸ h12.1)
        have bd : vertex t₂ p.2 ≠ vertex t₃ p.2 := by
          intro eq
          exact Finset.disjoint_left.mp (disjoint t₂ (inF (by omega)) t₃ (inF (by omega)) t23)
            h02.2.1 (eq.symm ▸ h03.2.1)
        have hab := h02.2.2
        have hbc := h12.2.2.symm
        have hcd := h13.2.2
        have hda := h03.2.2.symm
        let W : G.Walk (vertex t₀ p.1) (vertex t₀ p.1) := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
        have cycle : W.IsCycle := by
          refine SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simp [W]⟩
          simp only [W, SimpleGraph.Walk.tail_cons]
          simp [hab.ne.symm, hbc.ne, hcd.ne, hda.ne, ac.symm, bd]
        have long := girth _ W cycle
        have short : W.length = 4 := rfl
        omega
    have noCross {t w : Fin n × Fin n} (ht : t ∈ L) (hw : w ∈ L) {a b : Fin n}
        (ha : a ∈ support t) (hb : b ∈ support w) : ¬ G.Adj a b := by
      have htT : t ∈ T := subset _ ht
      have hwT : w ∈ T := subset _ hw
      have tags : tag t = tag w := (Finset.mem_filter.mp htT).2.trans (Finset.mem_filter.mp hwT).2.symm
      by_cases et : t = w
      · subst w
        exact oneTest (Finset.mem_filter.mp htT).1 ha hb
      by_cases atEnd : a ∈ ({u, v} : Finset (Fin n))
      · exact oneTest (Finset.mem_filter.mp hwT).1 (fixedEndpoint tags ha atEnd) hb
      by_cases btEnd : b ∈ ({u, v} : Finset (Fin n))
      · exact oneTest (Finset.mem_filter.mp htT).1 ha (fixedEndpoint tags.symm hb btEnd)
      have aOutside : a ∈ outside t := Finset.mem_sdiff.mpr ⟨ha, atEnd⟩
      have bOutside : b ∈ outside w := Finset.mem_sdiff.mpr ⟨hb, btEnd⟩
      obtain ⟨i, hI, eI⟩ := List.mem_iff_getElem.mp ht
      obtain ⟨j, hJ, eJ⟩ := List.mem_iff_getElem.mp hw
      have distinct : i ≠ j := by intro eq; subst j; exact et (eI.symm.trans eJ)
      obtain ⟨p, rfl⟩ := ofSupport ha
      obtain ⟨q, rfl⟩ := ofSupport hb
      intro adj
      rcases lt_or_gt_of_ne distinct with less | greater
      · have h := List.pairwise_iff_getElem.mp sameColor i j hI hJ less
        rw [eI, eJ, allFalse] at h
        exact negative h (p, q) ⟨aOutside, bOutside, adj⟩
      · have h := List.pairwise_iff_getElem.mp sameColor j i hJ hI greater
        rw [eJ, eI, allFalse] at h
        exact negative h (q, p) ⟨bOutside, aOutside, adj.symm⟩
    let E := (L.take m).toFinset
    have subL : ∀ t ∈ E, t ∈ L := fun _ ht => List.mem_of_mem_take (List.mem_toFinset.mp ht)
    refine ⟨E, fun t ht => (Finset.mem_filter.mp (subset _ (subL t ht))).1, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup (nd.take (i := m)), List.length_take, len, Nat.min_eq_left]
      exact Nat.le_max_left _ _
    · intro a ha b hb
      obtain ⟨t, ht, ha⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨w, hw, hb⟩ := Finset.mem_biUnion.mp hb
      exact noCross (subL t ht) (subL w hw) ha hb
  have selectionAveraging {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
      (items : Finset E) (k cap : ℕ) (selected : Finset V → E → Prop)
      (recover : ∀ e ∈ items, ∃ U B : Finset V, Disjoint U B ∧ (U ∪ B).card ≤ k ∧
        ∀ A, U ⊆ A → Disjoint A B → selected A e)
      (bound : ∀ (A : Finset V) (D : Finset E), D ⊆ items → (∀ e ∈ D, selected A e) → D.card ≤ cap) :
      items.card ≤ 2 ^ k * cap := by
    classical
    let trials := (Finset.univ : Finset V).powerset
    let count (e : E) := (trials.filter fun A => selected A e).card
    let n := Fintype.card V
    have cardTrials : trials.card = 2 ^ n := by simp [trials, n]
    have enough (e : E) (he : e ∈ items) : 2 ^ n ≤ count e * 2 ^ k := by
      obtain ⟨U, B, separate, small, inEvent⟩ := recover e he
      let free := (Finset.univ : Finset V) \ (U ∪ B)
      have freeCard : free.card = n - (U ∪ B).card := by
        simp [free, n, Finset.card_sdiff_of_subset (Finset.subset_univ (U ∪ B))]
      have avail {W : Finset V} (hW : W ∈ free.powerset) {x : V} (hx : x ∈ W) :
          x ∉ U ∪ B := (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hW hx)).2
      have mapInto (W : Finset V) (hW : W ∈ free.powerset) :
          U ∪ W ∈ trials.filter (fun A => selected A e) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
        apply inEvent _ Finset.subset_union_left
        apply Finset.disjoint_left.mpr
        intro x hx hxB
        rcases Finset.mem_union.mp hx with hxU | hxW
        · exact Finset.disjoint_left.mp separate hxU hxB
        · exact avail hW hxW (Finset.mem_union_right U hxB)
      have cancelUnion (W X : Finset V) (hW : W ∈ free.powerset) (hX : X ∈ free.powerset)
          (equal : U ∪ W = U ∪ X) : W = X := by
        ext x
        constructor
        · intro hx
          have h : x ∈ U ∪ X := equal ▸ Finset.mem_union_right U hx
          exact (Finset.mem_union.mp h).resolve_left (fun hxU => avail hW hx (Finset.mem_union_left B hxU))
        · intro hx
          have h : x ∈ U ∪ W := equal.symm ▸ Finset.mem_union_right U hx
          exact (Finset.mem_union.mp h).resolve_left (fun hxU => avail hX hx (Finset.mem_union_left B hxU))
      have cardBound : free.powerset.card ≤ count e := by
        apply Finset.card_le_card_of_injOn (fun W => U ∪ W) mapInto
        intro W hW X hX equal
        exact cancelUnion W X hW hX equal
      rw [Finset.card_powerset, freeCard] at cardBound
      have exp : n ≤ n - (U ∪ B).card + k := by omega
      calc
        2 ^ n ≤ 2 ^ (n - (U ∪ B).card + k) := Nat.pow_le_pow_right (by decide) exp
        _ = 2 ^ (n - (U ∪ B).card) * 2 ^ k := by rw [pow_add]
        _ ≤ count e * 2 ^ k := Nat.mul_le_mul_right _ cardBound
    have doubleCount : (∑ e ∈ items, count e) = ∑ A ∈ trials, (items.filter (selected A)).card := by
      simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have total : (∑ e ∈ items, count e) ≤ trials.card * cap := by
      rw [doubleCount]
      calc
        _ ≤ ∑ _A ∈ trials, cap := Finset.sum_le_sum fun A _ =>
          bound A _ (Finset.filter_subset _ _) (fun _ he => (Finset.mem_filter.mp he).2)
        _ = _ := Finset.sum_const_nat fun _ _ => rfl
    have many : items.card * 2 ^ n ≤ (∑ e ∈ items, count e) * 2 ^ k := by
      rw [Finset.sum_mul, ← Finset.sum_const_nat (f := fun _ : E => 2 ^ n) (fun _ _ => rfl)]
      exact Finset.sum_le_sum enough
    have result : items.card * 2 ^ n ≤ (2 ^ k * cap) * 2 ^ n := by
      calc
        items.card * 2 ^ n ≤ (∑ e ∈ items, count e) * 2 ^ k := many
        _ ≤ (trials.card * cap) * 2 ^ k := Nat.mul_le_mul_right _ total
        _ = (2 ^ k * cap) * 2 ^ n := by rw [cardTrials]; ac_rfl
    exact le_of_mul_le_mul_right result (by positivity)
  have h_delete : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (walk : G.Walk v v), walk.IsCycle → 5 ≤ walk.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ (k : ℕ) (T : Finset (Sym2 (Fin n))), T ⊆ G.edgeFinset →
      (∀ e ∈ T, ∃ u v : Fin n, e = s(u,v) ∧ ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧
        ∃ B : Finset (Fin n), B.card ≤ k ∧ u ∉ B ∧ v ∉ B ∧
          ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q) →
      T.card ≤ 2^(k+2)*C.size := by
    intro n G dec girth C mono k T sub witnesses
    let selected (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
      ∃ u ∈ A, ∃ v ∈ A, e = s(u,v) ∧
        ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧
          ∀ p ∈ A, ∀ q ∈ A,
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q
    refine selectionAveraging T (k+2) C.size selected ?_ ?_
    · intro e he
      obtain ⟨u, v, eq, j, own, B, size, hu, hv, clean⟩ := witnesses e he
      let U : Finset (Fin n) := {u,v}
      refine ⟨U, B, ?_, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro x hx hb
        have isEnd : x = u ∨ x = v := by simpa [U] using hx
        rcases isEnd with rfl | rfl
        · exact hu hb
        · exact hv hb
      · calc
          (U ∪ B).card ≤ U.card + B.card := Finset.card_union_le _ _
          _ ≤ k + 2 := by
            have huCard : U.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
            omega
      · intro A retains excludes
        refine ⟨u, retains (by simp [U]), v, retains (by simp [U]), eq, j, own, ?_⟩
        intro p hp q hq accepts
        exact clean p (fun hb => Finset.disjoint_left.mp excludes hp hb)
          q (fun hb => Finset.disjoint_left.mp excludes hq hb) accepts
    · intro A D inc ok
      exact h_slice n G girth C mono A D (fun _ he => sub (inc he)) ok
  obtain ⟨m,c,hc⟩ := h_pack
  obtain ⟨M, chooseIndependent⟩ := thin m
  let k := 2 * M
  refine ⟨2^(k+2)+c, ?_⟩
  intro n G inst degrees girth givenC givenMono givenFun
  -- Counting all edges in a least circuit gives a bound for every subset in the original circuit.
  let candidates (s : ℕ) := ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size = s ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
  have existsSize : ∃ s, candidates s := ⟨givenC.size,givenC,rfl,givenMono,givenFun⟩
  obtain ⟨C,sizeEq,mono,computes⟩ := Nat.find_spec existsSize
  have least : PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C := by
    refine ⟨mono, fun D dMono same => ?_⟩
    exact sizeEq.le.trans (Nat.find_min' existsSize ⟨D,rfl,dMono,same.trans computes⟩)
  have cost := least.2 givenC givenMono (givenFun.trans computes.symm)
  apply le_trans (Finset.card_filter_le _ _)
  apply le_trans _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right cost 1))
  let goalEdges := G.edgeFinset
  let shield := fun e : Sym2 (Fin n) => ∃ u v : Fin n, e = s(u,v) ∧
    ∃ j : Fin C.gates.length, PEqualNP.EdgeOwnership.Owns n C j u v ∧ ∃ B : Finset (Fin n),
      B.card ≤ k ∧ u ∉ B ∧ v ∉ B ∧
        ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q
  let A := goalEdges.filter shield
  let D := goalEdges \ A
  have graphmem {e} (he : e ∈ goalEdges) : e ∈ G.edgeFinset := he
  have ha := h_delete n G girth C mono k A
    (fun _ he => graphmem (Finset.mem_filter.mp he).1) (fun _ he => (Finset.mem_filter.mp he).2)
  have hd : D.card ≤ c*(C.size+1) := by
    apply hc n G degrees girth C least computes D (fun _ he => graphmem (Finset.mem_sdiff.mp he).1)
    intro e he u v eq j owns
    dsimp only
    by_cases atU : PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u u) = true
    · exact Or.inl atU
    by_cases atV : PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput v v) = true
    · exact Or.inr (Or.inl atV)
    right; right
    let allowed : Finset (Fin n) := Finset.univ \ {u,v}
    let outside (t : Fin n × Fin n) := ({t.1,t.2} : Finset (Fin n)) \ {u,v}
    let bad (t : Fin n × Fin n) := PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput t.1 t.2) = true ∧ ¬G.Adj t.1 t.2
    have edge : G.Adj u v := by
      have mem := graphmem (Finset.mem_sdiff.mp he).1
      simpa [eq] using mem
    have small (t) : (outside t).card ≤ 2 :=
      (Finset.card_le_card Finset.sdiff_subset).trans
        ((Finset.card_insert_le _ _).trans (by simp))
    have inside (t) : outside t ⊆ allowed := fun _ hx =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have nz (t) (ht : bad t) : (outside t).Nonempty := by
      by_contra! empty
      have endpoints (x) (hx : x ∈ ({t.1,t.2} : Finset (Fin n))) : x = u ∨ x = v := by
        by_contra! miss
        have hit : x ∈ outside t := Finset.mem_sdiff.mpr ⟨hx,by simp [miss.1,miss.2]⟩
        simp [empty] at hit
      rcases endpoints t.1 (by simp) with a|a <;> rcases endpoints t.2 (by simp) with b|b
      · exact atU (by simpa only [a,b] using ht.1)
      · exact ht.2 (a ▸ b ▸ edge)
      · exact ht.2 (a ▸ b ▸ edge.symm)
      · exact atV (by simpa only [a,b] using ht.1)
    -- Removing the outside vertices of earlier tests forces a new test disjoint from them.
    have more (B : Finset (Fin n)) (sub : B ⊆ allowed) (cap : B.card ≤ 2 * M) :
        ∃ t, bad t ∧ Disjoint (outside t) B := by
      have avoidU : u ∉ B := fun h => (Finset.mem_sdiff.mp (sub h)).2 (by simp)
      have avoidV : v ∉ B := fun h => (Finset.mem_sdiff.mp (sub h)).2 (by simp)
      have leaks : ¬ ∀ p ∉ B, ∀ q ∉ B, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput p q) = true → G.Adj p q := by
        intro clean
        exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp he).1, u,v,eq,j,owns,B,cap,avoidU,avoidV,clean⟩)
      push Not at leaks
      obtain ⟨p,hp,q,hq,on,nonedge⟩ := leaks
      refine ⟨(p,q),⟨on,nonedge⟩,Finset.disjoint_left.mpr ?_⟩
      intro x hx
      have h : x = p ∨ x = q := by simpa using (Finset.mem_sdiff.mp hx).1
      rcases h with rfl|rfl
      · exact hp
      · exact hq
    have pack : ∀ r ≤ M, ∃ F : Finset (Fin n × Fin n), F.card = r ∧
        (∀ t ∈ F, bad t) ∧ ∀ t ∈ F, ∀ w ∈ F, t ≠ w → Disjoint (outside t) (outside w) := by
      intro r
      induction r with
      | zero => intro _; exact ⟨∅,by simp,by simp,by simp⟩
      | succ r ih =>
        intro hr
        obtain ⟨F,hF,hok,dis⟩ := ih (by omega)
        let B := F.biUnion outside
        have incl : B ⊆ allowed := by
          intro x hx
          obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hx
          exact inside t ht
        have cap : B.card ≤ 2 * M := calc
          B.card ≤ ∑ t∈F, (outside t).card := Finset.card_biUnion_le
          _ ≤ ∑ _t∈F, 2 := Finset.sum_le_sum (fun t _ => small t)
          _ ≤ 2 * M := by simp [hF]; omega
        obtain ⟨a,ha,hnew⟩ := more B incl cap
        have cross (b) (hb : b ∈ F) : Disjoint (outside a) (outside b) :=
          hnew.mono_right (Finset.subset_biUnion_of_mem outside hb)
        have fresh : a ∉ F := by
          intro old
          obtain ⟨x,hx⟩ := nz a ha
          exact Finset.disjoint_left.mp (cross a old) hx hx
        refine ⟨insert a F, by simp [fresh,hF], ?_, ?_⟩
        · intro t ht
          rcases Finset.mem_insert.mp ht with rfl|ht
          · exact ha
          · exact hok t ht
        · intro t ht w hw ne
          by_cases eqt : t = a
          · subst t
            exact cross w ((Finset.mem_insert.mp hw).resolve_left ne.symm)
          · have oldt := (Finset.mem_insert.mp ht).resolve_left eqt
            by_cases eqw : w = a
            · subst w
              exact (cross t oldt).symm
            · exact dis t oldt w ((Finset.mem_insert.mp hw).resolve_left eqw) ne
    obtain ⟨F, hF, fb, fd⟩ := pack M le_rfl
    obtain ⟨E, incl, count, independent⟩ :=
      chooseIndependent n G girth u v F edge hF.ge (fun t ht => (fb t ht).2) fd
    exact ⟨E, count, fun t ht => fb t (incl ht),
      fun t ht w hw distinct => fd t (incl ht) w (incl hw) distinct, independent⟩
  have total : goalEdges.card ≤ D.card+A.card := Finset.card_le_card_sdiff_add_card
  rw [Nat.add_mul]
  have hscale := Nat.mul_le_mul_left (2^(k+2)) (Nat.le_succ C.size)
  exact total.trans ((Nat.add_le_add hd (ha.trans hscale)).trans_eq (Nat.add_comm _ _))
