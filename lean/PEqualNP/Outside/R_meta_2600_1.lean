import Mathlib.Tactic
import PEqualNP.Defs

-- Set one vertex (a point or a line) to false. A gate that becomes constant, or equal to an earlier
-- wire, is free, and what is left is right on every input where that vertex is false. If five gates
-- are free, at most 57 gates do it, against the first hypothesis. The second is the rest: in a
-- circuit with at most 62 gates some vertex frees five gates.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2600_1
    (minusVertex : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 26), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, x v = false → (C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 13, (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) → 58 ≤ C.size)
    (freeFive : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (W : (Fin 26 → Bool) → ℕ → Bool),
      (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + i ∧ b < 26 + i) →
      C.size ≤ 62 → (∀ x i, W x i = (C.wires (List.ofFn x)).getD i false) →
      (∀ x : Fin 26 → Bool, (W x C.output = true ↔ ∃ a b : Fin 13, (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) →
      ∃ (v : Fin 26) (J : Finset ℕ), 5 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
        ∃ (a b : Bool), ∃ k < 26 + j, ∀ x : Fin 26 → Bool, x v = false → W x (26 + j) = (a && W x k || b)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  classical
  have wnil : ∀ (o : ℕ) (x : List Bool), PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[], o⟩ x = x := fun _ _ => rfl
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
  have run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length ∧
      (∀ i < x.length, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false) ∧
      ∀ (j : ℕ) (h : j < gs.length), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false else false) := by
    intro gs o x
    induction gs using List.reverseRecOn with
    | nil => refine ⟨by rw [wnil]; simp, fun i _ => by rw [wnil], fun j h => absurd h (Nat.not_lt_zero _)⟩
    | append_singleton gs g ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x =
          PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
            [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
        wsnoc gs g o x
      rw [e]
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x = W at h1 h2 h3 ⊢
      generalize hval : g.op.eval (g.inputs.map fun i => W.getD i false) = val
      have old : ∀ i < W.length, (W ++ [val]).getD i false = W.getD i false := fun i hi =>
        List.getD_append _ _ _ _ hi
      refine ⟨by simp [h1]; omega, fun i hi => by rw [old i (by omega)]; exact h2 i hi, ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · rw [old _ (by omega), h3 j hlt, List.getElem_append_left hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · rfl
      · have hj' : j = gs.length := by simp at hj; omega
        subst hj'
        rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_concat_length]
        refine hval.symm.trans ?_
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · exact List.getD_eq_default _ _ (by omega)
  intro C hgate hright
  by_contra hsize
  have hmono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨hop, a, b, hl, _⟩ := hgate i g hi
    exact ⟨hop, by rw [hl]; simp⟩
  obtain ⟨v, J, hcard, hJ⟩ := freeFive C (fun x i => (C.wires (List.ofFn x)).getD i false) hgate
    (by omega) (fun _ _ => rfl) hright
  let S := {y : Fin 26 → Bool // y v = false}
  let W : S → ℕ → Bool := fun y i => (C.wires (List.ofFn y.1)).getD i false
  have hW0 : ∀ (y : S) (i : Fin 26), W y i = y.1 i := by
    intro y i
    have := (run C.gates C.output (List.ofFn y.1)).2.1 i (by simp)
    refine this.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn (by simp)
  have hWg : ∀ (y : S) (j : ℕ) (h : j < C.gates.length), W y (26 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 26 + j then W y i else false) := by
    intro y j h
    have := (run C.gates C.output (List.ofFn y.1)).2.2 j h
    rw [List.length_ofFn] at this
    exact this
  have hWout : ∀ (y : S) i, 26 + C.gates.length ≤ i → W y i = false := by
    intro y i hi
    have := (run C.gates C.output (List.ofFn y.1)).1
    rw [List.length_ofFn] at this
    exact List.getD_eq_default _ _ (this.le.trans hi)
  have hall : ∀ (A U : {y : Fin 26 → Bool // y v = false} → ℕ → Bool) (m : ℕ) (l : List ℕ),
      (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
      (∀ y, (l.map (A y)).all id = false) ∨
        ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).all id = (l'.map (U y)).all id := by
    intro A U m l
    induction l with
    | nil => intro _; exact Or.inr ⟨[], by simp⟩
    | cons i l ih =>
      intro h
      rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
      · left; intro y; simp only [List.map_cons, List.all_cons, h0 y, Bool.and_false]
      rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
      · cases b
        · left; intro y; simp only [List.map_cons, List.all_cons, hb y, id, Bool.false_and]
        · exact Or.inr ⟨l', by simp; omega, fun y => by
            rw [List.map_cons, List.all_cons, hb y, he y]; simp⟩
      · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
          rw [List.map_cons, List.all_cons, hb y, he y, List.map_cons, List.all_cons]⟩
  have hany : ∀ (A U : {y : Fin 26 → Bool // y v = false} → ℕ → Bool) (m : ℕ) (l : List ℕ),
      (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
      (∀ y, (l.map (A y)).any id = true) ∨
        ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).any id = (l'.map (U y)).any id := by
    intro A U m l
    induction l with
    | nil => intro _; exact Or.inr ⟨[], by simp⟩
    | cons i l ih =>
      intro h
      rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
      · left; intro y; simp only [List.map_cons, List.any_cons, h0 y, Bool.or_true]
      rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
      · cases b
        · exact Or.inr ⟨l', by simp; omega, fun y => by
            rw [List.map_cons, List.any_cons, hb y, he y]; simp⟩
        · left; intro y; simp only [List.map_cons, List.any_cons, hb y, id, Bool.true_or]
      · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
          rw [List.map_cons, List.any_cons, hb y, he y, List.map_cons, List.any_cons]⟩
  have main : ∀ k ≤ C.gates.length, ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
      PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k)).card ≤ k ∧
      ∀ i < 26 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 26 + gs.length, ∀ y : S,
        W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], (fun g hg => absurd hg List.not_mem_nil), by simp, ?_⟩
      intro i hi
      refine Or.inr ⟨i, by simpa using hi, fun y => ?_⟩
      rw [wnil]
      refine (hW0 y ⟨i, hi⟩).trans ?_
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      exact (List.getElem_ofFn (f := y.1) (by simpa using hi)).symm
    | succ k ih =>
      intro hk
      obtain ⟨gs, hgf, hgc, hgi⟩ := ih (by omega)
      have hfilt : (J.filter (· < k + 1)).card ≤ (J.filter (· < k)).card + (if k ∈ J then 1 else 0) := by
        have hsub : J.filter (· < k + 1) ⊆ J.filter (· < k) ∪ (if k ∈ J then {k} else ∅) := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_union] at ha ⊢
          rcases Nat.lt_or_ge a k with h | h
          · exact Or.inl ⟨ha.1, h⟩
          · have : a = k := by omega
            subst this
            right; simp [ha.1]
        refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
        split <;> simp
      -- wire `26 + k` is constant, kept already, or one new gate away
      have keep : ((∃ b, ∀ y, W y (26 + k) = b) ∨ ∃ j < 26 + gs.length, ∀ y : S,
            W y (26 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false) →
          ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
          PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 ∧
          ∀ i < 26 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 26 + gs.length, ∀ y : S,
            W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
        intro h
        refine ⟨gs, hgf, ?_, ?_⟩
        · split at hfilt <;> omega
        · intro i hi
          rcases Nat.lt_or_ge i (26 + k) with h' | h'
          · exact hgi i h'
          · have : i = 26 + k := by omega
            subst this; exact h
      by_cases hkJ : k ∈ J
      · apply keep
        obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
        have hb' : ∀ y : S, W y (26 + k) = (a && W y i || b) := fun y => hb y.1 y.2
        cases b with
        | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
        | false =>
          cases a with
          | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
          | true =>
            have hb'' : ∀ y, W y (26 + k) = W y i := fun y => by rw [hb']; simp
            rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
            · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
            · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
      · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
        have hg := hmono _ hmem
        have hWk := fun y => hWg y k (by omega)
        generalize C.gates[k] = g at hg hWk
        let U : S → ℕ → Bool := fun y j =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false
        let A : S → ℕ → Bool := fun y i => if i < 26 + k then W y i else false
        have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 26 + gs.length, ∀ y, A y i = U y j := by
          intro i
          by_cases h : i < 26 + k
          · simpa [A, h, U] using hgi i h
          · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
        have hWA : ∀ y, W y (26 + k) = g.op.eval (g.inputs.map (A y)) := hWk
        have hnew : (∃ b, ∀ y, W y (26 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.Monotone2 ⟨[g'], 0⟩ ∧ ∀ y, W y (26 + k) = g'.op.eval (g'.inputs.map (U y)) := by
          obtain ⟨op, l⟩ := g
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          obtain ⟨hop, hlen⟩ := hg
          rcases hop with rfl | rfl
          · rcases hall A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
            · exact Or.inl ⟨false, fun y => (hWA y).trans (h y)⟩
            · exact Or.inr ⟨⟨.and, l'⟩, (fun g hg => by obtain rfl := List.mem_singleton.1 hg; exact ⟨Or.inl rfl, h1.trans hlen⟩), fun y => (hWA y).trans (h3 y)⟩
          · rcases hany A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
            · exact Or.inl ⟨true, fun y => (hWA y).trans (h y)⟩
            · exact Or.inr ⟨⟨.or, l'⟩, (fun g hg => by obtain rfl := List.mem_singleton.1 hg; exact ⟨Or.inr rfl, h1.trans hlen⟩), fun y => (hWA y).trans (h3 y)⟩
        rcases hnew with h | ⟨g', hg', hv⟩
        · exact keep (Or.inl h)
        have step : ∀ y : S, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g'], 0⟩ (List.ofFn y.1) =
            PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1) ++ [g'.op.eval (g'.inputs.map (U y))] := by
          intro y
          exact wsnoc gs g' 0 _
        have hlen : ∀ y : S, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).length = 26 + gs.length := by
          intro y
          have := (run gs 0 (List.ofFn y.1)).1
          rwa [List.length_ofFn] at this
        refine ⟨gs ++ [g'], ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.1 ha with h | h
          · exact hgf a h
          · exact hg' a h
        · simp only [hkJ, ite_false] at hfilt
          simp only [List.length_append, List.length_singleton]
          omega
        · intro i hi
          rcases Nat.lt_or_ge i (26 + k) with h' | h'
          · rcases hgi i h' with h | ⟨j, hj, h⟩
            · exact Or.inl h
            · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
              rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
              exact h y
          · have : i = 26 + k := by omega
            subst this
            refine Or.inr ⟨26 + gs.length, by simp, fun y => ?_⟩
            rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
            simpa using hv y
  obtain ⟨gs, hgf, hgc, hgi⟩ := main C.gates.length (le_refl _)
  have hJf : J.filter (· < C.gates.length) = J := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact (hJ j hj).1
  rw [hJf] at hgc
  have hsz : C.gates.length ≤ 62 := by
    have : C.size = C.gates.length := rfl
    omega
  have hout : (∃ b, ∀ y, W y C.output = b) ∨ ∃ j < 26 + gs.length, ∀ y : S,
      W y C.output = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y.1)).getD j false := by
    rcases Nat.lt_or_ge C.output (26 + C.gates.length) with h | h
    · exact hgi _ h
    · exact Or.inl ⟨false, fun y => hWout y _ h⟩
  rcases hout with ⟨b, hb⟩ | ⟨j, _, hb⟩
  · let y0 : S := ⟨fun _ => false, rfl⟩
    have hc : ∃ c : Fin 13, v ≠ Fin.castAdd 13 c ∧ v ≠ Fin.natAdd 13 c := by
      clear * -
      revert v
      decide
    obtain ⟨c, hc1, hc2⟩ := hc
    let y1 : S := ⟨fun i => decide (i = Fin.castAdd 13 c ∨ i = Fin.natAdd 13 c), decide_eq_false (not_or.2 ⟨hc1, hc2⟩)⟩
    have e1 : W y1 C.output = true := (hright y1.1).2 ⟨c, c, Or.inl rfl, by simp [y1], by simp [y1]⟩
    have e0 : W y0 C.output = true := (hb y0).trans ((hb y1).symm.trans e1)
    obtain ⟨a, b', _, ha, _⟩ := (hright y0.1).1 e0
    exact absurd ha (by simp [y0])
  · have h58 := minusVertex ⟨gs, j⟩ v hgf (fun x hx => by
      rw [← hright x]
      have := hb ⟨x, hx⟩
      exact ⟨fun h => this.trans h, fun h => this.symm.trans h⟩)
    have : (PEqualNP.CircuitLowerBounds.Circuit.mk gs j).size = gs.length := rfl
    omega
