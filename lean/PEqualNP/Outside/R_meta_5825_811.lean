import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5825_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) → PEqualNP.NotBracket.notCount x3 + (15 : ℕ) ≤ x3.size →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((10 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((10 : ℕ) + ↑x5) = Bool.false) :
    ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((10 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((10 : ℕ) + ↑x5) = Bool.false := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro a b C p q hab fan sz
  by_cases hn : PEqualNP.NotBracket.notCount C + (15 : ℕ) ≤ C.size
  · exact dense a b C p q hab fan sz hn
  · intro g0 pet val e1 e2 e3
    by_contra none
    let step := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    have pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), ∃ r : List Bool, gs.foldl step w = w ++ r ∧ r.length = gs.length := by
      intro gs
      induction gs with
      | nil => exact fun w => ⟨[], by rw [List.foldl_nil, List.append_nil], rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨r, hr, hl⟩ := ih (step w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: r, ?_, ?_⟩
        · rw [List.foldl_cons, hr]
          show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ++ r = _
          rw [List.append_assoc, List.singleton_append]
        · rw [List.length_cons, List.length_cons, hl]
    have valEq : ∀ (x : Fin 10 → Bool) (i : ℕ), val x i = (C.gates.foldl step (step (List.ofFn x) g0)).getD i false := fun x i => rfl
    have wlen : ∀ x : Fin 10 → Bool, (C.gates.foldl step (step (List.ofFn x) g0)).length = 11 + C.gates.length := by
      intro x
      obtain ⟨r, hr, hl⟩ := pre C.gates (step (List.ofFn x) g0)
      rw [hr, List.length_append, hl]
      show (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).length + C.gates.length = _
      rw [List.length_append, List.length_ofFn, List.length_singleton]
    have orEq : ∀ x : Fin 10 → Bool, (val x ((10 : ℕ) + ↑p) || val x ((10 : ℕ) + ↑q)) = pet x := by
      intro x
      cases hx : pet x
      · rw [(e3 x hx).1, (e3 x hx).2]
        rfl
      · cases h4 : val x ((10 : ℕ) + ↑p)
        · cases h5 : val x ((10 : ℕ) + ↑q)
          · exact absurd ⟨x, hx, h4, h5⟩ none
          · rfl
        · rfl
    by_cases hp : (10 : ℕ) + ↑p < 11 + C.gates.length
    · by_cases hq : (10 : ℕ) + ↑q < 11 + C.gates.length
      · let g2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(10 : ℕ) + ↑p, (10 : ℕ) + ↑q]⟩
        let F : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: (C.gates ++ [g2]), 11 + C.gates.length⟩
        have fanF : PEqualNP.MetaComplexity.FanInTwo F := by
          intro h hh
          rcases List.mem_cons.mp hh with e | hh
          · rw [e]
            exact ⟨Or.inl rfl, Nat.le_refl 2⟩
          · rcases List.mem_append.mp hh with hh | hh
            · exact fan h hh
            · rcases List.mem_cons.mp hh with e | hh
              · rw [e]
                exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
              · exact absurd hh List.not_mem_nil
        have evalF : ∀ (x3 : Fin (10 : ℕ) → Bool), F.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ))) := by
          intro x
          have hb : ((C.gates.foldl step (step (List.ofFn x) g0)) ++ [List.any [(C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑p) false, (C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑q) false] id]).getD (11 + C.gates.length) false = List.any [(C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑p) false, (C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑q) false] id := by
            rw [List.getD_append_right _ _ _ _ (by rw [wlen x])]
            rw [wlen x]
            simp
          show ((g0 :: (C.gates ++ [g2])).foldl step (List.ofFn x)).getD (11 + C.gates.length) false = _
          rw [List.foldl_cons, List.foldl_append]
          show ((C.gates.foldl step (step (List.ofFn x) g0)) ++ [List.any [(C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑p) false, (C.gates.foldl step (step (List.ofFn x) g0)).getD ((10 : ℕ) + ↑q) false] id]).getD (11 + C.gates.length) false = _
          rw [hb, ← valEq x, ← valEq x]
          have k := orEq x
          simp only [List.any_cons, List.any_nil, id, Bool.or_false]
          exact k
        have bd := bound F fanF evalF
        have hg0 : ¬(decide (g0.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
          intro hd
          have e := of_decide_eq_true hd
          cases e
        have hg2 : ¬(decide (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
          intro hd
          have e := of_decide_eq_true hd
          cases e
        have nc : PEqualNP.NotBracket.notCount F = PEqualNP.NotBracket.notCount C := by
          change ((g0 :: (C.gates ++ [g2])).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (C.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
          rw [List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg0, List.filter_append,
            List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg2, List.filter_nil, List.append_nil]
        have dl : F.size = C.size + 2 := by
          change (g0 :: (C.gates ++ [g2])).length = C.gates.length + 2
          rw [List.length_cons, List.length_append]
          rfl
        omega
      · obtain ⟨y, _, hy⟩ := e2
        rw [valEq y, List.getD_eq_default _ _ (by rw [wlen y]; omega)] at hy
        exact Bool.false_ne_true hy
    · obtain ⟨y, hy, _⟩ := e1
      rw [valEq y, List.getD_eq_default _ _ (by rw [wlen y]; omega)] at hy
      exact Bool.false_ne_true hy
