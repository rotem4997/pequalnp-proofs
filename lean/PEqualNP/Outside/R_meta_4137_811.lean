import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4137_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → PEqualNP.NotBracket.notCount x1 + (15 : ℕ) ≤ x1.size → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ))) = Bool.false ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro C fan sz
  by_contra none
  by_cases hn : PEqualNP.NotBracket.notCount C + (15 : ℕ) ≤ C.size
  · exact none (dense C fan sz hn)
  · have comp : ∀ x : Fin 10 → Bool, (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ))) = Bool.false → C.eval (List.ofFn x) = (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) := by
      intro x h0
      by_contra h
      exact none ⟨x, h0, h⟩
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
    have wiresEq : ∀ x : Fin 10 → Bool, C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := fun x => rfl
    by_cases ho : C.output < 10 + C.gates.length
    · let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩
      let g2 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, 10 + C.gates.length]⟩
      let F : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [g1, g2], 10 + C.gates.length + 1⟩
      have fanF : PEqualNP.MetaComplexity.FanInTwo F := by
        intro h hh
        rcases List.mem_append.mp hh with hh | hh
        · exact fan h hh
        · rcases List.mem_cons.mp hh with e | hh
          · rw [e]
            exact ⟨Or.inl rfl, Nat.le_refl 2⟩
          · rcases List.mem_cons.mp hh with e | hh
            · rw [e]
              exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
            · exact absurd hh (List.not_mem_nil)
      have evalF : ∀ (x3 : Fin (10 : ℕ) → Bool), F.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ))) := by
        intro x
        obtain ⟨r, hr, hl⟩ := pre C.gates (List.ofFn x)
        have hlen : (List.ofFn x ++ r).length = 10 + C.gates.length := by
          rw [List.length_append, List.length_ofFn, hl]
        have hc : C.eval (List.ofFn x) = (List.ofFn x ++ r).getD C.output false := by
          show (C.gates.foldl step (List.ofFn x)).getD C.output false = _
          rw [hr]
        have h0 : (List.ofFn x ++ r).getD 0 false = x 0 := by
          rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; omega)]
          simp [List.getD_eq_getElem?_getD]
        have h1 : (List.ofFn x ++ r).getD 1 false = x 1 := by
          rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; omega)]
          simp [List.getD_eq_getElem?_getD]
        have hb : (((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]) ++ [(List.any [((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD C.output false, ((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD (10 + C.gates.length) false] id)]).getD (10 + C.gates.length + 1) false = (List.any [((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD C.output false, ((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD (10 + C.gates.length) false] id) := by
          rw [List.getD_append_right _ _ _ _ (by rw [List.length_append, hlen, List.length_singleton])]
          rw [List.length_append, hlen, List.length_singleton]
          simp
        have ha1 : ((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD C.output false = (List.ofFn x ++ r).getD C.output false := List.getD_append _ _ _ _ (by rw [hlen]; omega)
        have ha2 : ((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD (10 + C.gates.length) false = (List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id) := by
          rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
          rw [hlen]
          simp
        have key : F.eval (List.ofFn x) = (C.eval (List.ofFn x) || (x 0 && x 1)) := by
          show ((C.gates ++ [g1, g2]).foldl step (List.ofFn x)).getD (10 + C.gates.length + 1) false = _
          rw [List.foldl_append, hr, hc]
          show (((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]) ++ [(List.any [((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD C.output false, ((List.ofFn x ++ r) ++ [(List.all [(List.ofFn x ++ r).getD 0 false, (List.ofFn x ++ r).getD 1 false] id)]).getD (10 + C.gates.length) false] id)]).getD (10 + C.gates.length + 1) false = _
          rw [hb, ha1, ha2, h0, h1]
          simp
        rw [key]
        cases hx : (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)))
        · rw [comp x hx, Bool.or_false, hx]
        · rw [Bool.or_true]
          simp
      have bd := bound F fanF evalF
      have hg1 : ¬(decide (g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
        intro hd
        have e := of_decide_eq_true hd
        cases e
      have hg2 : ¬(decide (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
        intro hd
        have e := of_decide_eq_true hd
        cases e
      have nc : PEqualNP.NotBracket.notCount F = PEqualNP.NotBracket.notCount C := by
        change ((C.gates ++ [g1, g2]).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (C.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
        rw [List.filter_append, List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg1,
          List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg2, List.filter_nil, List.append_nil]
      have dl : F.size = C.size + 2 := by
        change (C.gates ++ [g1, g2]).length = C.gates.length + 2
        rw [List.length_append]
        rfl
      omega
    · let x : Fin 10 → Bool := fun i => decide (i = 1 ∨ i = 2)
      obtain ⟨r, hr, hl⟩ := pre C.gates (List.ofFn x)
      have hc : C.eval (List.ofFn x) = false := by
        show (C.gates.foldl step (List.ofFn x)).getD C.output false = false
        rw [hr]
        apply List.getD_eq_default
        rw [List.length_append, List.length_ofFn, hl]
        omega
      have e := comp x (by decide)
      rw [hc] at e
      exact absurd e (by decide)
