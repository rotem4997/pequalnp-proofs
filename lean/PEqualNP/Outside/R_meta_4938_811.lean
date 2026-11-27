import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4938_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) → PEqualNP.NotBracket.notCount { gates := x1 :: x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } + (15 : ℕ) ≤ x2.size →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (16 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro g C a b gOk cOk budget P V aOnly bOnly safe
  by_contra uncovered
  by_cases hn : PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } + (15 : ℕ) ≤ C.size
  · exact uncovered (dense g C a b gOk cOk budget hn aOnly bOnly safe)
  · have joint : ∀ x : Fin 10 → Bool, (V x a || V x b) = P x := by
      intro x
      cases pval : P x with
      | false =>
        have s := safe x pval
        rw [s.1, s.2]
        rfl
      | true =>
        cases va : V x a with
        | true => rfl
        | false =>
          cases vb : V x b with
          | true => rfl
          | false => exact (uncovered ⟨x, pval, va, vb⟩).elim
    let step := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    have len : ∀ (L : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (L.foldl step w).length = w.length + L.length := by
      intro L
      induction L with
      | nil => intro w; rfl
      | cons h hs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have atEnd : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
      intro l v
      simp
    let orGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, b]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: (C.gates ++ [orGate]), 11 + C.size⟩
    have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro h hh
      rcases List.mem_cons.mp hh with e | hh
      · rw [e]
        exact gOk g (List.mem_singleton.mpr rfl)
      · rcases List.mem_append.mp hh with h1 | h1
        · exact cOk h h1
        · rw [List.mem_singleton] at h1
          rw [h1]
          exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    have evalD : ∀ (x3 : Fin (10 : ℕ) → Bool), D.eval (List.ofFn x3) = P x3 := by
      intro x
      have hl : (C.wires (step (List.ofFn x) g)).length = 11 + C.size := by
        have e := len C.gates (step (List.ofFn x) g)
        have e2 : (step (List.ofFn x) g).length = 11 := by simp [step]
        rw [e2] at e
        exact e
      have top := atEnd (C.wires (step (List.ofFn x) g)) (orGate.op.eval (orGate.inputs.map fun i => (C.wires (step (List.ofFn x) g)).getD i false))
      rw [hl] at top
      change ((C.gates ++ [orGate]).foldl step (step (List.ofFn x) g)).getD (11 + C.size) false = P x
      rw [List.foldl_append]
      change (C.wires (step (List.ofFn x) g) ++ [orGate.op.eval (orGate.inputs.map fun i => (C.wires (step (List.ofFn x) g)).getD i false)]).getD (11 + C.size) false = P x
      rw [top, ← joint x]
      show List.any [V x a, V x b] id = (V x a || V x b)
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have bd := bound D fanD evalD
    have z : ([orGate].filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro h hh
      rw [List.mem_singleton] at hh
      rw [hh]
      intro hd
      have e := of_decide_eq_true hd
      cases e
    have nc : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } := by
      change ((g :: (C.gates ++ [orGate])).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = ((g :: C.gates).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
      rw [← List.cons_append, List.filter_append, List.length_append, z, List.length_nil, Nat.add_zero]
    have dl : D.size = C.size + 2 := by
      change (g :: (C.gates ++ [orGate])).length = C.gates.length + 2
      rw [List.length_cons, List.length_append, List.length_singleton]
    omega
