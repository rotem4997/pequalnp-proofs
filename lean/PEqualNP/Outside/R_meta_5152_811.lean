import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5152_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (negBound : ¬PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x1 : Fin (10 : ℕ) → Bool) => !(x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)))) (17 : ℕ))
    (dense : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         (∀ (x8 : Fin (10 : ℕ)) (x9 : Finset ℕ), (∀ x10 ∈ x9, ∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), (x1 :: x2.gates)[x10]? = Option.some x12 ∧ ↑x8 ∈ x12.inputs ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.not → x12.inputs.head? = Option.some ↑x8)) → x9.card ≤ if x4 = Bool.true then (3 : ℕ) else (2 : ℕ)) → PEqualNP.NotBracket.notCount x2 + (16 : ℕ) ≤ x2.size → (x4 = Bool.true → (17 : ℕ) ≤ x2.size) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         (∀ (x8 : Fin (10 : ℕ)) (x9 : Finset ℕ), (∀ x10 ∈ x9, ∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), (x1 :: x2.gates)[x10]? = Option.some x12 ∧ ↑x8 ∈ x12.inputs ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.not → x12.inputs.head? = Option.some ↑x8)) → x9.card ≤ if x4 = Bool.true then (3 : ℕ) else (2 : ℕ)) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11 := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro g C out neg fan cOk budget fanout P V
  by_contra none
  have comp : ∀ x : Fin 10 → Bool, (if neg = true then !V x out else V x out) = P x := by
    intro x
    by_contra h
    exact none ⟨x, h⟩
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
  let C1 : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: C.gates, out⟩
  have fan1 : PEqualNP.MetaComplexity.FanInTwo C1 := by
    intro h hh
    rcases List.mem_cons.mp hh with e | hh
    · rw [e]
      exact fan g (List.mem_singleton.mpr rfl)
    · exact cOk h hh
  have size1 : C1.size = C.size + 1 := by
    change (g :: C.gates).length = C.gates.length + 1
    rw [List.length_cons]
  have same : PEqualNP.NotBracket.notCount C1 = PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } := rfl
  have B : neg = true → (17 : ℕ) ≤ C.size := by
    intro hneg
    by_contra small
    apply negBound
    refine ⟨C1, fan1, by omega, ?_⟩
    intro x
    have h := comp x
    rw [if_pos hneg] at h
    show V x out = !(P x)
    rw [← h, Bool.not_not]
  have A : PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } + (16 : ℕ) ≤ C.size := by
    by_cases hneg : neg = true
    · let notGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [out]⟩
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: (C.gates ++ [notGate]), 11 + C.size⟩
      have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
        intro h hh
        rcases List.mem_cons.mp hh with e | hh
        · rw [e]
          exact fan g (List.mem_singleton.mpr rfl)
        · rcases List.mem_append.mp hh with h1 | h1
          · exact cOk h h1
          · rw [List.mem_singleton] at h1
            rw [h1]
            exact ⟨Or.inr (Or.inr rfl), Nat.le_succ 1⟩
      have evalD : ∀ (x3 : Fin (10 : ℕ) → Bool), D.eval (List.ofFn x3) = P x3 := by
        intro x
        have hl : (C.wires (step (List.ofFn x) g)).length = 11 + C.size := by
          have e := len C.gates (step (List.ofFn x) g)
          have e2 : (step (List.ofFn x) g).length = 11 := by simp [step]
          rw [e2] at e
          exact e
        have top := atEnd (C.wires (step (List.ofFn x) g)) (notGate.op.eval (notGate.inputs.map fun i => (C.wires (step (List.ofFn x) g)).getD i false))
        rw [hl] at top
        change ((C.gates ++ [notGate]).foldl step (step (List.ofFn x) g)).getD (11 + C.size) false = P x
        rw [List.foldl_append]
        change (C.wires (step (List.ofFn x) g) ++ [notGate.op.eval (notGate.inputs.map fun i => (C.wires (step (List.ofFn x) g)).getD i false)]).getD (11 + C.size) false = P x
        have h := comp x
        rw [if_pos hneg] at h
        rw [top, ← h]
        rfl
      have bd := bound D fanD evalD
      have zz : ([notGate].filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) = [notGate] := List.filter_cons_of_pos (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) (l := []) (decide_eq_true rfl)
      have nc : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } + 1 := by
        change ((g :: (C.gates ++ [notGate])).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = ((g :: C.gates).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length + 1
        rw [← List.cons_append, List.filter_append, List.length_append, zz, List.length_singleton]
      have dl : D.size = C.size + 2 := by
        change (g :: (C.gates ++ [notGate])).length = C.gates.length + 2
        rw [List.length_cons, List.length_append, List.length_singleton]
      omega
    · have evalC : ∀ (x3 : Fin (10 : ℕ) → Bool), C1.eval (List.ofFn x3) = P x3 := by
        intro x
        have h := comp x
        rw [if_neg hneg] at h
        exact h
      have bd := bound C1 fan1 evalC
      omega
  have sub : PEqualNP.NotBracket.notCount C ≤ PEqualNP.NotBracket.notCount { gates := g :: C.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } :=
    ((List.sublist_cons_self g C.gates).filter (fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not))).length_le
  exact none (dense g C out neg fan cOk budget fanout (by omega) B)
