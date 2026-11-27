import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6583_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (28 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (18 : ℕ) →       (16 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) x2.gates →         have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8)).getD x9 Bool.false;         (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 ↑x3 = Bool.true ∧ x8 x9 ↑x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 ↑x3 = Bool.false ∧ x8 x10 ↑x4 = Bool.true) → ¬∀ (x11 : Fin (10 : ℕ) → Bool), (x8 x11 ↑x3 && x8 x11 ↑x4) = x1 x11) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (28 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (18 : ℕ) →       (15 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) x2.gates →         have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires (List.ofFn x8)).getD x9 Bool.false;         (∃ (x9 : Fin (10 : ℕ) → Bool), x8 x9 ↑x3 = Bool.true ∧ x8 x9 ↑x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x8 x10 ↑x3 = Bool.false ∧ x8 x10 ↑x4 = Bool.true) → ¬∀ (x11 : Fin (10 : ℕ) → Bool), (x8 x11 ↑x3 && x8 x11 ↑x4) = x1 x11 := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro F C a b fan size count W ab ba computes
  have size' : C.gates.length = 18 := size
  have notFew : PEqualNP.NotBracket.notCount C ≤ 2 := by
    let step := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have len : ∀ (L : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), (L.foldl step w).length = w.length + L.length := by
      intro L
      induction L with
      | nil => intro w; rfl
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
    have atEnd : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
      intro l v
      simp
    let andGate : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a.val, b.val]⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates ++ [andGate], 28⟩
    have fanD : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact fan g h
      · rw [List.mem_singleton] at h
        rw [h]
        exact ⟨Or.inl rfl, Nat.le_refl 2⟩
    have evalD : ∀ (x3 : Fin (10 : ℕ) → Bool), D.eval (List.ofFn x3) = F x3 := by
      intro x
      have hl : (C.wires (List.ofFn x)).length = 28 := by
        have e := len C.gates (List.ofFn x)
        rw [List.length_ofFn, size'] at e
        exact e
      have top := atEnd (C.wires (List.ofFn x)) (andGate.op.eval (andGate.inputs.map fun i => (C.wires (List.ofFn x)).getD i false))
      rw [hl] at top
      change ((C.gates ++ [andGate]).foldl step (List.ofFn x)).getD 28 false = F x
      rw [List.foldl_append]
      change (C.wires (List.ofFn x) ++ [andGate.op.eval (andGate.inputs.map fun i => (C.wires (List.ofFn x)).getD i false)]).getD 28 false = F x
      rw [top]
      rw [← computes x]
      show List.all [W x a.val, W x b.val] id = (W x a.val && W x b.val)
      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
    have bd := bound D fanD evalD
    have nc : PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount C := by
      change ((C.gates ++ [andGate]).filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (C.gates.filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
      have z : ([andGate].filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro g hg
        rw [List.mem_singleton] at hg
        rw [hg]
        intro hd
        have e := of_decide_eq_true hd
        cases e
      rw [List.filter_append, List.length_append, z, List.length_nil, Nat.add_zero]
    have dl : D.size = 19 := by
      change (C.gates ++ [andGate]).length = 19
      rw [List.length_append, size']
      rfl
    omega
  have many : (16 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) C.gates := by
    have split : C.gates.length = List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) C.gates + List.countP (fun (a : PEqualNP.CircuitLowerBounds.Gate) => decide ¬((fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) a = true)) C.gates := List.length_eq_countP_add_countP _
    have nf : PEqualNP.NotBracket.notCount C = List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) C.gates := by
      change (C.gates.filter fun g => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = _
      rw [List.countP_eq_length_filter]
    have mono := List.countP_mono_left (l := C.gates) (p := fun (a : PEqualNP.CircuitLowerBounds.Gate) => decide ¬((fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => !x7.op.eval [Bool.false]) a = true)) (q := fun g : PEqualNP.CircuitLowerBounds.Gate => decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) (by
      intro g hg hp
      have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := (fan g hg).1
      rcases hop with h | h | h
      · exfalso
        apply of_decide_eq_true hp
        show (!g.op.eval [false]) = true
        rw [h]
        rfl
      · exfalso
        apply of_decide_eq_true hp
        show (!g.op.eval [false]) = true
        rw [h]
        rfl
      · exact decide_eq_true h)
    omega
  exact dense C a b fan size many ab ba computes
