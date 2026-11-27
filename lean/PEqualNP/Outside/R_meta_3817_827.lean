import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Normalize the circuit and count the input positions left after every used wire's first read.
-- The five repeated wires and the total number of additional reads restrict the two remaining cases.
theorem PEqualNP.Outside.R_meta_3817_827
    (floor : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 15 ≤ C.size)
    (normalize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun 9 D = circuitFun 9 C ∧
      NestedCover.ReadsBack 9 D ∧ (∀ g ∈ D.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨ (g.op ≠ GateOp.not ∧ g.inputs.length = 2)) ∧
      let pins := D.gates.flatMap Gate.inputs
      let repeated := (pins.toFinset.filter (fun w => 2 ≤ pins.count w)).card
      let extra := pins.length - pins.toFinset.card
      let unary := D.gates.countP (fun g => g.inputs.length == 1)
      D.output = 8 + D.size ∧ pins.toFinset = Finset.range (8 + D.size) ∧
      5 ≤ repeated ∧ repeated ≤ extra ∧ extra + unary + 8 = D.size)
    (binary : ∀ D : Circuit, FanInTwo D → D.size = 15 → NestedCover.ReadsBack 9 D →
    (∀ g ∈ D.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨ (g.op ≠ GateOp.not ∧ g.inputs.length = 2)) → circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    let pins := D.gates.flatMap Gate.inputs
      let repeated := (pins.toFinset.filter (fun w => 2 ≤ pins.count w)).card
      let extra := pins.length - pins.toFinset.card
      let unary := D.gates.countP (fun g => g.inputs.length == 1)
      D.output = 23 → pins.toFinset = Finset.range 23 → 5 ≤ repeated → extra = 7 → unary = 0 → False)
    (signed : ∀ D : Circuit, FanInTwo D → D.size = 15 → NestedCover.ReadsBack 9 D →
    (∀ g ∈ D.gates, (g.op = GateOp.not ∧ g.inputs.length = 1) ∨ (g.op ≠ GateOp.not ∧ g.inputs.length = 2)) → circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
    let pins := D.gates.flatMap Gate.inputs
      let repeated := (pins.toFinset.filter (fun w => 2 ≤ pins.count w)).card
      let extra := pins.length - pins.toFinset.card
      let unary := D.gates.countP (fun g => g.inputs.length == 1)
      D.output = 23 → pins.toFinset = Finset.range 23 → 5 ≤ repeated → extra + unary = 7 → (unary = 1 ∨ unary = 2) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C legal small
  classical
  by_contra noWitness
  have correct : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    exact Classical.not_not.mp (fun bad => noWitness ⟨x, bad⟩)
  obtain ⟨D, hd, budget, same, back, arity, last, readAll, forks, forkLe, count⟩ := normalize C legal correct
  have good := same.trans correct
  have lower := floor D hd good
  have size : D.size = 15 := by omega
  let pins := D.gates.flatMap Gate.inputs
  let extra := pins.length - pins.toFinset.card
  let unary := D.gates.countP (fun g => g.inputs.length == 1)
  change _ ≤ extra at forkLe
  change extra + unary + 8 = D.size at count
  rw [size] at last readAll
  have unaryBound : unary ≤ 2 := by omega
  have budgetSeven : extra + unary = 7 := by omega
  by_cases h : unary = 0
  · have extraSeven : extra = 7 := by omega
    exact binary D hd size back arity good last readAll forks extraSeven h
  · have choice : unary = 1 ∨ unary = 2 := by omega
    exact signed D hd size back arity good last readAll forks budgetSeven choice
