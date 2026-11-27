import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1755 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], 29⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 20 ∧ C.output = 29 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 10 + p.2) ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro C
  refine ⟨rfl, rfl, ?_, ?_⟩
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by rfl
    rw [h]
    simp only [C, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false]
    generalize x 0 = a0
    generalize x 1 = a1
    generalize x 2 = a2
    generalize x 3 = a3
    generalize x 4 = a4
    generalize x 5 = a5
    generalize x 6 = a6
    generalize x 7 = a7
    generalize x 8 = a8
    generalize x 9 = a9
    revert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
    decide
