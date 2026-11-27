import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_10264 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 16 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    revert x
    decide +kernel
