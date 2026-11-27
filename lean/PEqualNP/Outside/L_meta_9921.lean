import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_9921 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) = (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat))) 14 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 17] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    revert x
    decide +kernel
