import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_10388 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (4 ≤ ((List.ofFn x).count true))) 23 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }], output := 28 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    revert x
    decide +kernel
