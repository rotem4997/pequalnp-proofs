import Mathlib
import PEqualNP.Defs

-- The proof pattern (explicit circuit, gate check by cases, `decide +kernel` over all inputs) is copied from
-- the merged L_meta_9921. The 20-gate circuit: with t = a1 b1, u = a0 b0, h = t xor (u and (a1 or b1)),
-- bit 4 is (a2 and b2) ? not h : ((a2 or b2) and t and (a2 b0 or b2 a0)).
theorem PEqualNP.Outside.L_meta_10266 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 4) 23 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 24] }], output := 25 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    revert x
    decide +kernel
