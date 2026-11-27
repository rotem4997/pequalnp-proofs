import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19291 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7597924 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
