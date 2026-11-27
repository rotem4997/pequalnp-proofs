import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19398 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 21]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
