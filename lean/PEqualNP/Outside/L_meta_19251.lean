import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19251 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 18]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
