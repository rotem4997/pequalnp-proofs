import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19310 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7578934 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩], 19⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
