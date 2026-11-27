import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19041 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4990 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
