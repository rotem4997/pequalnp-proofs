import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19499

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.not, [17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_19499

theorem PEqualNP.Outside.L_meta_19499 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7586366 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19499.C0, PEqualNP.Outside.L_meta_19499.fan, by decide, PEqualNP.Outside.L_meta_19499.rep⟩
