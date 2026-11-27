import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19049

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [5, 6]⟩,
  ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4478 : ℕ).testBit (4 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_19049

theorem PEqualNP.Outside.L_meta_19049 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4478 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19049.C0, PEqualNP.Outside.L_meta_19049.fan, by decide, PEqualNP.Outside.L_meta_19049.rep⟩
