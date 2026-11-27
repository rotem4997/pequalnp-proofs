import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19498

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def W : Circuit := ⟨[⟨.or, [5, 0]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [10, 2]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [15, 13]⟩, ⟨.not, [16]⟩, ⟨.and, [17, 18]⟩], 19⟩

theorem fan : FanInTwo W := by
  intro g hg
  simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7578841 : ℕ).testBit (5 * u.val + v.val)) W := by decide +kernel

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_19498

theorem PEqualNP.Outside.L_meta_19498 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7578841 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨L_meta_19498.W, L_meta_19498.fan, by decide, L_meta_19498.rep⟩
