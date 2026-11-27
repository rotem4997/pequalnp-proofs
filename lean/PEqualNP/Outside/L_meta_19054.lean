import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19054_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 8]⟩,
    ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_19054_aux

theorem PEqualNP.Outside.L_meta_19054 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4830 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19054_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_19054_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
