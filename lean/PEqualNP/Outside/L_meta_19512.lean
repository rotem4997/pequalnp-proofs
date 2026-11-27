import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19512 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236753 : ℕ).testBit (5 * u.val + v.val)) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.or, [13, 12]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [15, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g mem
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · change ∀ u v : Fin 5, _
    decide +kernel
