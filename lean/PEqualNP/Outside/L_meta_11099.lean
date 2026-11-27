import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11099

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_11099

theorem PEqualNP.Outside.L_meta_11099 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (3 ≤ ((List.ofFn x).count true))) 10 := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · have key : ∀ x : Fin 5 → Bool, (⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = decide (3 ≤ ((List.ofFn x).count true)) := by decide
    exact key
