import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_752 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  intro s
  let f := fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)
  change HasCircuitSize 4 f s ↔ 3 ≤ s
  constructor
  · intro hc
    have hd : ∀ i : Fin 4, ∃ x : Fin 4 → Bool, f (Function.update x i (!x i)) ≠ f x := by
      dsimp only [f]
      decide +kernel
    have hs := PEqualNP.MetaComplexity.Helpers.dep_lower 4 f hd s hc
    omega
  · intro hs
    let C : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩
    refine ⟨C, ?_, hs, ?_⟩
    · simp [C, FanInTwo]
    · dsimp only [C, f]
      decide +kernel
