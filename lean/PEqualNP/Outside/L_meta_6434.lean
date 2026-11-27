import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6434

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6434

theorem PEqualNP.Outside.L_meta_6434 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → PEqualNP.ReadK.IsReadK x2 x7 (1 : ℕ) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.ReadK.IsReadK x2 x11 (1 : ℕ) ∧ x11.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x12 : Fin x2 → Bool), x11.eval (List.ofFn x12) = x7.eval (List.ofFn x12) := by
  refine ⟨1, ?_⟩
  intro n G _ _ _ C hC _ hR
  exact ⟨C, hC, hR, by omega, fun _ => rfl⟩
