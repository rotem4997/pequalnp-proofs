import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7255 : ∀ (x1 : ℕ), x1 = (0 : ℕ) → ∀ (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x5 : Fin x1) (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x6 ≠ x8 → x6 ≠ x9 → x7 ≠ x8 → x7 ≠ x9 → x8 ≠ x9 → x3.Adj x6 x7 → x3.Adj x7 x8 → x3.Adj x8 x9 → ¬x3.Adj x9 x6) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin x1 → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x3.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x3 x4.size := by
  intro n hn G C hex
  obtain ⟨a, _⟩ := hex
  subst hn
  exact a.elim0
