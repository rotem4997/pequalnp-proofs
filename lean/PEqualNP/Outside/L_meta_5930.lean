import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5930 : ∀ (x1 : List ℕ) (x2 x3 : ℕ), x3 < x1.length → (x1 ++ [x2]).getD x3 (0 : ℕ) = x1.getD x3 (0 : ℕ) := by
  intro L a i h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
