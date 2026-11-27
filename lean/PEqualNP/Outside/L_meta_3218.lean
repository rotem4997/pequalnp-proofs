import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3218 : ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 :=
  ⟨0, fun x2 => Nat.zero_le x2⟩
