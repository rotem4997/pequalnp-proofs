import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_11463 : ∀ (x1 : Fin (7 : ℕ) → Bool), ∃ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∃ (x3 : Fin (7 : ℕ)), (∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.true → x2.testBit ↑(x4 + x3) = Bool.true) ∧ ∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.false → x1 (x4 + (1 : Fin (7 : ℕ))) = Bool.false → x1 (x4 + (3 : Fin (7 : ℕ))) = Bool.false → x2.testBit ((7 : ℕ) + ↑(x4 + x3)) = Bool.true := by
  decide +kernel
