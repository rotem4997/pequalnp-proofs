import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_126 : ∀ (R : Type) [CommRing R] (x y z : R), 24 * x * y * z = (x + y + z) ^ 3 - (x + y - z) ^ 3 - (x - y + z) ^ 3 + (x - y - z) ^ 3 := by
  intro R _ x y z
  ring
