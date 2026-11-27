import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7581 : have x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → ℕ := fun (x1 x2 : Fin (21 : ℕ)) => if (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] then (1 : ℕ) else (0 : ℕ); ∀ (x2 x3 : Fin (21 : ℕ)), ∑ x4 : Fin (21 : ℕ), x1 x2 x4 * x1 x3 x4 = (1 : ℕ) + if x2 = x3 then (4 : ℕ) else (0 : ℕ) := by
  dsimp only
  set_option synthInstance.maxSize 100000 in
  set_option synthInstance.maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  decide +kernel
