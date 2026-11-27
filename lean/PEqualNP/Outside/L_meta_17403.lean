import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
set_option maxRecDepth 1000000 in
theorem PEqualNP.Outside.L_meta_17403 : have x1 : Finset (Fin (13 : ℕ)) := Finset.univ; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → {x5 ∈ x1 | ∀ x6 ∈ x3, ¬x2 x6 x5}.card ≤ (3 : ℕ) := by
  decide +kernel
