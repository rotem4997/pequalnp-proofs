import Mathlib
import PEqualNP.Defs

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1977 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 ≠ x3 → x2 ≠ x4 → x3 ≠ x4 → x2 - x5 ∈ x1 → x3 - x5 ∈ x1 → x4 - x5 ∈ x1 → ∃ (x12 : Fin (13 : ℕ)), ∀ (x13 : Fin (13 : ℕ)), x2 - x13 ∉ x1 → x3 - x13 ∉ x1 → x4 - x13 ∉ x1 → x12 - x13 ∈ x1 := by
  intro x1
  show ∀ (x2 x3 x4 x5 : Fin 13), x2 ≠ x3 → x2 ≠ x4 → x3 ≠ x4 → x2 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → x3 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → x4 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → ∃ (x12 : Fin 13), ∀ (x13 : Fin 13), x2 - x13 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x3 - x13 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x4 - x13 ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x12 - x13 ∈ ({0, 1, 3, 9} : Finset (Fin 13))
  decide +kernel
