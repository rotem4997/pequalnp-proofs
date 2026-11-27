import Mathlib
import PEqualNP.Defs

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_6985 : ∀ (x1 : Fin (16 : ℕ)) (x2 : Fin (13 : ℕ)) (x3 : Fin (3 : ℕ)),   have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ));   have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑((x5 - x2) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x3 (0 : Fin (13 : ℕ))) = Bool.true};   (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), (∀ x9 ∈ x5, ¬x4 x9 x8) ∧ x4 x6 x8) ∧ (¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x5, x4 x7 x6) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x5, ¬x4 x8 x7) → x4 x6 x7 := by
  intro x1 x2 x3
  fin_cases x1 <;> fin_cases x3 <;>
    (revert x2; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; decide +kernel)
