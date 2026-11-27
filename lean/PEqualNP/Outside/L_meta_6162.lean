import Mathlib
import PEqualNP.Defs

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_6162 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : x2 → x2 → Prop := fun (x4 x5 : x2) => (∀ (x6 : x1), x6 ∈ x5 ↔ ∀ x7 ∈ x4, ¬x3 x7 x6) ∧ (∀ x6 ∉ x4, ∃ x8 ∈ x5, x3 x6 x8) ∧ (¬∃ (x6 : x1), ∀ x7 ∈ x4, x3 x7 x6) ∧ ¬∃ (x6 : x1), ∀ x7 ∈ x5, x3 x6 x7; have x5 : x2 → x2 := fun (x5 : x2) => id (Finset.filter fun (x6 : x1) => ∀ x7 ∈ x5, ¬x3 x7 x6) Finset.univ; have x6 : x2 → x2 := fun (x6 : x2) => Finset.image (fun (x7 : x1) => -x7) x6; ∀ (x7 x8 x9 : x1), x7 < x8 → x8 < x9 → (¬∃ (x12 : x1), x3 x7 x12 ∧ x3 x8 x12 ∧ x3 x9 x12) → x4 {x7, x8, x9} (x5 {x7, x8, x9}) ∧ x4 (x6 (x5 {x7, x8, x9})) (x6 {x7, x8, x9}) := by
  intro x1 x2 x3
  dsimp only [id]
  decide +kernel
