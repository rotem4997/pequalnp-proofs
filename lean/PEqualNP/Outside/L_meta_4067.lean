import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_4067 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → x5 (x2 x6)) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → x4 (x3 x6) := by
  intro x1
  dsimp only
  decide +kernel
