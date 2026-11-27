import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3037 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2],   have x4 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x4 : Finset (Fin x1)) (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide ¬∃ x7 ∈ x4, x2 x6 x7) (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) x5;   ∀ (x5 : Finset (Fin x1)), Fintype.card { x6 : Fin x1 // x4 x5 (Fin.natAdd x1 x6) = Bool.true } = x5.card ∧ ¬∃ (x6 : Fin x1) (x7 : Fin x1), x2 x6 x7 ∧ x4 x5 (Fin.castAdd x1 x6) = Bool.true ∧ x4 x5 (Fin.natAdd x1 x7) = Bool.true := by
  intro n I _ x4 Y
  have h1 : ∀ l : Fin n, x4 Y (Fin.natAdd n l) = decide (l ∈ Y) := fun l => Fin.addCases_right l
  have h2 : ∀ p : Fin n, x4 Y (Fin.castAdd n p) = decide (¬∃ x7 ∈ Y, I p x7) := fun p => Fin.addCases_left p
  constructor
  · simp only [h1, decide_eq_true_eq]
    rw [Fintype.card_subtype]
    simp
  · rintro ⟨p, l, hI, hp, hl⟩
    rw [h2] at hp
    rw [h1] at hl
    simp only [decide_eq_true_eq] at hp hl
    exact hp ⟨l, hl, hI⟩
