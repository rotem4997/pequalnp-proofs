import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4043_617
    (h1 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), D.size ≤ C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ (∀ (xs : List Bool), xs.length = n → D.eval xs = C.eval xs) ∧ (D.size = 0 ∨ D.output < n ∨ D.output = n + D.size - 1))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (x1.size = 0 ∨ x1.output < (26 : ℕ) ∨ x1.output = (26 : ℕ) + x1.size - 1) → (58 : ℕ) ≤ x1.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false → (x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) → (58 : ℕ) ≤ x1.size := by
  intro x1 x2 hm hcomp
  obtain ⟨D, hsz, hmD, hev, hnf⟩ := h1 26 x1 hm
  have hcomp' : ∀ (x4 : Fin (26 : ℕ) → Bool), x4 x2 = Bool.false →
      (D.eval (List.ofFn x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true) := by
    intro x4 hx
    rw [hev (List.ofFn x4) (by simp)]
    exact hcomp x4 hx
  exact le_trans (h2 D x2 hmD hcomp' hnf) hsz
