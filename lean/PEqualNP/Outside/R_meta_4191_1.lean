import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- Separate the already read-1 case from the conversion: if C is already read-1,
-- take R = C with constant 1; otherwise the conversion itself is the new gap.
theorem PEqualNP.Outside.R_meta_4191_1
    (read1 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → PEqualNP.ReadK.IsReadK x2 x7 (1 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.ReadK.IsReadK x2 x10 (1 : ℕ) ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = x7.eval (List.ofFn x11))
    (nonread1 : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ¬ PEqualNP.ReadK.IsReadK x2 x7 (1 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.ReadK.IsReadK x2 x10 (1 : ℕ) ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = x7.eval (List.ofFn x11)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x2 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.ReadK.IsReadK x2 x10 (1 : ℕ) ∧ x10.size + (1 : ℕ) ≤ x1 * (x7.size + (1 : ℕ)) ∧ ∀ (x11 : Fin x2 → Bool), x10.eval (List.ofFn x11) = x7.eval (List.ofFn x11) := by
  obtain ⟨a1, ha1⟩ := read1
  obtain ⟨a2, ha2⟩ := nonread1
  refine ⟨a1 + a2, ?_⟩
  intro n G inst hdeg hgirth C hmono hgraph
  by_cases h : PEqualNP.ReadK.IsReadK n C 1
  · obtain ⟨R, hmR, hread, hsizeR, hRC⟩ := ha1 n G hdeg hgirth C hmono hgraph h
    exact ⟨R, hmR, hread, hsizeR.trans (Nat.mul_le_mul (Nat.le_add_right a1 a2) le_rfl), hRC⟩
  · obtain ⟨R, hmR, hread, hsizeR, hRC⟩ := ha2 n G hdeg hgirth C hmono hgraph h
    exact ⟨R, hmR, hread, hsizeR.trans (Nat.mul_le_mul (Nat.le_add_left a2 a1) le_rfl), hRC⟩
