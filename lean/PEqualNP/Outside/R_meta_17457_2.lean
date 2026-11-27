import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The last gate of the circuit is an AND gate or it is not, so the step is asked once under
-- each of the two cases and the two children together give the step by a case split.
theorem PEqualNP.Outside.R_meta_17457_2
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (20 : ℕ) + x2 ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (20 : ℕ) + x2 ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (20 : ℕ) + x2 ≤ x1.size := by
  intros x1 x2 x3 h1 h2 h3 h4
  by_cases hq : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact lastAnd x1 x2 x3 h1 h2 h3 h4 hq
  · exact lastOr x1 x2 x3 h1 h2 h3 h4 hq
