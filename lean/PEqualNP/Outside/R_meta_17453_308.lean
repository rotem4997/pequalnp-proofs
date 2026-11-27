import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17453_308
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → x1.size ≤ (23 : ℕ) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (59 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (23 : ℕ) < x1.size → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (59 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : x1.size ≤ (23 : ℕ)
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> first | assumption | omega
