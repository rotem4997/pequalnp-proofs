import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17455_222
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (59 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → x1.output < (26 : ℕ) + x1.size → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ x6 ≠ (0 : Fin (13 : ℕ)) ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (59 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> assumption
