import PEqualNP.Defs

-- Credit: the case-split reduction shape of foudress (R_meta_1710_64, #23768) and willakone
-- (R_meta_17910_64). This is a split on x1 at 50; each piece is the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_17440_2
    (caseA : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < (50 : ℕ) → (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ))
    (caseB : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (50 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), (∀ x10 ∈ x3, x10.1 ∈ x8 ∨ x10.2 ∈ x9) ∧ x3.card + x8.card + x9.card ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4
  rcases Nat.lt_or_ge x1 (50 : ℕ) with h | h
  · exact @caseA x1 x2 x3 x4 h
  · exact @caseB x1 x2 x3 x4 h
