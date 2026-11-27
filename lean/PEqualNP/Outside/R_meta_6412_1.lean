import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6412_1
    (h1 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ x1.output < 14 ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true))
    (h2 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ 14 ≤ x1.output ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true))
    : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs.Nodup) ∧ PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x2 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x3 ∈ PEqualNP.CircuitLowerBounds.fanoLines x4 ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) := by
  rintro ⟨C, hA, hB, hC, hD⟩
  by_cases h : C.output < 14
  · exact h1 ⟨C, hA, hB, hC, h, hD⟩
  · exact h2 ⟨C, hA, hB, hC, Nat.le_of_not_lt h, hD⟩
