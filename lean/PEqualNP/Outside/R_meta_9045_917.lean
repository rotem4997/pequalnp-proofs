import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The output wire is an input wire, or it is a gate wire.
theorem PEqualNP.Outside.R_meta_9045_917
    (inputOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → (x4.output < x2 + x2) → x2 * x1 ≤ (100 : ℕ) * x4.size)
    (gateOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → (x2 + x2 ≤ x4.output) → x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9
  by_cases h : (x4.output < x2 + x2)
  · exact inputOut x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h
  · exact gateOut x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 (by omega)
