import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The output wire is an input wire, or it is a gate wire.
theorem PEqualNP.Outside.R_meta_8947_233
    (inputOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 → x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) → (x4.output < x2 + x2) → x2 * x1 ≤ (100 : ℕ) * x4.size)
    (gateOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 → x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) → (x2 + x2 ≤ x4.output) → x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x13 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x15 x16 : Finset (Fin x2)), x16.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x15 x16 → x4.eval (PEqualNP.GenericRejection.incidenceInput x15 x16) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  by_cases h : (x4.output < x2 + x2)
  · exact inputOut x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h
  · exact gateOut x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 (by omega)
