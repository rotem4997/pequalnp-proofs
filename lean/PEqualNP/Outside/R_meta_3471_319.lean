import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3471_319
    (h1 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
      x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size →
      (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x4.size)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      ¬ PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
      x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size →
      (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hq hN hcard huniq hao houtge houtlt hor hright hfalse
  by_cases hr2 : PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ)
  · exact h1 x1 x2 x3 x4 hq hN hcard huniq hao hr2 houtge houtlt hor hright hfalse
  · exact h2 x1 x2 x3 x4 hq hN hcard huniq hao hr2 houtge houtlt hor hright hfalse
