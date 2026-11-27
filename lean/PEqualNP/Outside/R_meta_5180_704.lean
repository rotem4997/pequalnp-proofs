import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The output wire is either an input wire or a gate wire: the two children split the search
-- by that property.
theorem PEqualNP.Outside.R_meta_5180_704
    (inputOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → (x4.output < x2 + x2) → x2 * x1 ≤ (100 : ℕ) * x4.size)
    (gateOut :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → (x2 + x2 ≤ x4.output) → x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → (∀ (x12 : Finset (Fin (x2 + x2))), List.countP (fun (x13 : Fin x2) => Decidable.decide (Fin.natAdd x2 x13 ∈ x12)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x12 ↔ ∃ (x14 : Fin x2) (x15 : Fin x2), x14 ∈ x3 x15 ∧ x12 = {Fin.castAdd x2 x14, Fin.natAdd x2 x15})) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8
  by_cases h : x4.output < x2 + x2
  · exact inputOut x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h
  · exact gateOut x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 (by omega)
