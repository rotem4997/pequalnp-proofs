import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-18627`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_18627_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 → x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} → (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 → x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} → (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (7 : ℕ)), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 ∈ x1.gates, x6.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x1 → x2 ∈ PEqualNP.CircuitLowerBounds.fanoLines x3 → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x3} → (∃ x11 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (2 : ℕ) ≤ List.count ((14 : ℕ) + x11) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)) → False) := by
  classical
  intro h1 h2 x1 x2 x3
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
