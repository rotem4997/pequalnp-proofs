import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17715`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17715_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(1 : ℕ), (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(1 : ℕ), (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(1 : ℕ), (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7)) [((0 : ℕ), (7 : ℕ))] → False) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
