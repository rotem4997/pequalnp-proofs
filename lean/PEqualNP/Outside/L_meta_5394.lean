import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_5394 : ∀ C D : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit) → D = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 8 C ∧ C.size = 14 ∧ PEqualNP.TopForm.IsAO2 8 D ∧ D.size = 9 ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 C x = decide (∃ e ∈ ([(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (1, 7), (4, 7)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 D x = decide (∃ e ∈ ([(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (1, 7), (4, 7)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (1, 7), (4, 7)] : List (Fin 8 × Fin 8)), PEqualNP.Core.ReadTwiceAt 8 C (C.output - 8) e.1 e.2 ↔ e ∈ ([(1, 5), (3, 6)] : List (Fin 8 × Fin 8))) := by
  intro C D hC hD
  subst hC
  subst hD
  refine ⟨by decide, rfl, by decide, rfl, ?_, ?_, ?_⟩
  · intro x
    revert x
    decide
  · intro x
    revert x
    decide
  · decide
