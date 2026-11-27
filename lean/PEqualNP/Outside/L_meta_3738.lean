import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3738 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 8 C ∧ C.size = 9 ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (1, 7), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), PEqualNP.Core.ReadTwiceAt 8 C (C.output - 8) e.1 e.2 ↔ e ∈ ([(0, 7), (1, 7)] : List (Fin 8 × Fin 8))) := by
  intro C hC
  subst hC
  refine ⟨by decide, rfl, ?_, ?_⟩
  · intro x
    revert x
    set_option maxRecDepth 100000 in decide
  · set_option maxRecDepth 100000 in decide
