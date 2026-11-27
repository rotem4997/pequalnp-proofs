import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_3741 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 8 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 6), (2, 3), (2, 4), (2, 6)] : List (Fin 7 × Fin 7))) := by
  intro C hC
  subst hC
  refine ⟨by decide, rfl, by decide, by decide⟩
