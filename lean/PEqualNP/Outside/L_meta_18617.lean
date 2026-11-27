import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_18617 : (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(1 : Fin (13 : ℕ)), (2 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) := by
  let C : Circuit := ⟨[⟨.or, [13, 18]⟩, ⟨.or, [27, 24]⟩, ⟨.and, [1, 28]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [30, 25]⟩, ⟨.and, [2, 31]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [33, 21]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [36, 23]⟩, ⟨.and, [10, 37]⟩, ⟨.or, [29, 32]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [40, 38]⟩], 41⟩
  refine ⟨C, (by decide), (by decide), (by decide), (by decide), (by decide), ?_⟩
  intro x
  simp [C, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
    Fin.exists_fin_succ, Bool.or_eq_true, Bool.and_eq_true]
  tauto
