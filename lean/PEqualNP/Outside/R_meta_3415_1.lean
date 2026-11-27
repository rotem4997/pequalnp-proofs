import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3415_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
      (¬∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then Bool.false != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
      (¬∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then Bool.true != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (14 : ℕ) →
      (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) →
      (¬∃ x6 ∈ x1.gates, (0 : ℕ) ∈ x6.inputs ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      ∃ (x7 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x8 : Fin (9 : ℕ)) => if x8 = (0 : Fin (9 : ℕ)) then x2 != x7 (0 : Fin (9 : ℕ)) else x7 x8) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hfan hsize hlen hnot
  cases x2
  · exact h1 x1 hfan hsize hlen hnot
  · exact h2 x1 hfan hsize hlen hnot
