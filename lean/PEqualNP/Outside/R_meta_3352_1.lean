import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3352_1
    (h1 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)));
          ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo x2 →
            (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
            (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →
            x2.size < (15 : ℕ) →
            (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) →
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1)
    (h2 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)));
          ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo x2 →
            (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
            (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →
            x2.size = (15 : ℕ) →
            (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) →
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)));
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →
      x2.size ≤ (15 : ℕ) →
      (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) →
      PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1 := by
  intro _ x2 hfan hnot hwire hsize hcount
  by_cases hlt : x2.size < 15
  · exact h1 x2 hfan hnot hwire hlt hcount
  · have heq : x2.size = 15 := by omega
    exact h2 x2 hfan hnot hwire heq hcount
