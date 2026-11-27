import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2756_1
    (h1 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → (x1.length ≤ (1 : ℕ) ∨ ∃ x3 ∈ x1, (10 : ℕ) ≤ x3) →
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) →
        (2 : ℕ) ≤ List.countP (fun g => (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any fun i => decide (i = 0 ∨ i = 9)) x4.gates →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
          have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];
          x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → (x1.length ≤ (1 : ℕ) ∨ ∃ x3 ∈ x1, (10 : ℕ) ≤ x3) →
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) →
        List.countP (fun g => (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any fun i => decide (i = 0 ∨ i = 9)) x4.gates ≤ (1 : ℕ) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
          have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];
          x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → (x1.length ≤ (1 : ℕ) ∨ ∃ x3 ∈ x1, (10 : ℕ) ≤ x3) →
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) →
        ∃ (x7 : Fin (9 : ℕ) → Bool),
          have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];
          x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hdeg x4 hfan hsz
  by_cases hc : 2 ≤ List.countP (fun g => (if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs).any fun i => decide (i = 0 ∨ i = 9)) x4.gates
  · exact h1 x1 hlen hdeg x4 hfan hsz hc
  · exact h2 x1 hlen hdeg x4 hfan hsz (by omega)
