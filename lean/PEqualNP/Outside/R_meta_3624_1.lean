import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The two pin shapes of the step, separated.
-- pos covers pins on wires 0 through 8: the extension is a product of literals.
-- neg covers pins touching wire 9: the extension is a literal times not x_0.
theorem PEqualNP.Outside.R_meta_3624_1
    (pos : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : Circuit), FanInTwo x3 → x3.size = (13 : ℕ) →
        List.countP (fun (x6 : Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →
          (∃ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ ↑x7 ≠ (9 : ℕ) ∧ ↑x8 ≠ (9 : ℕ)) →
            ∃ (x8 : Fin (9 : ℕ) → Bool),
              have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
              x3.eval (x9 ++ [GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠
                (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (neg : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : Circuit), FanInTwo x3 → x3.size = (13 : ℕ) →
        List.countP (fun (x6 : Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →
          (∃ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ (↑x7 = (9 : ℕ) ∨ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (0 : ℕ) ∧ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (9 : ℕ) ∧ ↑x8 = (0 : ℕ))) →
            ∃ (x8 : Fin (9 : ℕ) → Bool),
              have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
              x3.eval (x9 ++ [GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠
                (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →             (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ ¬(↑x7 = (0 : ℕ) ∧ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (9 : ℕ) ∧ ↑x8 = (0 : ℕ))) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen x3 hfan hsize hnot hgood
  obtain ⟨x7, x8, hne, hx1, h09, h90⟩ := hgood
  by_cases h7 : (x7 : ℕ) = 9
  · exact neg x1 hlen x3 hfan hsize hnot ⟨x7, x8, hne, hx1, Or.inl h7, h09, h90⟩
  · by_cases h8 : (x8 : ℕ) = 9
    · exact neg x1 hlen x3 hfan hsize hnot ⟨x7, x8, hne, hx1, Or.inr h8, h09, h90⟩
    · exact pos x1 hlen x3 hfan hsize hnot ⟨x7, x8, hne, hx1, h7, h8⟩
