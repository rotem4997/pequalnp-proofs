import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1938_1
    (h1 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) →
      (x1.length ≤ (1 : ℕ) ∨ ∃ i ∈ x1, (10 : ℕ) ≤ i) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : List ℕ), x1.length = (2 : ℕ) →
      (∀ i ∈ x1, i < (10 : ℕ)) → ((0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h3 : ∀ (x1 : List ℕ), x1.length = (2 : ℕ) →
      (∀ i ∈ x1, (1 : ℕ) ≤ i ∧ i < (9 : ℕ)) → ((4 : ℕ) ∈ x1 ∨ (6 : ℕ) ∈ x1 ∨ (7 : ℕ) ∈ x1) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (h4 : ∀ (x1 : List ℕ), x1.length = (2 : ℕ) →
      (∀ i ∈ x1, i = (1 : ℕ) ∨ i = (2 : ℕ) ∨ i = (3 : ℕ) ∨ i = (5 : ℕ) ∨ i = (8 : ℕ)) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) →
        ∃ (x6 : Fin (9 : ℕ) → Bool),
          have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];
          x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen x3 hfan hsz
  by_cases hc1 : x1.length ≤ 1 ∨ ∃ i ∈ x1, 10 ≤ i
  · exact h1 x1 hlen hc1 x3 hfan hsz
  · push_neg at hc1
    have hlen2 : x1.length = 2 := by omega
    have hlt10 : ∀ i ∈ x1, i < 10 := hc1.2
    by_cases hc2 : 0 ∈ x1 ∨ 9 ∈ x1
    · exact h2 x1 hlen2 hlt10 hc2 x3 hfan hsz
    · push_neg at hc2
      have hrange : ∀ i ∈ x1, 1 ≤ i ∧ i < 9 := by
        intro i hi
        have := hlt10 i hi
        have hne0 : i ≠ 0 := fun h => hc2.1 (h ▸ hi)
        have hne9 : i ≠ 9 := fun h => hc2.2 (h ▸ hi)
        omega
      by_cases hc3 : 4 ∈ x1 ∨ 6 ∈ x1 ∨ 7 ∈ x1
      · exact h3 x1 hlen2 hrange hc3 x3 hfan hsz
      · push_neg at hc3
        have hdeg3 : ∀ i ∈ x1, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 8 := by
          intro i hi
          have hr := hrange i hi
          have hne4 : i ≠ 4 := fun h => hc3.1 (h ▸ hi)
          have hne6 : i ≠ 6 := fun h => hc3.2.1 (h ▸ hi)
          have hne7 : i ≠ 7 := fun h => hc3.2.2 (h ▸ hi)
          omega
        exact h4 x1 hlen2 hdeg3 x3 hfan hsz
