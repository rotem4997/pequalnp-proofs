import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2913_1
    (hNil : ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x4 →
      x4.size ≤ (13 : ℕ) →
      ∃ (x7 : Fin (9 : ℕ) → Bool),
        let x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval []]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hSingle : ∀ (a : ℕ), a = (0 : ℕ) ∨ (9 : ℕ) ≤ a → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x4 →
      x4.size ≤ (13 : ℕ) →
      ∃ (x7 : Fin (9 : ℕ) → Bool),
        let x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval [x8.getD a Bool.false]]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))))
    (hPair : ∀ (a b : ℕ), a = (0 : ℕ) ∨ (9 : ℕ) ≤ a → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x4 →
      x4.size ≤ (13 : ℕ) →
      ∃ (x7 : Fin (9 : ℕ) → Bool),
        let x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))]
        x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval [x8.getD a Bool.false, x8.getD b Bool.false]]) ≠
          (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     x1 = [] ∨ x1.headD (10 : ℕ) = (0 : ℕ) ∨ (9 : ℕ) ≤ x1.headD (10 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hHead x4 hFan hSize
  cases x1 with
  | nil =>
    simpa using hNil x4 hFan hSize
  | cons a t =>
    have hA : a = (0 : ℕ) ∨ (9 : ℕ) ≤ a := by
      rcases hHead with hNilList | hA0 | hA9
      · cases hNilList
      · exact Or.inl (by simpa using hA0)
      · exact Or.inr (by simpa using hA9)
    cases t with
    | nil =>
      simpa using hSingle a hA x4 hFan hSize
    | cons b t' =>
      have hlen' : t'.length + 2 ≤ 2 := by simpa using hlen
      have ht' : t'.length = 0 := by omega
      have htNil : t' = [] := by simpa using ht'
      subst htNil
      simpa using hPair a b hA x4 hFan hSize
