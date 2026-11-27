import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The full Petersen lower bound at 19 gates rules out a 17-gate circuit
-- together with one complemented extended input: add the AND and NOT input
-- gates in front, producing a 19-gate circuit over the original ten inputs.
theorem PEqualNP.Outside.R_meta_4817_1
    (fullLower :
      ¬ PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ)
        (fun x : Fin (10 : ℕ) → Bool =>
          x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) ||
          x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
          x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) ||
          x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
          x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) ||
          x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
          x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
          x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
          x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
          x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
          x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
          x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
          x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
          x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
          x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))
        (19 : ℕ))
    (encode :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (k : Fin (12 : ℕ)),
        PEqualNP.MetaComplexity.FanInTwo C →
        C.size ≤ (17 : ℕ) →
        (∀ x : Fin (10 : ℕ) → Bool,
          have x6 : List Bool :=
            List.ofFn x ++
              [x (0 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ))];
          C.eval (x6 ++ [!x6.getD (↑k) Bool.false]) =
            (fun x : Fin (10 : ℕ) → Bool =>
              x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) ||
              x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
              x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) ||
              x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
              x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) ||
              x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
              x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
              x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
              x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
              x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
              x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
              x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
              x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
              x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
              x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))) x) →
        PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ)
          (fun x : Fin (10 : ℕ) → Bool =>
            x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) ||
            x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) ||
            x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) ||
            x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) ||
            x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) ||
            x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) ||
            x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
            x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
            x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
            x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
            x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) ||
            x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) ||
            x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) ||
            x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) ||
            x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))
          (19 : ℕ)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (17 : ℕ) →
      ∃ (x5 : Fin (10 : ℕ) → Bool),
        have x6 : List Bool :=
          List.ofFn x5 ++
            [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];
        x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠
          (fun (x7 : Fin (10 : ℕ) → Bool) =>
            x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) ||
            x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) ||
            x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) ||
            x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) ||
            x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) ||
            x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) ||
            x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
            x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
            x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
            x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
            x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) ||
            x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) ||
            x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) ||
            x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) ||
            x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5 := by
  intro C k hfan hsize
  by_contra hall
  push_neg at hall
  apply fullLower
  apply encode C k hfan hsize
  intro x
  exact not_not.mp (hall x)
