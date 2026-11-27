import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3074_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) →
      (15 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) →
      (15 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      (15 : ℕ) ≤ x1.size := by
  classical
  intro x1 hfan hdiff hdiff2 hcomp hfilt
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · exact h1 x1 hfan hdiff hdiff2 hcomp hfilt h
  · exact h2 x1 hfan hdiff hdiff2 hcomp hfilt h
