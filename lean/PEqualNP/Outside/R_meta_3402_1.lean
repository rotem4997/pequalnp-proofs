import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_3402_1
    (prependTwoOr : ∀ (x2 : Finset (Fin 9)) (x1 : Circuit),
      FanInTwo x1 → x2.card ≤ 2 → notCount x1 = 0 →
      ∃ D : Circuit, FanInTwo D ∧ notCount D = 0 ∧ D.size = x1.size + 2 ∧
        ∀ x6 : Fin 9 → Bool,
          D.eval (List.ofFn x6) =
            x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, decide (∃ x7 ∈ x2, x6 x7 = true)]))
    (monoBoundG9 : ∀ (D : Circuit),
      FanInTwo D → notCount D = 0 →
      (∀ x6 : Fin 9 → Bool,
        D.eval (List.ofFn x6) =
          ([((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
            ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
            ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
            ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
            fun (x7 : Fin 9 × Fin 9) => x6 x7.1 && x6 x7.2)) →
      16 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x1 = (0 : ℕ) → (∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x7 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x7.1 && x6 x7.2) → (14 : ℕ) ≤ x1.size := by
  intro x1 x2 hfan hcard hnot heval
  obtain ⟨D, hDfan, hDnot, hDsz, hDev⟩ := prependTwoOr x2 x1 hfan hcard hnot
  have h16 := monoBoundG9 D hDfan hDnot (fun x6 => (hDev x6).trans (heval x6))
  omega
