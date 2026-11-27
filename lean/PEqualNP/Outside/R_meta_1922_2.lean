import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1922_2 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →
      ∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), 4 ≤ (x1.gates.filter fun g => decide (v.val ∈ g.inputs)).length →
      ∃ T : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 T ∧ T.size + 4 ≤ x1.size ∧
        (∀ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [x 0 || x 4]) = ([(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8)] : List (Fin 9 × Fin 9)).any (fun e => e.1 != v && e.2 != v && x e.1 && x e.2))) →
    (∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), ∀ T : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 T →
      (∀ x : Fin 9 → Bool, T.eval (List.ofFn x ++ [x 0 || x 4]) = ([(0, 1), (1, 2), (2, 3), (0, 4), (3, 4), (0, 5), (1, 6), (2, 7), (5, 7), (3, 8), (5, 8), (6, 8)] : List (Fin 9 × Fin 9)).any (fun e => e.1 != v && e.2 != v && x e.1 && x e.2)) →
      11 ≤ T.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →
      (∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), (x1.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ 3) →
      15 ≤ x1.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       (15 : ℕ) ≤ x1.size := by
  intro step bound few C hC hrows
  by_cases h : ∀ v ∈ ([1, 2, 3, 5, 8] : List (Fin 9)), (C.gates.filter fun g => decide (v.val ∈ g.inputs)).length ≤ 3
  · exact few C hC hrows h
  · push Not at h
    obtain ⟨v, hv, h4⟩ := h
    obtain ⟨T, hT, hsize, hval⟩ := step C hC hrows v hv h4
    have := bound v hv T hT hval
    omega
