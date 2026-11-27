import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_971_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C' ∧
        C'.size ≤ C.size ∧
        ∀ x : Fin 14 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C →
      (¬ ∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 14 C g1 g2) →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14,
            (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true) →
      27 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C →
      (∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 14 C g1 g2) →
      (∀ x : Fin 14 → Bool,
        C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14,
            (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true) →
      27 ≤ C.size) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro hNorm hFlat hNested C hMono hEval
  rcases hNorm C hMono with ⟨C', hMono', hRB', hSize', hEq'⟩
  have hEval' : ∀ x : Fin 14 → Bool,
      C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14,
          (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true := by
    intro x
    rw [hEq' x]
    exact hEval x
  by_cases hN : ∃ g1 g2 : ℕ,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C' g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C' g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.EdgeOwnership.InCone 14 C' g1 g2
  · exact le_trans (hNested C' hMono' hRB' hN hEval') hSize'
  · exact le_trans (hFlat C' hMono' hRB' hN hEval') hSize'
