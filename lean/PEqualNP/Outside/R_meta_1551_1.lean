import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1551_1 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1), (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) ∧
        (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates.head? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1), (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) ∧
        (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates.head? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧
        (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1), (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) ∧
        (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates.head? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) →
    ¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1), (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) s → 15 ≤ s) := by
  rintro ⟨C, hfan, hsize, heval, _⟩ _ _
  intro h
  exact absurd (h C.size ⟨C, hfan, le_rfl, heval⟩) (by omega)
