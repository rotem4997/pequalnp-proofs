import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2841_13
    (baseline : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (expand :
      ∀ (C : Circuit) (S : Finset (Fin 9)), FanInTwo C → S.card ≤ 2 →
        ∃ D : Circuit, FanInTwo D ∧
          D.size ≤ C.size + (if S.card ≤ 1 ∨ S = {0, 4} then 1 else 2) ∧
          ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [false]) =
            C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ j ∈ S, x j = true)]))
    (overlapping :
      ∀ (C : Circuit) (S : Finset (Fin 9)), FanInTwo C →
        S.card = 2 → S ≠ {0, 4} → ¬ Disjoint S {0, 4} → C.size = 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ j ∈ S, x j = true)]) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
          (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2)) → False)
    (disjoint :
      ∀ (C : Circuit) (S : Finset (Fin 9)), FanInTwo C →
        S.card = 2 → S ≠ {0, 4} → Disjoint S {0, 4} → C.size = 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ j ∈ S, x j = true)]) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
          (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x6 ∈ x2, x5 x6 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) → (14 : ℕ) ≤ x1.size := by
  intro C S fan card computes
  obtain ⟨D, fanD, sizeD, evalD⟩ := expand C S fan card
  have sizeLower := baseline D fanD (by
    intro x
    rw [evalD x, computes x]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc])
  by_cases available : S.card ≤ 1 ∨ S = {0, 4}
  · simp only [ite_eq_left available] at sizeD
    omega
  have two : S.card = 2 := by
    by_contra hn
    apply available
    exact Or.inl (by omega)
  have new : S ≠ {0, 4} := fun eq => available (Or.inr eq)
  by_contra! short
  simp only [ite_eq_right available] at sizeD
  have tight : C.size = 13 := by omega
  by_cases separated : Disjoint S {0, 4}
  · exact disjoint C S fan two new separated tight computes
  · exact overlapping C S fan two new separated tight computes
