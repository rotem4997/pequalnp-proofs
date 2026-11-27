import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_8297_899
    (compilePair : let f : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      ∀ (A B : Circuit), FanInTwo A → Monotone2 B →
        (∀ x : Fin 10 → Bool, B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) = f x) →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ A.size + B.size + 1 ∧
          ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x)
    (notNeverHelps : let f : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      ∀ D : Circuit, FanInTwo D → D.size ≤ 19 →
        (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x) →
        ∃ E : Circuit, Monotone2 E ∧ E.size ≤ D.size ∧
          ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = f x)
    (monoBound : let f : (Fin 10 → Bool) → Bool := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
      ∀ E : Circuit, Monotone2 E →
        (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = f x) → 20 ≤ E.size) :
  (have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.size + x3.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [!x2.eval (List.ofFn x7)]) = x1 x7) := by
  dsimp only
  intro A B hA hB hsz hcomp
  obtain ⟨D, hD, hszD, hfunD⟩ := compilePair A B hA hB hcomp
  obtain ⟨E, hE, hszE, hfunE⟩ := notNeverHelps D hD (by omega) hfunD
  have h20 := monoBound E hE hfunE
  omega
