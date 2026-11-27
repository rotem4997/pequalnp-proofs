import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2319_733
    (hExtract : ∀ (C : Circuit) (T : Finset (Fin 9 → Bool)), FanInTwo C →
      ∃ W : List (Finset (Fin 9 → Bool)),
        let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ [∅] ++ W.take j
        W.length = C.size ∧
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b ∨
            W.getD j ∅ = T \ A a) ∧
        ∀ x ∈ T, C.eval (List.ofFn x ++ [false]) = true ↔ x ∈ (V W.length).getD C.output ∅)
    (hLower :
      let T : Finset (Fin 9 → Bool) := Finset.univ.filter (fun x => (x 0 && x 1) = false)
      let E : Finset (Fin 9 × Fin 9) :=
        {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
          (3, 8), (5, 7), (6, 8), (8, 5)}
      ¬ ∃ (W : List (Finset (Fin 9 → Bool))) (o : ℕ),
        let V (j : ℕ) := (List.ofFn fun i : Fin 9 => T.filter (fun x => x i)) ++ [∅] ++ W.take j
        W.length ≤ 13 ∧
        (∀ j < W.length, let A := fun i => (V j).getD i ∅
          ∃ a b : ℕ, W.getD j ∅ = A a ∪ A b ∨ W.getD j ∅ = A a ∩ A b ∨
            W.getD j ∅ = T \ A a) ∧
        ∀ x ∈ T, x ∈ (V W.length).getD o ∅ ↔
          ∃ e ∈ E, x e.1 = true ∧ x e.2 = true) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ))) = Bool.false → x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size
 := by
  classical
  intro C hC hEval
  by_contra! hSize
  let T : Finset (Fin 9 → Bool) := Finset.univ.filter (fun x => (x 0 && x 1) = false)
  let E : Finset (Fin 9 × Fin 9) :=
    {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
      (3, 8), (5, 7), (6, 8), (8, 5)}
  obtain ⟨W, hLength, hTrace, hValues⟩ := hExtract C T hC
  apply hLower
  refine ⟨W, C.output, by omega, hTrace, ?_⟩
  intro x hx
  have domain : (x 0 && x 1) = false := (Finset.mem_filter.mp hx).2
  calc
    _ ↔ C.eval (List.ofFn x ++ [false]) = true := (hValues x hx).symm
    _ ↔ ∃ e ∈ E, x e.1 = true ∧ x e.2 = true := by
      rw [hEval x domain]
      simp [E, Bool.and_eq_true, Bool.or_eq_true, or_assoc]
