import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1938_741
    (hPair : ∀ ops : List ℕ, ops.length ≤ 2 →
      ∃ a b : Fin 11, a ≤ b ∧ ∀ xs : List Bool, xs.length = 10 →
        GateOp.or.eval (ops.map (fun i => xs.getD i false)) =
          (xs.getD a.val false || xs.getD b.val false))
    (hBound : ∀ (a b : Fin 11) (C : Circuit), a ≤ b → FanInTwo C → C.size ≤ 13 →
      ∃ k : BitVec 9,
        let x : Fin 9 → Bool := fun i => k.getLsbD i.val
        let u := List.ofFn x ++ [!x 0]
        C.eval (u ++ [u.getD a.val false || u.getD b.val false]) ≠
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
            (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
              (fun e => x e.1 && x e.2)) :
∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))
 := by
  intro ops hLen C hFan hSize
  obtain ⟨a, b, hOrder, hPairValue⟩ := hPair ops hLen
  obtain ⟨k, hk⟩ := hBound a b C hOrder hFan hSize
  let x : Fin 9 → Bool := fun i => k.getLsbD i.val
  refine ⟨x, ?_⟩
  let u := List.ofFn x ++ [!x 0]
  have hLenU : u.length = 10 := by simp [u]
  change C.eval (u ++ [GateOp.or.eval (ops.map (fun i => u.getD i false))]) ≠ _
  rw [hPairValue u hLenU]
  simpa only [x, u, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using hk
