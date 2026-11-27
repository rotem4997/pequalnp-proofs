import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3849_1
    (base :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0, false]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (bypass :
      ∀ C : Circuit, FanInTwo C → ∀ j : Fin 11,
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (w : List Bool) (b : Bool), w.length = 10 →
            D.eval (w ++ [b]) = C.eval (w ++ [w.getD j.val false])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∀ (x4 : Fin (9 : ℕ)), ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x4]) ≠ (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
  intro C hC hs i
  obtain ⟨D, hD, hsize, heval⟩ := bypass C hC (Fin.castAdd 2 i)
  obtain ⟨x, hx⟩ := base D hD (hsize.trans_le hs)
  let w := List.ofFn x ++ [!x 0]
  have hw : w.length = 10 := by simp [w]
  have hi : w.getD (Fin.castAdd 2 i).val false = x i := by
    change (List.ofFn x ++ [!x 0]).getD i.val false = x i
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have he := heval w false hw
  rw [hi] at he
  refine ⟨x, ?_⟩
  change C.eval (w ++ [x i]) ≠ _
  rw [← he]
  exact hx
