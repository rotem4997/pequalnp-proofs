import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3302_1
    (core : ¬ HasCircuitSize 8
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
        (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) ||
        (x 7 && x 4) || x 0 || x 3) 13)
    (embed : ∀ (p t : Circuit), FanInTwo p → FanInTwo t →
      (∀ x : Fin 8 → Bool,
        t.eval (p.wires (List.ofFn x) ++ [false]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
           (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
           (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) ||
           (x 7 && x 4) || x 0 || x 3)) →
      HasCircuitSize 8
        (fun x : Fin 8 → Bool =>
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
           (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) ||
           (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) ||
           (x 7 && x 4) || x 0 || x 3)) (p.size + t.size)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size ≤ (4 : ℕ) →         x2.size + x3.size ≤ (13 : ℕ) →           (8 : ℕ) ≤ x4 →             x4 < (8 : ℕ) + x2.size →               have x11 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x11 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x11);               have x12 : (Fin (8 : ℕ) → Bool) → Bool := fun (x12 : Fin (8 : ℕ) → Bool) => (x11 x12).getD x4 Bool.false;               (∀ (x13 : Fin (8 : ℕ) → Bool), x1 x13 = Bool.false → (x13 (0 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ))) = Bool.true → x12 x13 = Bool.true) → (∀ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x11 x14 ++ [x12 x14]) = x1 x14) → ∃ (x15 : Fin (8 : ℕ) → Bool), x3.eval (x11 x15 ++ [Bool.false]) ≠ (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro p t i fp ft hp hsum hge hlt hsens heval
  by_contra hcon
  push Not at hcon
  obtain ⟨C, hCfan, hCsize, hCeval⟩ := embed p t fp ft hcon
  exact core ⟨C, hCfan, hCsize.trans hsum, hCeval⟩
