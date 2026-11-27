import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6024

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6024

theorem PEqualNP.Outside.L_meta_6024 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.gates = [] → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C π _ _ hg
  have hev : ∀ x : List Bool, C.eval x = x.getD C.output false := by
    intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hg]
  by_cases h1 : C.output < 10
  · refine ⟨fun i => decide (i = π ⟨C.output, h1⟩), ?_⟩
    rw [hev]
    have e : (List.ofFn ((fun i => decide (i = π ⟨C.output, h1⟩)) ∘ π) ++
        [decide ((0 : Fin 10) = π ⟨C.output, h1⟩) && decide ((2 : Fin 10) = π ⟨C.output, h1⟩)]).getD C.output false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h1), List.getElem?_ofFn, dif_pos h1]
      simp
    rw [e]
    generalize π ⟨C.output, h1⟩ = j
    revert j
    decide
  · by_cases h2 : C.output = 10
    · refine ⟨fun i => decide (i = 0 ∨ i = 2), ?_⟩
      rw [hev, h2]
      have e : (List.ofFn ((fun i : Fin 10 => decide (i = 0 ∨ i = 2)) ∘ π) ++
          [decide ((0 : Fin 10) = 0 ∨ (0 : Fin 10) = 2) && decide ((2 : Fin 10) = 0 ∨ (2 : Fin 10) = 2)]).getD 10 false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
        simp
      rw [e]
      decide
    · refine ⟨fun _ => true, ?_⟩
      rw [hev, List.getD_eq_default _ _ (by simp; omega)]
      decide
