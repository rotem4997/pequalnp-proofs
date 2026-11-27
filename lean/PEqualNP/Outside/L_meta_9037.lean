import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9037_aux

open PEqualNP.CircuitLowerBounds

theorem pre (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem wire_in (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    C.eval x = x.getD i false ∨ C.output ≠ i := by
  by_cases ho : C.output = i
  · left
    unfold Circuit.eval Circuit.wires
    obtain ⟨t, ht⟩ := pre C.gates x
    rw [← ht, ho]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · right; exact ho

end PEqualNP.Outside.L_meta_9037_aux

open PEqualNP.Outside.L_meta_9037_aux in
theorem PEqualNP.Outside.L_meta_9037 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output < (10 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C _ _ ho
  refine ⟨fun j => decide (j.val = C.output), ?_⟩
  have hl : C.output < (List.ofFn (fun j : Fin 10 => decide (j.val = C.output))).length := by
    simpa using ho
  rcases wire_in C _ C.output hl with h | h
  · rw [h]
    generalize hk : C.output = k at ho ⊢
    interval_cases k <;> decide
  · exact absurd rfl h
