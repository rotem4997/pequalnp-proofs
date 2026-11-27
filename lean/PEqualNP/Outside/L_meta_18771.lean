import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18771_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_getD (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
      = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem eval_input (C : Circuit) (x : List Bool) (h : C.output < x.length) :
    C.eval x = x.getD C.output false := foldl_getD _ _ _ h

theorem key : ∀ o : Fin 10, ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => (fun j : Fin 10 => decide (j = o)) (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && (fun j : Fin 10 => decide (j = o)) (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ)))) = false := by
  decide

end PEqualNP.Outside.L_meta_18771_aux

open PEqualNP.Outside.L_meta_18771_aux in
theorem PEqualNP.Outside.L_meta_18771 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (10 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ))) := by
  intro C ho _ _ _
  refine ⟨fun j => decide (j = ⟨C.output, ho⟩), ?_⟩
  rw [key ⟨C.output, ho⟩, eval_input C _ (by simpa using ho)]
  rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
  simp
