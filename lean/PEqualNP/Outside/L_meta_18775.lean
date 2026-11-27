import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18775_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepW w g) (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem eval_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (h : C.output < n) :
    C.eval (List.ofFn x) = x ⟨C.output, h⟩ := by
  change (C.gates.foldl stepW (List.ofFn x)).getD C.output false = x ⟨C.output, h⟩
  rw [foldl_getD_lt C.gates (List.ofFn x) C.output (by simp [h])]
  simp [List.getD_eq_getElem?_getD, h]

theorem rhs_false (k : Fin 10) :
    let x : Fin 10 → Bool := fun i => decide (i = k)
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
     x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
     x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) = false := by
  revert k
  decide

end PEqualNP.Outside.L_meta_18775_aux

theorem PEqualNP.Outside.L_meta_18775 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (10 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  intro C hout _ _ _
  let k : Fin 10 := ⟨C.output, hout⟩
  refine ⟨fun i => decide (i = k), ?_⟩
  rw [PEqualNP.Outside.L_meta_18775_aux.eval_lt C (fun i => decide (i = k)) hout,
      PEqualNP.Outside.L_meta_18775_aux.rhs_false k]
  simp [k]
