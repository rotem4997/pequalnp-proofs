import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18759
open PEqualNP.CircuitLowerBounds
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]


end PEqualNP.Outside.L_meta_18759
open PEqualNP.Outside.L_meta_18759
theorem PEqualNP.Outside.L_meta_18759 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (32 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 : Fin (32 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (32 : ℕ)) (x7 : Fin (32 : ℕ)), (↑x6 < (16 : ℕ) ∧ (16 : ℕ) ≤ ↑x7 ∧ ([(195 : ℕ), (32908 : ℕ), (281 : ℕ), (562 : ℕ), (1124 : ℕ), (2464 : ℕ), (12608 : ℕ), (25216 : ℕ), (34560 : ℕ), (19457 : ℕ), (38914 : ℕ), (4613 : ℕ), (9226 : ℕ), (10260 : ℕ), (20520 : ℕ), (49232 : ℕ)].getD ↑x6 (0 : ℕ)).testBit (↑x7 - (16 : ℕ)) = Bool.true) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (79 : ℕ) ≤ x1.size) := by
  intro C h _ _ computes
  let x (i : Fin 32) := decide (i.val = C.output)
  have one : C.eval (List.ofFn x) = true := by
    change (C.gates.foldl stepWire (List.ofFn x)).getD C.output false = true
    rw [foldl_getD_lt _ _ _ (by simpa)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos h,Option.getD_some,x,decide_true]
  obtain ⟨u,v,⟨hu,hv,_⟩,xu,xv⟩ := (computes x).1 one
  have eu : u.val = C.output := of_decide_eq_true xu
  have ev : v.val = C.output := of_decide_eq_true xv
  omega
