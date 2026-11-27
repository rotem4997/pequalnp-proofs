import PEqualNP.MetaComplexity.Helpers.Shannon
import PEqualNP.MetaComplexity.Helpers.Support

/-!
# One NOT gate: evaluation basics

Step 1 of the build plan. The fold inside
`Circuit.wires` is `Helpers.wiresFrom` (from `Shannon.lean`); this file restates its basic
facts for `Circuit.wires` with the output field free, so later files can rewrite with them.
-/

namespace PEqualNP.MetaComplexity.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- The wires of a circuit do not depend on its output field. -/
theorem on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

/-- `Circuit.wires` is the fold `wiresFrom`. -/
theorem on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

/-- The wire list has one wire per input bit and one per gate. -/
theorem on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

/-- Reading at or beyond the length gives `false`. -/
theorem on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

/-- The same for `wiresFrom`. -/
theorem on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

/-- The wires of `l1 ++ l2`: run `l2` on the wires of `l1`. -/
theorem on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

/-- One gate on a wire list: the old wires, then the gate's value. -/
theorem on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

/-- Input wire `i < n` of `List.ofFn x` reads `x i`, whatever the gates. -/
theorem on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

/-- The wire a gate reads in a list `w`, read through a list that extends `w`. -/
theorem on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

end PEqualNP.MetaComplexity.OneNot
