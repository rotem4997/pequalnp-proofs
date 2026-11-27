import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2954_aux

open PEqualNP.CircuitLowerBounds

theorem fold_rep (k : ℕ) : ∀ w : List Bool,
    (List.replicate k ({ op := GateOp.or, inputs := [] } : Gate)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
      = w ++ List.replicate k false := by
  induction k with
  | zero => intro w; simp
  | succ k ih =>
    intro w
    rw [List.replicate_succ, List.foldl_cons, ih]
    simp [GateOp.eval]
    rfl

theorem getD_rep (w : List Bool) (k i : ℕ) :
    (w ++ List.replicate k false).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_append_left h]
  · have h2 : w[i]? = none := List.getElem?_eq_none (by omega)
    rw [h2, List.getElem?_append_right (by omega), List.getElem?_replicate]
    split <;> rfl

end PEqualNP.Outside.L_meta_2954_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2954_aux in
theorem PEqualNP.Outside.L_meta_2954 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) (x4 : ℕ), ({ gates := x1.gates ++ List.replicate x2 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x3)).getD x4 Bool.false = (x1.wires (List.ofFn x3)).getD x4 Bool.false := by
  intro x1 x2 x3 x4
  unfold Circuit.wires
  rw [List.foldl_append, fold_rep, getD_rep]
