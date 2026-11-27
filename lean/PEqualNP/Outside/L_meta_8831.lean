import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8831_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    rw [List.getD_append _ _ _ _ hi]

end PEqualNP.Outside.L_meta_8831_aux

open PEqualNP.Outside.L_meta_8831_aux in
theorem PEqualNP.Outside.L_meta_8831 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → x1 ≤ x4.output ∧ x4.output < x1 + x4.size := by
  intro n K _ C hf ⟨u, v, huv⟩
  constructor
  · by_contra h
    simp only [not_le] at h
    have e := congrFun hf (fun j => decide (j = ⟨C.output, h⟩))
    have l : PEqualNP.MetaComplexity.circuitFun n C (fun j => decide (j = ⟨C.output, h⟩)) = true := by
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [fold_pre _ _ _ (by simpa using h)]
      simp [List.getD_eq_getElem?_getD, h]
    rw [l] at e
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun at e
    simp at e
  · by_contra h
    simp only [not_lt] at h
    have e := congrFun hf (fun _ => true)
    have l : PEqualNP.MetaComplexity.circuitFun n C (fun _ => true) = false := by
      unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
      have := fold_len C.gates (List.ofFn (fun _ : Fin n => true))
      unfold PEqualNP.CircuitLowerBounds.Circuit.size at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        unfold PEqualNP.CircuitLowerBounds.Circuit.wires; simp at this ⊢; omega)]
      rfl
    rw [l] at e
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun at e
    simp at e
    exact e u v huv
