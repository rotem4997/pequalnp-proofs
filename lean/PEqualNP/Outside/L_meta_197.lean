import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open CircuitLowerBounds

private def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem readEarlierWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (appendWire w g).length := by simp [appendWire]; omega
    rw [List.foldl_cons, ih (appendWire w g) hi']
    simp only [appendWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- Replacing a gate that already outputs true preserves the entire list of wire values. -/
private theorem forceTrue (gs : List Gate) (w : List Bool) (j : ℕ)
    (h : (gs.foldl appendWire w).getD (w.length + j) false = true) :
    (gs.set j ⟨.and, []⟩).foldl appendWire w = gs.foldl appendWire w := by
  induction gs generalizing w j with
  | nil => simp
  | cons g gs ih =>
    cases j with
    | zero =>
      change (gs.foldl appendWire (appendWire w g)).getD w.length false = true at h
      rw [readEarlierWire gs (appendWire w g) w.length (by simp [appendWire])] at h
      have hg : g.op.eval (g.inputs.map fun i => w.getD i false) = true := by
        simpa [appendWire] using h
      change gs.foldl appendWire (w ++ [true]) = gs.foldl appendWire (appendWire w g)
      simp only [appendWire, hg]
    | succ j =>
      apply ih (appendWire w g) j
      have index : (appendWire w g).length + j = w.length + (j + 1) := by
        simp only [appendWire, List.length_append, List.length_singleton]
        omega
      rw [index]
      exact h

theorem L_meta_197 :
    ∀ (n j : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (f : (Fin n → Bool) → Bool) (x : Fin n → Bool),
      (PEqualNP.MetaComplexity.circuitFun n
        { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩,
          output := C.output } x || !((C.wires (List.ofFn x)).getD (n + j) false)) ≠ f x →
      PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨
        ((C.wires (List.ofFn x)).getD (n + j) false = false ∧ f x = false) := by
  intro n j C f x herr
  cases hw : (C.wires (List.ofFn x)).getD (n + j) false with
  | false =>
    right
    refine ⟨rfl, ?_⟩
    cases hf : f x <;> simp_all
  | true =>
    left
    have same := forceTrue C.gates (List.ofFn x) j (by
      rw [List.length_ofFn]
      exact hw)
    have hout : MetaComplexity.circuitFun n ⟨C.gates.set j ⟨.and, []⟩, C.output⟩ x =
        MetaComplexity.circuitFun n C x :=
      congrArg (fun w : List Bool => w.getD C.output false) same
    simpa only [hw, Bool.not_true, Bool.or_false, hout] using herr

end PEqualNP.Outside
