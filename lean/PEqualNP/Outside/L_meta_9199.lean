import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9199_aux

open PEqualNP.CircuitLowerBounds

theorem pre : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), i < x.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false
      = x.getD i false := by
  intro gs
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    rw [List.foldl_cons, ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

theorem key : ∀ (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate), gs[j]? = some g →
    (∀ i ∈ g.inputs, i < x.length + j) →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD (x.length + j) false
      = g.op.eval (g.inputs.map fun i =>
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false) := by
  intro gs
  induction gs with
  | nil => intro x j g hg; simp at hg
  | cons h t ih =>
    intro x j g hg hin
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      rw [List.foldl_cons, Nat.add_zero, pre _ _ _ (by simp)]
      rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi' := hin i hi
      rw [pre _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg
      rw [List.foldl_cons]
      have hl : x.length + (j + 1) = (x ++ [h.op.eval (h.inputs.map fun i => x.getD i false)]).length + j := by
        simp; omega
      rw [hl]
      apply ih _ j g hg
      intro i hi
      have := hin i hi
      simp; omega

end PEqualNP.Outside.L_meta_9199_aux

theorem PEqualNP.Outside.L_meta_9199 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ) → Bool) (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (∀ x6 ∈ x4.inputs, x6 < (14 : ℕ) + x3) → PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 ((14 : ℕ) + x3) x2 = x4.op.eval (List.map (fun (x7 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 x2) x4.inputs) := by
  intro x1 x2 x3 x4 h hin
  have := PEqualNP.Outside.L_meta_9199_aux.key x1.gates (List.ofFn x2) x3 x4 h (by simpa using hin)
  simp only [List.length_ofFn] at this
  exact this
