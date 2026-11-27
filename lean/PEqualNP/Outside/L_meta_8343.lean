import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8343_aux

open PEqualNP.CircuitLowerBounds

theorem hget (acc : List ℕ) (k i : ℕ) :
    (acc.map (fun x => x.testBit k)).getD i false = (acc.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases acc[i]? <;> simp

theorem main (k : ℕ) (gs : List Gate) :
    ∀ (acc : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    List.map (fun (x : ℕ) => x.testBit k)
      (List.foldl (fun (x6 : List ℕ) (x7 : Gate) =>
                   have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
                   have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
                   x6 ++ [if x7.op.eval [Bool.false, Bool.true] = Bool.true then x8 ||| x9 else x8 &&& x9]) acc gs)
    = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.map (fun (x : ℕ) => x.testBit k) acc) gs := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g t ih =>
    intro acc h
    have hg := h g (by simp)
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hl⟩ := hg
    match inputs, hl with
    | [a, b], _ =>
      rcases hop with hop | hop <;> simp only at hop <;> subst hop <;>
        simp [GateOp.eval, Nat.testBit_or, Nat.testBit_and] <;>
        cases acc[a]? <;> cases acc[b]? <;> simp

end PEqualNP.Outside.L_meta_8343_aux

theorem PEqualNP.Outside.L_meta_8343 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : ℕ),   (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x5.inputs.length = (2 : ℕ)) →     ((List.foldl                 (fun (x6 : List ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) =>                   have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                   have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                   x6 ++ [if x7.op.eval [Bool.false, Bool.true] = Bool.true then x8 ||| x9 else x8 &&& x9])                 x2 x1.gates).getD             x3 (0 : ℕ)).testBit         x4 =       (x1.wires (List.map (fun (x6 : ℕ) => x6.testBit x4) x2)).getD x3 Bool.false := by
  intro x1 x2 x3 x4 h
  rw [← PEqualNP.Outside.L_meta_8343_aux.hget]
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  exact congrArg (fun l => l.getD x3 false) (PEqualNP.Outside.L_meta_8343_aux.main x4 x1.gates x2 h)
