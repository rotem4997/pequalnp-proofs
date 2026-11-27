import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7350_aux

open PEqualNP.CircuitLowerBounds

theorem getD_tb (l : List (ℕ × ℕ)) (k i : ℕ) :
    (List.map (fun (p : ℕ × ℕ) => p.1.testBit k) l).getD i false
      = (l.getD i ((0 : ℕ), (0 : ℕ))).1.testBit k := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ n => simpa using ih n

theorem main (k : ℕ) (gs : List Gate) :
    ∀ (acc : List (ℕ × ℕ)),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    List.map (fun (p : ℕ × ℕ) => p.1.testBit k)
      (List.foldl (fun (x1 : List (ℕ × ℕ)) (x2 : Gate) =>
        x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then
          (x1.getD (x2.inputs.getD 0 0) ((0 : ℕ), (0 : ℕ))).1 ||| (x1.getD (x2.inputs.getD 1 0) ((0 : ℕ), (0 : ℕ))).1
          else (x1.getD (x2.inputs.getD 0 0) ((0 : ℕ), (0 : ℕ))).1 &&& (x1.getD (x2.inputs.getD 1 0) ((0 : ℕ), (0 : ℕ))).1,
          (x1.getD (x2.inputs.getD 0 0) ((0 : ℕ), (0 : ℕ))).2 + (x1.getD (x2.inputs.getD 1 0) ((0 : ℕ), (0 : ℕ))).2)]) acc gs)
    = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.map (fun (p : ℕ × ℕ) => p.1.testBit k) acc) gs := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g t ih =>
    intro acc h
    have hg := h g (by simp)
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hlen⟩ := hg
    simp only at hop hlen
    match inputs, hlen with
    | [a, b], _ =>
      rcases hop with rfl | rfl
      · simp [GateOp.eval, Nat.testBit_and]
        cases acc[a]? <;> cases acc[b]? <;> simp
      · simp [GateOp.eval, Nat.testBit_or]
        cases acc[a]? <;> cases acc[b]? <;> simp

end PEqualNP.Outside.L_meta_7350_aux

theorem PEqualNP.Outside.L_meta_7350 : have x1 : List (ℕ × ℕ) → PEqualNP.CircuitLowerBounds.Gate → List (ℕ × ℕ) := fun (x1 : List (ℕ × ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) =>   have x3 : ℕ × ℕ := x1.getD (x2.inputs.getD (0 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   have x4 : ℕ × ℕ := x1.getD (x2.inputs.getD (1 : ℕ) (0 : ℕ)) ((0 : ℕ), (0 : ℕ));   x1 ++ [(if x2.op.eval [Bool.false, Bool.true] = Bool.true then x3.1 ||| x4.1 else x3.1 &&& x4.1, x3.2 + x4.2)]; ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List (ℕ × ℕ)), (∀ x4 ∈ x2, (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x4.inputs.length = (2 : ℕ)) → ∀ (x5 x6 : ℕ), ((List.foldl x1 x3 x2).getD x6 ((0 : ℕ), (0 : ℕ))).1.testBit x5 = { gates := x2, output := x6 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.map (fun (x7 : ℕ × ℕ) => x7.1.testBit x5) x3) := by
  intro x1 x2 x3 h x5 x6
  have hm := PEqualNP.Outside.L_meta_7350_aux.main x5 x2 x3 h
  rw [← PEqualNP.Outside.L_meta_7350_aux.getD_tb]
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact congrArg (fun l => l.getD x6 false) hm
