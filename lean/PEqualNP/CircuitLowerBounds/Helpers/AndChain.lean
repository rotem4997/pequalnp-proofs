import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-clb-003: evaluating a circuit gate by gate, and the chain of fan-in two AND
gates that computes the conjunction of all inputs.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- Evaluating one more gate appends its value to the wires. -/
theorem wires_append_gate (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) o).wires x =
      (Circuit.mk gs o').wires x ++
        [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o').wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

/-- The AND chain on `n` inputs up to stage `j`: wire `n` is the constant `true`, and wire
`n + j + 1` is the AND of wire `n + j` and input `j`. -/
def andChain (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, []⟩]
  | j + 1 => andChain n j ++ [⟨GateOp.and, [n + j, j]⟩]

theorem andChain_length (n j : ℕ) : (andChain n j).length = j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [andChain, ih]

theorem andChain_gates (n j : ℕ) :
    ∀ g ∈ andChain n j, g.op = GateOp.and ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => intro g hg; simp [andChain] at hg; subst hg; simp
  | succ j ih =>
    intro g hg
    simp only [andChain, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · subst hg; simp

theorem andChain_wires (x : List Bool) (j : ℕ) (hj : j ≤ x.length) (o : ℕ) :
    (Circuit.mk (andChain x.length j) o).wires x =
      x ++ (List.range (j + 1)).map (fun i => (x.take i).all id) := by
  induction j with
  | zero => simp [Circuit.wires, andChain, GateOp.eval]
  | succ j ih =>
    have hj' : j < x.length := hj
    rw [andChain, wires_append_gate _ _ o o, ih (le_of_lt hj'), List.range_succ (n := j + 1),
      List.map_append, ← List.append_assoc]
    congr 1
    have h1 : (x ++ (List.range (j + 1)).map (fun i => (x.take i).all id)).getD (x.length + j)
        false = (x.take j).all id := by
      rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
      simp
    have h2 : (x ++ (List.range (j + 1)).map (fun i => (x.take i).all id)).getD j false
        = x[j] := by
      rw [List.getD_append _ _ _ _ hj']
      simp [List.getD_eq_getElem?_getD, hj']
    simp only [List.map_cons, List.map_nil, h1, h2, GateOp.eval, List.all_cons, List.all_nil,
      Bool.and_true, id]
    rw [List.take_succ_eq_append_getElem hj', List.all_append]
    simp

/-- The AND chain computes the conjunction of all inputs on its last wire. -/
theorem andChain_eval (x : List Bool) :
    (Circuit.mk (andChain x.length x.length) (x.length + x.length)).eval x = x.all id := by
  rw [Circuit.eval, andChain_wires x x.length le_rfl,
    List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
  simp

end PEqualNP.CircuitLowerBounds.Helpers
