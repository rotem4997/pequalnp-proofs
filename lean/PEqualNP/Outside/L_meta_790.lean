import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_790

lemma key : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    (PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) [a0, a1, a2, a3, a4, a5] = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧
        ![a0, a1, a2, a3, a4, a5] u = true ∧ ![a0, a1, a2, a3, a4, a5] v = true) := by
  decide

lemma ofFnN (x : Fin 6 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl

lemma vecN (x : Fin 6 → Bool) : ![x 0, x 1, x 2, x 3, x 4, x 5] = x := by
  funext i
  fin_cases i <;> rfl

end PEqualNP.Outside.L_meta_790

open PEqualNP.Outside.L_meta_790 in
theorem PEqualNP.Outside.L_meta_790 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have h := key (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    rw [vecN x] at h
    rw [ofFnN x]
    exact h
