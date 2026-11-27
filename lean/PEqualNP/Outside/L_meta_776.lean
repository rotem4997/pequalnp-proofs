import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_776

open PEqualNP.CircuitLowerBounds

-- The circuit of the statement.
def circ : Circuit :=
  { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [4, 7]⟩,
      ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩], output := 11 }

-- The value of the circuit on five given bits.
theorem eval_bits (a b c d e : Bool) :
    circ.eval [a, b, c, d, e] = ((a && b) || (a && e) || (b && c) || (c && d) || (d && e)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl

theorem ofFn5 (x : Fin 5 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
  simp [List.ofFn_succ]

theorem edge_iff (x : Fin 5 → Bool) :
    (∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true) ↔
      ((x 0 && x 1) || (x 0 && x 4) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, hm, hu, hv⟩
    fin_cases u <;> fin_cases v <;> simp at hm <;> simp_all
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, 1, by simp, h.1, h.2⟩
    · exact ⟨0, 4, by simp, h.1, h.2⟩
    · exact ⟨1, 2, by simp, h.1, h.2⟩
    · exact ⟨2, 3, by simp, h.1, h.2⟩
    · exact ⟨3, 4, by simp, h.1, h.2⟩

end PEqualNP.Outside.L_meta_776

theorem PEqualNP.Outside.L_meta_776 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩], output := 11 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [PEqualNP.Outside.L_meta_776.edge_iff, PEqualNP.Outside.L_meta_776.ofFn5]
    have h := PEqualNP.Outside.L_meta_776.eval_bits (x 0) (x 1) (x 2) (x 3) (x 4)
    rw [← h]
    rfl
