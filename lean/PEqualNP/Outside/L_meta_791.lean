import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_791

open PEqualNP.CircuitLowerBounds

-- The circuit of the statement.
def circ : Circuit :=
  { gates := [⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [2, 0]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [11, 13]⟩], output := 14 }

-- The value of the circuit on the given bits.
theorem eval_bits (a b c d e f g : Bool) :
    circ.eval [a, b, c, d, e, f, g] = ((a && b) || (b && c) || (c && d) || (d && e) || (e && f) || (f && g)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem ofFn_list (x : Fin 7 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  simp [List.ofFn_succ]

theorem edge_iff (x : Fin 7 → Bool) :
    (∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] : List (ℕ × ℕ)) ∧
        x u = true ∧ x v = true) ↔
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, hm, hu, hv⟩
    fin_cases u <;> fin_cases v <;> simp at hm <;> simp_all
  · rintro (((((h | h) | h) | h) | h) | h)
    · exact ⟨0, 1, by simp, h.1, h.2⟩
    · exact ⟨1, 2, by simp, h.1, h.2⟩
    · exact ⟨2, 3, by simp, h.1, h.2⟩
    · exact ⟨3, 4, by simp, h.1, h.2⟩
    · exact ⟨4, 5, by simp, h.1, h.2⟩
    · exact ⟨5, 6, by simp, h.1, h.2⟩

end PEqualNP.Outside.L_meta_791

theorem PEqualNP.Outside.L_meta_791 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 7 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 7, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [PEqualNP.Outside.L_meta_791.edge_iff, PEqualNP.Outside.L_meta_791.ofFn_list]
    have h := PEqualNP.Outside.L_meta_791.eval_bits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
    rw [← h]
    rfl
