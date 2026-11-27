import PEqualNP.MetaComplexity.Helpers.Support

/-!
# The edge function of the 4-cycle

It is `(x0 OR x2) AND (x1 OR x3)`: three gates. It depends on all four inputs, so three gates
are needed.
-/

namespace PEqualNP.MetaComplexity.Helpers.ExactCycle4

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The edge function of the 4-cycle `0 1 2 3`. -/
def cyc4 (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 0)

/-- The three-gate circuit. -/
def up : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩], 6⟩

theorem fanInTwo_up : FanInTwo up := by
  intro g hg
  simp only [up, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

theorem ofFn4 (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

theorem eval_up (x : Fin 4 → Bool) : up.eval (List.ofFn x) = cyc4 x := by
  rw [ofFn4]
  unfold cyc4
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  revert a b c d
  decide

theorem upper (s : ℕ) (hs : 3 ≤ s) : HasCircuitSize 4 cyc4 s :=
  ⟨up, fanInTwo_up, by simp [up, Circuit.size]; omega, eval_up⟩

theorem lower (s : ℕ) (h : HasCircuitSize 4 cyc4 s) : 3 ≤ s := by
  have := dep_lower 4 cyc4 (fun i => by
    fin_cases i
    · exact ⟨![false, true, false, false], by decide⟩
    · exact ⟨![true, false, false, false], by decide⟩
    · exact ⟨![false, true, false, false], by decide⟩
    · exact ⟨![true, false, false, false], by decide⟩) s h
  omega

theorem size_iff (s : ℕ) : HasCircuitSize 4 cyc4 s ↔ 3 ≤ s := ⟨lower s, upper s⟩

end PEqualNP.MetaComplexity.Helpers.ExactCycle4
