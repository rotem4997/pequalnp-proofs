import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
Helpers for L-clb-004: every Boolean function on `n` inputs has a fan-in two circuit with at
most `(n + 2) * 2 ^ n` gates. The circuit is the Shannon expansion of
`PEqualNP.MetaComplexity.Helpers.shannon`, which has at most `5 * 2 ^ n - 4` gates; that count
is at most `(n + 2) * 2 ^ n` at every `n` (with equality at `n = 1` and `n = 2`).
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The Shannon count `5 * 2 ^ n - 4`, written without subtraction, is at most
`(n + 2) * 2 ^ n`. -/
theorem shannon_count_le (n s : ℕ) (h : s + 4 ≤ 5 * 2 ^ n) : s ≤ (n + 2) * 2 ^ n := by
  have small : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n := by grind
  rcases small with rfl | rfl | rfl | h3
  · grind
  · grind
  · grind
  · have h5 : 5 * 2 ^ n ≤ (n + 2) * 2 ^ n := by simp [*]
    grind

/-- Every Boolean function on `n` inputs has a circuit with at most `(n + 2) * 2 ^ n` gates. -/
theorem hasCircuitSize_all (n : ℕ) (f : (Fin n → Bool) → Bool) :
    HasCircuitSize n f ((n + 2) * 2 ^ n) := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := PEqualNP.MetaComplexity.Helpers.shannon n f n le_rfl
  refine ⟨⟨gs, out⟩, ok, ?_, ?_⟩
  · have hs : gs.length ≤ (n + 2) * 2 ^ n := shannon_count_le n gs.length len
    exact hs
  · intro x
    have h := ev (List.ofFn x) (by simp)
    have hx : (fun i : Fin n => (List.ofFn x).getD (i : ℕ) false) = x := by simp
    rw [hx] at h
    exact h

end PEqualNP.CircuitLowerBounds.Helpers
