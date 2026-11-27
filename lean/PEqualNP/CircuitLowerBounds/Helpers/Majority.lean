import PEqualNP.Defs
import Mathlib.Tactic

/-!
# One MAJORITY gate decides MAJORITY

Helper module (proofs only, no statement may use it). The circuit with the single gate
MAJORITY reading wires `0` to `n - 1` has size 1 and depth 1 and decides, at length `n`,
whether at least half of the input symbols are true.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

theorem map_getD_range' (x : List Bool) :
    (List.range x.length).map (fun i => x[i]?.getD false) = x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [h1]

theorem foldr_max_replicate (n : ℕ) : List.foldr max 0 (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem maj_in_TC0 : ({x : List Bool | x.length ≤ 2 * x.count true} : Language Bool) ∈ TC0 := by
  refine ⟨Polynomial.X + 1, 1, fun n => ⟨⟨[⟨GateOp.maj, List.range n⟩], n⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨by simp, by simp⟩
  · simp [Circuit.size]
  · simp [Circuit.depth, Circuit.depths, foldr_max_replicate]
  · intro x hx
    subst hx
    have : (⟨[⟨GateOp.maj, List.range x.length⟩], x.length⟩ : Circuit).eval x
        = decide (x.length ≤ 2 * x.count true) := by
      simp [Circuit.eval, Circuit.wires, map_getD_range', GateOp.eval]
    rw [this]
    simp
    rfl

end PEqualNP.CircuitLowerBounds.Helpers
