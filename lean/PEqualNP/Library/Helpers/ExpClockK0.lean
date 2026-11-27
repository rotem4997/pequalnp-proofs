import PEqualNP.Library.Helpers.Erasure

/-!
# The exponential clock statement fails at `k = 0`

Helper module (proofs only, no statement may use it). At `k = 0` the claimed time bound
`c * 2 ^ (n ^ 0) + c = 3 * c` is a constant, but a machine must erase its input, and one step
pops a bounded number of symbols, so the running time grows linearly in the input length.
-/

open Turing

namespace PEqualNP.Library.Helpers

/-- Any function on binary strings with outputs of bounded length needs linear time. -/
theorem time_linear_of_bounded_output (f : List Bool → List Bool) (t : ℕ → ℕ) (B : ℕ)
    (hB : ∀ x, (f x).length ≤ B)
    (h : PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      f t) :
    ∃ d : ℕ, ∀ n : ℕ, n ≤ d * t n + B := by
  obtain ⟨c, hc⟩ := h
  let _ := c.tm.ΛFin
  let _ := c.tm.kDecidableEq
  refine ⟨Finset.univ.sup fun l => pops (c.tm.m l), fun n => ?_⟩
  have h := c.outputsFun (List.replicate n false)
  have key := iter_len c.tm.m c.tm.k₀ h.steps _ _ h.evals_in_steps
  have hle : h.steps ≤ t n := by
    have := h.steps_le_m.trans (hc _); simpa using this
  have hinit : ((initList c.tm (List.map c.inputAlphabet.invFun
      (List.replicate n false))).stk c.tm.k₀).length = n := by
    simp [initList]
  have hhalt : ((haltList c.tm (List.map c.outputAlphabet.invFun
      (f (List.replicate n false)))).stk c.tm.k₀).length ≤ B :=
    (halt_len _ _ _).trans (by simpa using hB (List.replicate n false))
  rw [hinit] at key
  have : (Finset.univ.sup fun l => pops (c.tm.m l)) * h.steps ≤
      (Finset.univ.sup fun l => pops (c.tm.m l)) * t n :=
    Nat.mul_le_mul_left _ hle
  rw [Nat.mul_comm] at this
  omega

/-- The statement of `L-lib-082` is false at `k = 0`. -/
theorem expClock_false_k0 :
    ¬ ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ 0)) true)
      (fun n : ℕ => c * 2 ^ (n ^ 0) + c) := by
  rintro ⟨c, h⟩
  obtain ⟨d, hd⟩ := time_linear_of_bounded_output _ _ 2 (fun x => by simp) h
  have := hd (d * (c * 2 + c) + 3)
  simp at this

/-- The negation of the full `L-lib-082` statement. -/
theorem L082_statement_false :
    ¬ ∀ k : ℕ, ∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ (x.length ^ k)) true)
      (fun n : ℕ => c * 2 ^ (n ^ k) + c) :=
  fun h => expClock_false_k0 (h 0)

end PEqualNP.Library.Helpers
