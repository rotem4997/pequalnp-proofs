import PEqualNP.Search.Helpers.RUP.Trivial

/-!
# Helpers: the bound of the trivial resolution without a constant

Helper module, proofs only. Used by `L-lib-112`. The bound `4 * (card V + 1)` lines per learned
clause is at most `(2 * card V + 1) ^ 2` when there is a variable. With no variable every
clause is empty, a nonempty run forces the empty clause into the formula, and one line is
enough.
-/

namespace PEqualNP.Search.Helpers.RUP

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type}

/-- Over no variables, a nonempty run needs the empty clause in the formula. -/
theorem empty_mem_of_run [IsEmpty V] {F : Set (Clause V)} {ρ : List (Clause V)}
    (h : IsRUPRun F ρ) (hne : ρ ≠ []) : (∅ : Clause V) ∈ F := by
  induction h with
  | nil => exact absurd rfl hne
  | @learn ρ C _ hC ih =>
    obtain ⟨D, hD, _⟩ := hC
    rcases hD with hD | hD
    · rwa [Finset.eq_empty_of_isEmpty D] at hD
    · exact ih (List.ne_nil_of_mem hD)

/-- A run that learns the empty clause yields a resolution refutation of at most
`(number of learned clauses) * (2 * card V + 1) ^ 2` lines. -/
theorem refutation_of_run_quad [Fintype V] [DecidableEq V] {F : Set (Clause V)}
    {ρ : List (Clause V)} (h : IsRUPRun F ρ) (he : (∅ : Clause V) ∈ ρ) :
    ∃ π, IsRefutation F π ∧ π.length ≤ ρ.length * (2 * Fintype.card V + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp h0
    have hF := empty_mem_of_run h (List.ne_nil_of_mem he)
    refine ⟨[∅], ⟨IsDerivation.ax IsDerivation.nil hF, List.mem_cons_self⟩, ?_⟩
    have : 0 < ρ.length := List.length_pos_of_mem he
    simp
    omega
  · obtain ⟨π, hπ, hlen⟩ := refutation_of_run h he
    refine ⟨π, hπ, hlen.trans ?_⟩
    have : 4 * (Fintype.card V + 1) ≤ (2 * Fintype.card V + 1) ^ 2 := by nlinarith
    calc 4 * (ρ.length * (Fintype.card V + 1))
        = ρ.length * (4 * (Fintype.card V + 1)) := by ring
      _ ≤ ρ.length * (2 * Fintype.card V + 1) ^ 2 := Nat.mul_le_mul_left _ this

end PEqualNP.Search.Helpers.RUP
