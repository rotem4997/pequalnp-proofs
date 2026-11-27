import PEqualNP.ProofComplexity.Helpers.SizeWidth

namespace PEqualNP.ProofComplexity

/-- L-pcx-008: Ben-Sasson and Wigderson, short resolution refutations give narrow ones. A
refutation of `S` lines of a formula with clauses of at most `k` literals over `n` variables
gives a refutation of width at most `k + c √(n ln S)`, for an absolute constant `c`. -/
theorem L008 : ∃ c : ℝ, ∀ (V : Type) [DecidableEq V] [Fintype V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.Clause V)) (k : ℕ), PEqualNP.ProofComplexity.IsRefutation F π → (∀ C ∈ F, C.card ≤ k) → ∃ π' : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F π' ∧ ∀ C ∈ π', (C.card : ℝ) ≤ (k : ℝ) + c * Real.sqrt ((Fintype.card V : ℝ) * Real.log (π.length : ℝ)) :=
  Helpers.SizeWidth.bsw

end PEqualNP.ProofComplexity
