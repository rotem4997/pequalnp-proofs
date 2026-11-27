import PEqualNP.ProofComplexity.Helpers.Completeness

namespace PEqualNP.ProofComplexity

/-- L-pcx-006: every unsatisfiable clause set over `n` variables has a refutation of at most
`2 ^ (n + 1) - 1` lines. -/
theorem L006 : ∀ (V : Type) [DecidableEq V] [Fintype V] (F : Set (PEqualNP.ProofComplexity.Clause V)), ¬ PEqualNP.ProofComplexity.Satisfiable F → ∃ π : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F π ∧ π.length ≤ 2 ^ (Fintype.card V + 1) - 1 :=
  fun _ _ _ F h => Helpers.completeness F h

end PEqualNP.ProofComplexity
