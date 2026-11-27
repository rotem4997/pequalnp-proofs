import PEqualNP.ProofComplexity.Helpers.Restrict

namespace PEqualNP.ProofComplexity

/-- L-pcx-045: Res(⊕) is closed under restriction. A refutation of length `S` of a CNF gives a
refutation of length at most `2 S` of its restriction by any partial assignment. -/
theorem L045 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (ρ : V → Option Bool) (π : List (PEqualNP.ProofComplexity.LinClause V)), PEqualNP.ProofComplexity.IsLinRefutation F π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause V), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.restrictCNF F ρ) π' ∧ π'.length ≤ 2 * π.length :=
  fun _ _ F ρ π h => Helpers.rst_refutation F ρ π h

end PEqualNP.ProofComplexity
