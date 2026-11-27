import PEqualNP.ProofComplexity.Helpers.LinKOne

namespace PEqualNP.ProofComplexity

/-- L-pcx-052: Res(1, ⊕) with termwise weakening is Res(⊕): the same formulas have refutations
of the same lengths. -/
theorem L052 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (n : ℕ), (∃ π : List (PEqualNP.ProofComplexity.LinClause V), PEqualNP.ProofComplexity.IsLinRefutation F π ∧ π.length = n) ↔ (∃ π : List (PEqualNP.ProofComplexity.LinKLine V), PEqualNP.ProofComplexity.IsLinKRefutation 1 F π ∧ π.length = n) :=
  fun _ _ F n => Helpers.LinKOne.lin_iff_linK_one F n

end PEqualNP.ProofComplexity
