import PEqualNP.ProofComplexity.Helpers.LinKStrength

namespace PEqualNP.ProofComplexity

/-- L-pcx-056: for `1 ≤ k`, Res(k, ⊕) with termwise weakening contains Res(⊕): a Res(⊕)
refutation gives a Res(k, ⊕) refutation of the same length. -/
theorem L056 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause V)), 1 ≤ k → PEqualNP.ProofComplexity.IsLinRefutation F π → ∃ π' : List (PEqualNP.ProofComplexity.LinKLine V), PEqualNP.ProofComplexity.IsLinKRefutation k F π' ∧ π'.length = π.length :=
  fun _ _ F _ _ hk h => Helpers.LinKStrength.lin_to_linK F hk h

end PEqualNP.ProofComplexity
