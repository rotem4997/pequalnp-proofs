import PEqualNP.ProofComplexity.Helpers.LinKStrength

namespace PEqualNP.ProofComplexity

/-- L-pcx-057: Res(k, ⊕) with termwise weakening contains the k-DNF resolution Res(k): a Res(k)
refutation gives a Res(k, ⊕) refutation of the same length. -/
theorem L057 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (k : ℕ) (π : List (PEqualNP.ProofComplexity.KLine V)), PEqualNP.ProofComplexity.IsResKRefutation k F π → ∃ π' : List (PEqualNP.ProofComplexity.LinKLine V), PEqualNP.ProofComplexity.IsLinKRefutation k F π' ∧ π'.length = π.length :=
  fun _ _ F _ _ h => Helpers.LinKStrength.resK_refutation F h

end PEqualNP.ProofComplexity
