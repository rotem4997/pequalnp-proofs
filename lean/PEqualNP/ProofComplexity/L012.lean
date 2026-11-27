import PEqualNP.ProofComplexity.Helpers.Lin

namespace PEqualNP.ProofComplexity

/-- L-pcx-012: Res(⊕) is sound. -/
theorem L012 : ∀ (V : Type) [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)), PEqualNP.ProofComplexity.IsLinRefutation F π → ¬ PEqualNP.ProofComplexity.Satisfiable F :=
  fun _ _ _ _ h => Helpers.lin_refutation_unsat h

end PEqualNP.ProofComplexity
