import PEqualNP.ProofComplexity.Helpers.Resolution

namespace PEqualNP.ProofComplexity

/-- L-pcx-001: the resolution rule is sound. -/
theorem L001 : ∀ (V : Type) [DecidableEq V] (a : V → Bool) (C D R : PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsResolvent C D R → PEqualNP.ProofComplexity.ClauseSat a C → PEqualNP.ProofComplexity.ClauseSat a D → PEqualNP.ProofComplexity.ClauseSat a R :=
  fun _ _ a _ _ _ h hC hD => Helpers.resolvent_sound a h hC hD

end PEqualNP.ProofComplexity
