import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.MomentReduction

namespace PEqualNP.ProofComplexity

/-- L-pcx-028: the degree bound for functional pigeonhole follows from moment extension. -/
theorem L028 : ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, PEqualNP.ProofComplexity.MomentExt m N k) → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.funPHPSystem m N) B :=
  fun m N B hN h => Helpers.no_pc_refutation_of_momentExt m N B hN h

end PEqualNP.ProofComplexity
