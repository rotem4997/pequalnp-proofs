import PEqualNP.ProofComplexity.Helpers.DegreeBound

namespace PEqualNP.ProofComplexity

/-- L-pcx-027: functional pigeonhole has no polynomial calculus refutation over the
two-element field of degree `B` when there are at least `2 * B - 1` holes. -/
theorem L027 : ∀ (m N B : ℕ), 1 ≤ N → 2 * B ≤ N + 1 → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.funPHPSystem m N) B :=
  fun m N B hN hB => Helpers.funPHP_no_pc_refutation m N B hN hB

end PEqualNP.ProofComplexity
