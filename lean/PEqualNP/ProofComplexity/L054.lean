import PEqualNP.ProofComplexity.Helpers.LinKWire
import PEqualNP.ProofComplexity.Helpers.LinKSim

namespace PEqualNP.ProofComplexity

/-- L-pcx-054: for every `k ≥ 1`, resolution over conjunctions of at most `k` parity equations
(termwise weakening) is not polynomially bounded on functional pigeonhole formulas. -/
theorem L054 : ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), N < m ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length :=
  LinKWire.fun_not_poly LinKSim.simulation_refutation

end PEqualNP.ProofComplexity
