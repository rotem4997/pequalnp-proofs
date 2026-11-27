import PEqualNP.ProofComplexity.Helpers.Retype

namespace PEqualNP.ProofComplexity

/-- L-pcx-047: re-typing. A Res(⊕) refutation of length `S` of the pigeonhole formula gives a
Res(⊕) refutation of length at most `2 S` of the pigeonhole formula on a bipartite graph, over
the edge variables only. -/
theorem L047 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin N))), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP m N) π → ∃ π' : List (PEqualNP.ProofComplexity.LinClause (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.Expanders.graphPHP G) π' ∧ π'.length ≤ 2 * π.length :=
  fun _ _ G π h => Helpers.rt_refutation G π h

end PEqualNP.ProofComplexity
