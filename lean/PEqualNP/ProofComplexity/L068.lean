import PEqualNP.ProofComplexity.L054

namespace PEqualNP.ProofComplexity

/-- L-pcx-068: the statement of L-pcx-054 under a corrected title (the formula is the functional
pigeonhole formula on some bipartite graph, not the complete one). -/
theorem L068 : ∀ k : ℕ, 1 ≤ k → ∀ p : Polynomial ℕ, ∃ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), N < m ∧ ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length :=
  L054

end PEqualNP.ProofComplexity
