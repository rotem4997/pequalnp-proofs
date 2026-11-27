import PEqualNP.ProofComplexity.L059

namespace PEqualNP.ProofComplexity

/-- L-pcx-069: the statement of L-pcx-059 under a corrected title (the formula is the functional
pigeonhole formula on some bipartite graph, not the complete one). -/
theorem L069 : ∃ B : ℕ, 2 ≤ B ∧ ∀ p : Polynomial ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G))), 1 ≤ k → B ^ (2 * k) ≤ n → PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length :=
  L059

end PEqualNP.ProofComplexity
