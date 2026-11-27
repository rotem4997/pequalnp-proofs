import PEqualNP.ProofComplexity.Helpers.LinKGrow

namespace PEqualNP.ProofComplexity

/-- L-pcx-059: one constant `B`; for every polynomial `p` and every large `n`, one graph `G` on
`n + 1` pigeons and `n` holes such that for every `k ≥ 1` with `B ^ (2 * k) ≤ n`, every
refutation of the functional pigeonhole formula on `G` in resolution over conjunctions of at
most `k` parity equations has more than `p` of the number of variables many lines. -/
theorem L059 : ∃ B : ℕ, 2 ≤ B ∧ ∀ p : Polynomial ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, ∀ (k : ℕ) (π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G))), 1 ≤ k → B ^ (2 * k) ≤ n → PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π → p.eval (Fintype.card (PEqualNP.Expanders.GEdge G)) < π.length :=
  LinKGrow.grow_k

end PEqualNP.ProofComplexity
