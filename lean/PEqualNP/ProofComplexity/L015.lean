import PEqualNP.ProofComplexity.L017

namespace PEqualNP.ProofComplexity

/-- L-pcx-015: for every `k` some `n` has every Res(⊕) refutation of `PHP (n + 1) n` longer
than `n ^ k`. An instance of L-pcx-017 at the polynomial `X ^ k`. (The statement is weak: it
holds at `n = 1` for a trivial reason, which is why L-pcx-017 replaced it.) -/
theorem L015 : ∀ k : ℕ, ∃ n : ℕ, ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin (n + 1) × Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π → n ^ k < π.length := by
  intro k
  obtain ⟨n, hn⟩ := L017 (Polynomial.X ^ k)
  exact ⟨n, fun π hπ => by simpa using hn π hπ⟩

end PEqualNP.ProofComplexity
