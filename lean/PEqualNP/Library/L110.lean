import PEqualNP.Search.Helpers.PCSim.Incomplete

/-- Bounded-width Res(⊕) is incomplete on 3-CNFs: for every `k` some unsatisfiable 3-CNF has
no Res(⊕) refutation all of whose lines have at most `k` equations. -/
theorem PEqualNP.Library.L110 : ∀ k : ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) ∧ ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → ∃ L ∈ π, k < L.card :=
  PEqualNP.Search.Helpers.PCSim.incomplete
