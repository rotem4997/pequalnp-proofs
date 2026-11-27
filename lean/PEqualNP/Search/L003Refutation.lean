import PEqualNP.Search.Helpers.L003Bridge
import PEqualNP.ProofComplexity.L048

/-- Candidate 3 premise refuted: unsatisfiable 3-CNFs do not have polynomial-size Res(lin)
refutations. The family of L-pcx-048 through the bridge L-pcx-018. -/
theorem PEqualNP.Search.L003Refutation : ¬ (∃ p : Polynomial ℕ, ∀ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) → ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) → ∃ π : List (PEqualNP.Search.LinClause n), PEqualNP.Search.IsResLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π ∧ π.length ≤ p.eval n) :=
  PEqualNP.Search.Helpers.family_refutes_L003 PEqualNP.ProofComplexity.L048
