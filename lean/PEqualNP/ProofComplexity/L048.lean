import PEqualNP.ProofComplexity.Helpers.ThreeCnfFamily
import PEqualNP.ProofComplexity.L046

namespace PEqualNP.ProofComplexity

/-- L-pcx-048: some unsatisfiable 3-CNFs have no polynomially bounded dag-like Res(⊕)
refutations. -/
theorem L048 : ∀ p : Polynomial ℕ, ∃ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), (∀ C ∈ F, C.card ≤ 3) ∧ ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → p.eval n < π.length :=
  ThreeCnfFamily.three_cnf_hard L046

end PEqualNP.ProofComplexity
