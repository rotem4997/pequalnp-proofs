import PEqualNP.ProofComplexity.L005
import PEqualNP.ProofComplexity.L013
import PEqualNP.ProofComplexity.L021

open PEqualNP.ProofComplexity in
/-- Bit pigeonhole has a Res(+) refutation whenever it is unsatisfiable. -/
theorem PEqualNP.ProofComplexity.L039 : ∀ m l : ℕ, 2 ^ l < m → ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin l)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP m l) π := by
  intro m l h
  obtain ⟨π, hπ⟩ := PEqualNP.ProofComplexity.L005 (Fin m × Fin l) (BPHP m l) (PEqualNP.ProofComplexity.L021 m l h)
  obtain ⟨π', h', -⟩ := PEqualNP.ProofComplexity.L013 (Fin m × Fin l) (BPHP m l) π hπ
  exact ⟨π', h'⟩
