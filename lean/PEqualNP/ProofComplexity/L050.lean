import Mathlib
import PEqualNP.ProofComplexity.L013
import PEqualNP.ProofComplexity.L030

/-- A Res(+) refutation of the pigeonhole formula exists at every n, with an explicit length
bound: the resolution refutation of L-pcx-030 carried line by line by L-pcx-013. -/
theorem PEqualNP.ProofComplexity.L050 : ∀ n : ℕ, ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin (n + 1) × Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP (n + 1) n) π ∧ π.length ≤ 2 ^ ((n + 1) * n + 1) - 1 := by
  intro n
  obtain ⟨π, hπ, hlen⟩ := PEqualNP.ProofComplexity.L030 n
  obtain ⟨π', h', hl⟩ := PEqualNP.ProofComplexity.L013 (Fin (n + 1) × Fin n) (PEqualNP.ProofComplexity.PHP (n + 1) n) π hπ
  exact ⟨π', h', hl ▸ hlen⟩
