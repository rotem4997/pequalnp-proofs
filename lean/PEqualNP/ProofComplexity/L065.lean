import PEqualNP.ProofComplexity.Helpers.LiftRankWidth
import PEqualNP.ProofComplexity.Helpers.LiftRankSmall

namespace PEqualNP.ProofComplexity

/-- L-pcx-065: low degree over the two-element field does not bound the rank of resolution over
parities. There are CNFs of constant width, refuted by polynomial calculus in constant degree,
all of whose Res(⊕) refutations have a line of rank linear in the number of variables. -/
theorem L065 : ∃ w d c : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)), (∀ C ∈ F, C.card ≤ w) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) d ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → ∃ C ∈ π, n ≤ c * PEqualNP.ProofComplexity.linRank C :=
  LiftRank.assembly_of ⟨LiftRank.formula_width, LiftRank.formula_sem, LiftRank.formula_pc⟩
    LiftRank.width LiftRank.rename_pc LiftRank.rename_rank LiftRank.dependency

end PEqualNP.ProofComplexity
