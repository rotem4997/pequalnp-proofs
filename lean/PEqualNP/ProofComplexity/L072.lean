import PEqualNP.ProofComplexity.Helpers.LiftQuadAsm
import PEqualNP.ProofComplexity.Helpers.LiftQuadChain
import PEqualNP.ProofComplexity.Helpers.LiftQuadPath
import PEqualNP.ProofComplexity.Helpers.LiftQuadSubst
import PEqualNP.ProofComplexity.Helpers.LiftQuadGood

namespace PEqualNP.ProofComplexity

/-- L-pcx-072: quadratic size at constant degree over the two-element field. There are CNFs of
constant width, refuted by polynomial calculus in constant degree, all of whose dag-like Res(⊕)
refutations have at least `n ^ 2 / c` lines. -/
theorem L072 : ∃ w d c : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)), (∀ C ∈ F, C.card ≤ w) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) d ∧ ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinRefutation (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) π → n ^ 2 ≤ c * π.length :=
  LiftQuad.assembly_of LiftQuad.chain LiftQuad.step LiftQuad.path LiftQuad.subst LiftQuad.good_step

end PEqualNP.ProofComplexity
