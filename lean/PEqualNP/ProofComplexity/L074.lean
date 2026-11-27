import PEqualNP.ProofComplexity.Helpers.LiftClassKill
import PEqualNP.ProofComplexity.Helpers.LiftClassCount
import PEqualNP.ProofComplexity.Helpers.LiftClassJunta
import PEqualNP.ProofComplexity.Helpers.LiftClassSem
import PEqualNP.ProofComplexity.Helpers.LiftClassL2

namespace PEqualNP.ProofComplexity

/-- L-pcx-074: a class bound. A Res(⊕) refutation of an inner-product lift whose lines, as
written, have few cross-block incidences gives a resolution refutation of the base formula of
width at most `3 (w - 1 + I₀)`. -/
theorem L074 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (G : Set (PEqualNP.ProofComplexity.Clause (V × Fin 4))) (π : List (PEqualNP.ProofComplexity.LinClause (V × Fin 4))) (w I₀ : ℕ), 1 ≤ w → PEqualNP.ProofComplexity.IsIPLiftOf F G → PEqualNP.ProofComplexity.IsLinRefutation G π → (∀ L ∈ π, (PEqualNP.ProofComplexity.lineLocalBlocks L).card < w → PEqualNP.ProofComplexity.lineCrossInc L ≤ I₀) → (π.filter (fun L => w ≤ (PEqualNP.ProofComplexity.lineLocalBlocks L).card)).length * 4 ^ w < 5 ^ w → ∃ ρ : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F ρ ∧ ∀ C ∈ ρ, C.card ≤ 3 * (w - 1 + I₀) :=
  LiftClass.assembly LiftClass.stmtKill LiftClass.stmtCount LiftClass.stmtJunta LiftClass.stmtSem LiftClass.stmtL2

end PEqualNP.ProofComplexity
