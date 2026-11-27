import Mathlib
import PEqualNP.ProofComplexity.Helpers.LinKWitness

namespace PEqualNP.ProofComplexity

/-- L-pcx-055: non-vacuity of L-pcx-054. The functional pigeonhole formula on any graph with
more pigeons than holes has a Res(k, ⊕) refutation, for every `k ≥ 1`. -/
theorem L055 : ∀ (k m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N), 1 ≤ k → N < m → ∃ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G) π :=
  fun _ _ _ G hk h =>
    Helpers.LinKWitness.refutation_of_unsat hk _ (Helpers.LinKWitness.funGraphPHP_unsat G h)

end PEqualNP.ProofComplexity
