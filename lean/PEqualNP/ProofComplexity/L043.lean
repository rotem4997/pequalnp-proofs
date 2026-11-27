import PEqualNP.ProofComplexity.Helpers.ExpanderDet
import PEqualNP.ProofComplexity.Helpers.ExpanderPerm
import PEqualNP.ProofComplexity.Helpers.ExpanderArith
import PEqualNP.ProofComplexity.Helpers.ExpanderAssembly

namespace PEqualNP.ProofComplexity

/-- L-pcx-043: bounded-degree bipartite boundary expanders with `n + 1` pigeons and `n` holes
exist for all large `n`, by counting over 8 random permutations. -/
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end PEqualNP.ProofComplexity
