import PEqualNP.MetaComplexity.Helpers.Chain016
import PEqualNP.MetaComplexity.Helpers.McspReduce
import PEqualNP.MetaComplexity.L023
import PEqualNP.Library.L009

/-- Murray and Williams: if MCSP is NP-hard under deterministic polynomial-time many-one
reductions, some language decided in time `2 ^ (n ^ k) + k` is outside NP intersect P/poly.
MCSP reduces to partial MCSP, so this follows from the partial version. -/
theorem PEqualNP.MetaComplexity.L009 :
    PEqualNP.Library.NPHard PEqualNP.MetaComplexity.MCSP → ∃ L : Language Bool, (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧ ¬ (L ∈ PEqualNP.Library.NP ∧ L ∈ PEqualNP.CircuitLowerBounds.PPoly) :=
  fun h => PEqualNP.MetaComplexity.Helpers.chain016 PEqualNP.MetaComplexity.L023
    (fun L' hL' => PEqualNP.Library.L009 _ _ _ (h L' hL')
      PEqualNP.MetaComplexity.Helpers.mcsp_reduces)
