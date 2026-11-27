import PEqualNP.MetaComplexity.Helpers.Chain016
import PEqualNP.MetaComplexity.L023

/-- If partial MCSP is NP-hard under deterministic polynomial-time many-one reductions, then
some language decided in time `2 ^ (n ^ k) + k` is outside NP intersect P/poly. The argument
of Murray and Williams for MCSP, carried over to partial truth tables. -/
theorem PEqualNP.MetaComplexity.L016 :
    PEqualNP.Library.NPHard PEqualNP.MetaComplexity.PartialMCSP → ∃ L : Language Bool, (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧ ¬ (L ∈ PEqualNP.Library.NP ∧ L ∈ PEqualNP.CircuitLowerBounds.PPoly) :=
  fun h => PEqualNP.MetaComplexity.Helpers.chain016 PEqualNP.MetaComplexity.L023 h
