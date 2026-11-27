import PEqualNP.ProofComplexity.Helpers.GraphPHPReduction

namespace PEqualNP.ProofComplexity

/-- L-pcx-046: on a bipartite graph where every set of at most `s` pigeons has twice its size in
unique neighbouring holes, the plain pigeonhole CNF has no polynomial calculus refutation over
F2 of degree `D` when `2 (D + 1) ≤ s`. -/
theorem L046 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → 2 * (D + 1) ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.graphPHP G)) D :=
  fun _ _ G _ _ hG hs => Helpers.graphPHP_no_pc_refutation G hG (by omega) (by omega)

end PEqualNP.ProofComplexity
