import PEqualNP.ProofComplexity.Helpers.FunGraphPHPReduction

namespace PEqualNP.ProofComplexity

/-- L-pcx-049: on a bipartite graph of left degree at most `d` where every set of at most `s`
pigeons has twice its size in unique neighbouring holes, the functional pigeonhole CNF has no
polynomial calculus refutation over F2 of degree `D` when `1 ≤ s` and `d * D ≤ s`. -/
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end PEqualNP.ProofComplexity
