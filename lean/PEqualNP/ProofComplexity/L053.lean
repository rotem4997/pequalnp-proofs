import PEqualNP.ProofComplexity.Helpers.WeakPhpBase

namespace PEqualNP.ProofComplexity

/-- L-pcx-053: the base bound for the pigeonhole formula with any number of pigeons. If a
bipartite graph on `m` pigeons and `N` holes is an `(s, 2)` boundary expander of left degree at
most `b`, and `2 (D + 1) ≤ s`, `32 ≤ D`, `2 b ≤ D`, then every Res(⊕) refutation `π` of
`PHP m N` has `exp (D ^ 2 / (256 b m)) ≤ 2 |π|`. -/
theorem L053 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s b D : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin N))), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G b → 2 * (D + 1) ≤ s → 32 ≤ D → 2 * b ≤ D → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP m N) π → Real.exp (((D : ℝ) ^ 2) / (256 * ((b : ℝ) * (m : ℝ)))) ≤ 2 * (π.length : ℝ) :=
  fun m N G s b D π hE hL hs hD hb hπ => WeakPhpBase.weak_php_base m N G s b D π hE hL hs hD hb hπ

end PEqualNP.ProofComplexity
