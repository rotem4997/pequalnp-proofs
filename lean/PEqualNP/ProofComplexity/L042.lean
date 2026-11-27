import PEqualNP.ProofComplexity.Helpers.DegSizeAssembly

namespace PEqualNP.ProofComplexity

/-- L-pcx-042: degree to size. A CNF of width `w` with no polynomial calculus refutation over
`ZMod 2` of degree `D` has only dag-like Res(⊕) refutations of at least
`exp (D ^ 2 / (1024 v))` lines. -/
theorem L042 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w D : ℕ), (∀ C ∈ F, C.card ≤ w) → 32 * w ≤ D → 32 ≤ D → PEqualNP.ProofComplexity.IsLinRefutation F π → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem F) D → Real.exp (((D : ℝ) ^ 2) / (1024 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ) :=
  DegSizeAssembly.degree_to_size

end PEqualNP.ProofComplexity
