import PEqualNP.Gct.Helpers.GrenetMatrix

/-- Grenet (2011): for `m ≥ 1` the permanent of the `m × m` matrix of variables, over any
commutative ring, is the determinant of a matrix of size `2 ^ m - 1` with affine entries. The
matrix is a minor of `1 - N` for `N` the weighted adjacency matrix of the graph of subsets of
`Fin m`; the path sums solve a triangular system and Cramer's rule reads off the permanent. -/
theorem PEqualNP.Gct.L007 : ∀ (R : Type) [CommRing R] (m : ℕ), 1 ≤ m → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly R m) (2 ^ m - 1) :=
  fun R _ m hm => PEqualNP.Gct.Helpers.Grenet.hasDetExpression_permPoly R m hm
