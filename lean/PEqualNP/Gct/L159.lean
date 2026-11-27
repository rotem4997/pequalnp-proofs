import PEqualNP.Gct.Helpers.RealLevel

/-- The off-row, off-column product sum of a `p × q` array over a commutative ring equals the
squared total sum, minus the squared row sums, minus the squared column sums, plus the squared
entries. -/
theorem PEqualNP.Gct.L159 : ∀ (R : Type) [CommRing R] (p q : ℕ) (t : Fin p × Fin q → R), (∑ i, ∑ i', ∑ j, ∑ j', if i = i' ∨ j = j' then 0 else t (i, j) * t (i', j')) = (∑ i, ∑ j, t (i, j)) ^ 2 - (∑ i, (∑ j, t (i, j)) ^ 2) - (∑ j, (∑ i, t (i, j)) ^ 2) + ∑ i, ∑ j, t (i, j) ^ 2 :=
  PEqualNP.Gct.Helpers.RealLevel.ident
