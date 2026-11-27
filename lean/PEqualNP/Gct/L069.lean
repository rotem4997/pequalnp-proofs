import PEqualNP.Defs
import PEqualNP.Gct.Helpers.BorderSubspace

/-! L-gct-069, border subspace reduction: L-gct-035 for border determinantal expressions. If
`y` is a zero of `perm_m` such that every linear subspace `L` with `perm_m` vanishing on
`y + L` has dimension at most `k`, then every border determinantal expression of `perm_m` has
size at least `m ^ 2 - k`. Proof (in `Helpers/BorderSubspace.lean`): zeros of the approximants
tend to `y` by root persistence on a line, the subspaces of L-gct-035 at those zeros carry
orthonormal tuples of size `m ^ 2 - n`, and a convergent subsequence of tuples spans a subspace
on which `perm_m (y + ·)` vanishes. -/

theorem PEqualNP.Gct.L069 : ∀ (m n k : ℕ) (y : Fin m × Fin m → ℂ), MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 → (∀ L : Submodule ℂ (Fin m × Fin m → ℂ), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → Module.finrank ℂ L ≤ k) → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ k + n := by
  intro m n k y hy hL hB
  exact PEqualNP.Gct.Helpers.BorderSubspace.border_subspace m n k y hy hL hB
