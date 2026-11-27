import PEqualNP.Defs
import PEqualNP.Gct.L061
import PEqualNP.Gct.Helpers.MainAssembly

/-! L-gct-064: over `ℂ`, every determinantal expression of `perm_m` (`m ≥ 3`) has size `n` with
`3n ≥ 2m² - 10m + 11`. Assembly: at the zero `J - m E_11`, L-gct-062 bounds every linear space through
it inside `{perm = 0}` by `4(m-1)` plus a space of `(m-1) x (m-1)` matrices killing both power sums of
the entries, which L-gct-061 bounds by `(m-1)²/3`; L-gct-035 turns that into a size bound. -/

theorem PEqualNP.Gct.L064 :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m :=
  PEqualNP.Gct.Helpers.bound_of_fermat PEqualNP.Gct.L061
