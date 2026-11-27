import PEqualNP.Defs
import PEqualNP.Gct.Helpers.OrderConditions

/-! L-gct-051, first and second order conditions for a linear space through a zero `y` inside
the permanent hypersurface. If the permanent vanishes on `y + L` for a linear subspace `L`, then
for every `t` in `L` the gradient of the permanent at `y` kills `t` and the Hessian quadratic
form of the permanent at `y` vanishes at `t`. Proof: the function `s ↦ perm (y + s • t)` is
identically zero, so its first and second derivatives at `0` vanish. -/

open MvPolynomial PEqualNP.Gct.Helpers.OrderCond

theorem PEqualNP.Gct.L051 : ∀ (m : ℕ) (y : Fin m × Fin m → ℂ) (L : Submodule ℂ (Fin m × Fin m → ℂ)), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → ∀ t ∈ L, (∑ a, MvPolynomial.eval y (MvPolynomial.pderiv a (PEqualNP.Gct.permPoly ℂ m)) * t a = 0) ∧ (∑ a, ∑ b, MvPolynomial.eval y (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ m))) * t a * t b = 0) := by
  intro m y L h t ht
  exact order_conditions_of_vanish_on_line _ y t (fun s => h _ (L.smul_mem s ht))
