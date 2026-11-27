import PEqualNP.Defs
import PEqualNP.Gct.Helpers.TaylorOnSpace

/-! L-gct-052, polarized Taylor coefficients on a linear space. If the permanent vanishes on the
affine space `y + L`, then for every `k` the `k`-th differential of the permanent at `y`, applied
to any `t_1, .., t_k` in `L`, is zero. Proof: the directional derivative along a direction of `L`
of a polynomial vanishing on `y + L` again vanishes on `y + L`; iterate and expand. -/

open MvPolynomial PEqualNP.Gct.Helpers.TaylorSp

theorem PEqualNP.Gct.L052 : ∀ (m k : ℕ) (y : Fin m × Fin m → ℂ) (L : Submodule ℂ (Fin m × Fin m → ℂ)), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → ∀ t : Fin k → (Fin m × Fin m → ℂ), (∀ j, t j ∈ L) → ∑ a : Fin k → Fin m × Fin m, MvPolynomial.eval y ((List.ofFn a).foldr (fun i q => MvPolynomial.pderiv i q) (PEqualNP.Gct.permPoly ℂ m)) * ∏ j, t j (a j) = 0 := by
  intro m k y L h t ht
  exact differential_vanish _ y L h k t ht
