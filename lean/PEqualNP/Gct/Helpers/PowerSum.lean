import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-gct-029: the power sum `x_1 ^ r + ... + x_d ^ r` is homogeneous of degree `r`
and its partial derivatives vanish together only at the origin.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- The power sum of degree `r` in `d` variables over the complex numbers. -/
noncomputable def powerSum (d r : ℕ) : MvPolynomial (Fin d) ℂ :=
  ∑ i : Fin d, (X i : MvPolynomial (Fin d) ℂ) ^ r

theorem powerSum_isHomogeneous (d r : ℕ) : (powerSum d r).IsHomogeneous r := by
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℂ i).pow r

theorem eval_pderiv_powerSum (d r : ℕ) (x : Fin d → ℂ) (i : Fin d) :
    eval x (pderiv i (powerSum d r)) = (r : ℂ) * x i ^ (r - 1) := by
  classical
  simp only [powerSum, map_sum, Derivation.leibniz_pow, pderiv_X, smul_eq_mul, nsmul_eq_mul,
    map_mul, map_pow, eval_X, map_natCast]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_apply]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem powerSum_smooth (d r : ℕ) (hr : 2 ≤ r) (x : Fin d → ℂ)
    (h : ∀ i, eval x (pderiv i (powerSum d r)) = 0) : x = 0 := by
  funext i
  have hi := h i
  rw [eval_pderiv_powerSum] at hi
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have := (mul_eq_zero.mp hi).resolve_left hr0
  exact pow_eq_zero_iff (by omega) |>.mp this

end PEqualNP.Gct.Helpers
