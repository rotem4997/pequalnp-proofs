import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_120 : ∀ (n : ℕ) (c : ℂ) (w : Fin n → ℂ), (∀ s : ℂ, MvPolynomial.eval (fun p : Fin n × Fin n => 1 + s * c * w p.2) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → c = 0 ∨ w = 0 := by
  intro n c w h
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hc, hw⟩ := hne
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hcw : c * w j ≠ 0 := mul_ne_zero hc hj
  have hprod : (∏ i : Fin n, (1 + -(c * w j)⁻¹ * c * w i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [show -(c * w j)⁻¹ * c * w j = -((c * w j)⁻¹ * (c * w j)) by ring, inv_mul_cancel₀ hcw]
    ring
  have key := h (-(c * w j)⁻¹)
  rw [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum] at key
  simp only [map_prod, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X] at key
  simp only [hprod, Finset.sum_const_zero] at key
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)) key.symm