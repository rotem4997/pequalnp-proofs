import PEqualNP.Defs
import PEqualNP.Gct.Helpers.MRPlusOne

/-! Helper module, proofs only. Helpers for L-gct-050 (cone reduction): if the permanent vanishes
on `y + L` for a linear space `L`, then it vanishes on `u • y + L` for every scalar `u`, by
homogeneity for `u ≠ 0` and by continuity at `u = 0`. -/

namespace PEqualNP.Gct.Helpers.ConeRed

open MvPolynomial

theorem eval_smul_add_eq_zero (m : ℕ) (y : Fin m × Fin m → ℂ)
    (L : Submodule ℂ (Fin m × Fin m → ℂ))
    (h : ∀ t ∈ L, eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0)
    (l : Fin m × Fin m → ℂ) (hl : l ∈ L) (u : ℂ) :
    eval (u • y + l) (PEqualNP.Gct.permPoly ℂ m) = 0 := by
  have hne : ∀ v : ℂ, v ≠ 0 → eval (v • y + l) (PEqualNP.Gct.permPoly ℂ m) = 0 := by
    intro v hv
    have e : v • y + l = v • (y + v⁻¹ • l) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hv, one_smul]
    rw [e, (PEqualNP.Gct.Helpers.isHomogeneous_permPoly m).eval_smul,
      h _ (L.smul_mem _ hl), mul_zero]
  have hc : Continuous fun v : ℂ => eval (v • y + l) (PEqualNP.Gct.permPoly ℂ m) :=
    (MvPolynomial.continuous_eval (PEqualNP.Gct.permPoly ℂ m)).comp (by fun_prop)
  have hd : Dense ({0}ᶜ : Set ℂ) := dense_compl_singleton 0
  have := Continuous.ext_on hd hc (continuous_const (y := (0 : ℂ))) (fun v hv => hne v hv)
  exact congrFun this u

end PEqualNP.Gct.Helpers.ConeRed
