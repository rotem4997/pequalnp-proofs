import PEqualNP.Defs

/-! Helper for L-gct-091 (LS(4) <= 5). The `4 x 4` permanent written out as its 24 terms, in the
convention of `Helpers/Extension/Gradient.lean`: `z (σ i, i)`, first coordinate the row. -/

namespace PEqualNP.Gct.LS4

open Finset

theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

/-- The permanent of a `4 x 4` matrix as a sum over permutations, written out. -/
theorem sum_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    ∑ σ : Equiv.Perm (Fin 4), ∏ i, z (σ i, i) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

/-- The same for `MvPolynomial.eval` of `permPoly`. -/
theorem eval_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ 4) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [← sum_perm_four]
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

end PEqualNP.Gct.LS4
