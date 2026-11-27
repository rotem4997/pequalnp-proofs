import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_112 : ∀ w : Fin 4 × Fin 4 → ℂ, MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = (w (0, 0) * w (1, 1) + w (0, 1) * w (1, 0)) * (w (2, 2) * w (3, 3) + w (2, 3) * w (3, 2)) + (w (0, 0) * w (1, 2) + w (0, 2) * w (1, 0)) * (w (2, 1) * w (3, 3) + w (2, 3) * w (3, 1)) + (w (0, 0) * w (1, 3) + w (0, 3) * w (1, 0)) * (w (2, 1) * w (3, 2) + w (2, 2) * w (3, 1)) + (w (0, 1) * w (1, 2) + w (0, 2) * w (1, 1)) * (w (2, 0) * w (3, 3) + w (2, 3) * w (3, 0)) + (w (0, 1) * w (1, 3) + w (0, 3) * w (1, 1)) * (w (2, 0) * w (3, 2) + w (2, 2) * w (3, 0)) + (w (0, 2) * w (1, 3) + w (0, 3) * w (1, 2)) * (w (2, 0) * w (3, 1) + w (2, 1) * w (3, 0)) := by
  have sum_perm_succ : ∀ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ),
      ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
    intro n g
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  intro w
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_prod,
    Matrix.mvPolynomialX_apply, MvPolynomial.eval_X]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring
