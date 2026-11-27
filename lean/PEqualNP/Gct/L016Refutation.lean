import PEqualNP.Defs
import Mathlib.Tactic

/-- L-gct-016 fails for 1 x 1 matrices: `M = 0`, `E = 1`. The determinant of the 1 x 1 matrix of
variables is a variable, so its Hessian is zero and every `E` is in its kernel, while the
adjugate of a 1 x 1 matrix is `1`. -/
theorem PEqualNP.Gct.L016Refutation : ¬ ∀ (n : ℕ) (M E : Matrix (Fin n) (Fin n) ℂ), M.det = 0 → (∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n, MvPolynomial.eval (fun p => M p.1 p.2) (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.detPoly ℂ n))) * E b.1 b.2 = 0) → M.adjugate * E = 0 ∧ E * M.adjugate = 0 := by
  intro h
  have h1 := h 1 0 1 (by simp) (by
    intro a
    have hd : PEqualNP.Gct.detPoly ℂ 1 = MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) := by
      simp [PEqualNP.Gct.detPoly, Matrix.mvPolynomialX_apply]
    rw [hd]
    apply Finset.sum_eq_zero
    intro b _
    have : MvPolynomial.pderiv a (MvPolynomial.pderiv b
        (MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) : MvPolynomial (Fin 1 × Fin 1) ℂ)) = 0 := by
      rw [MvPolynomial.pderiv_X]
      by_cases hb : ((0 : Fin 1), (0 : Fin 1)) = b
      · simp [hb]
      · simp [hb]
    rw [this]; simp)
  have h2 := h1.1
  rw [Matrix.adjugate_fin_one, one_mul] at h2
  have := congrFun (congrFun h2 0) 0
  simp at this
