import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetRadical

/-! L-gct-020: for `n ≥ 2`, the adjugate of a singular matrix kills the radical of the Hessian of
the determinant there. Transvections reduce to a diagonal matrix, where the second derivatives
of the determinant are explicit. -/

theorem PEqualNP.Gct.L020 :
    ∀ (n : ℕ) (M E : Matrix (Fin n) (Fin n) ℂ), 2 ≤ n → M.det = 0 →
      (∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n, MvPolynomial.eval (fun p => M p.1 p.2)
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.detPoly ℂ n))) *
          E b.1 b.2 = 0) →
      M.adjugate * E = 0 ∧ E * M.adjugate = 0 :=
  fun _ M E hn hM hE => PEqualNP.Gct.Helpers.adjugate_mul_radical hn M E hM hE
