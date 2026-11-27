import PEqualNP.Gct.Helpers.Persist

/-- Nondegenerate zeros of a polynomial map persist under coefficientwise limits of bounded
degree. -/
theorem PEqualNP.Gct.L030 :
    ∀ (d D : ℕ) (F : Fin d → MvPolynomial (Fin d) ℂ) (Fk : ℕ → Fin d → MvPolynomial (Fin d) ℂ), (∀ k i, (Fk k i).totalDegree ≤ D) → (∀ i s, Filter.Tendsto (fun k => (Fk k i).coeff s) Filter.atTop (nhds ((F i).coeff s))) → ∀ S : Finset (Fin d → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → ∃ K, ∀ k ≥ K, ∃ T : Finset (Fin d → ℂ), T.card = S.card ∧ ∀ x ∈ T, (∀ i, MvPolynomial.eval x (Fk k i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (Fk k i))).det ≠ 0 :=
  fun d D F Fk hdeg hconv S hS =>
    PEqualNP.Gct.Helpers.nondeg_zeros_persist d D F Fk hdeg hconv S hS
