import PEqualNP.Gct.Helpers.BezoutBox

/-- Elementary Bezout with `D i + 1`: a polynomial map with component degrees at most `D i` has
at most `∏ (D i + 1)` zeros with invertible Jacobian. -/
theorem PEqualNP.Gct.L038 :
    ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ), (∀ i, (F i).totalDegree ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card ≤ ∏ i, (D i + 1) :=
  fun N F D hF S hS => PEqualNP.Gct.Helpers.bezout_box N F D hF S hS
