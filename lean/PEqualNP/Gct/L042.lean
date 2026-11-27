import PEqualNP.Gct.Helpers.BezPoints

/-- L-gct-042, count lemma B: a square complex system whose top-degree parts vanish together
only at 0 and whose common zeros all have invertible Jacobian has at least the product of the
degrees many common zeros. -/
theorem PEqualNP.Gct.L042 :
    ∀ (n : ℕ) (f : Fin n → MvPolynomial (Fin n) ℂ), (∀ x : Fin n → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.homogeneousComponent (f i).totalDegree (f i)) = 0) → x = 0) → (∀ x : Fin n → ℂ, (∀ i, MvPolynomial.eval x (f i) = 0) → (Matrix.of fun i j : Fin n => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))).det ≠ 0) → ∃ S : Finset (Fin n → ℂ), (∏ i, (f i).totalDegree) ≤ S.card ∧ ∀ x ∈ S, ∀ i, MvPolynomial.eval x (f i) = 0 :=
  PEqualNP.Gct.Helpers.bezCountB_holds
