import PEqualNP.Gct.Helpers.DetExprExists

/-- Valiant: every polynomial over a field has a determinantal expression. -/
theorem PEqualNP.Gct.L005 : ∀ (K : Type) [Field K] (k : ℕ) (p : MvPolynomial (Fin k) K),
    ∃ n : ℕ, PEqualNP.Gct.HasDetExpression p n :=
  fun K _ k p => PEqualNP.Gct.Helpers.DetExprExists.hasDetExpression_of_any (Fin k) K p
