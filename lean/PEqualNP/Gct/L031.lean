import PEqualNP.Defs

/-- An exact determinantal expression is a border expression: the constant sequence. -/
theorem PEqualNP.Gct.L031 : ∀ (σ : Type) (p : MvPolynomial σ ℂ) (n : ℕ), PEqualNP.Gct.HasDetExpression p n → PEqualNP.Gct.HasBorderDetExpression p n :=
  fun _ p _ h => ⟨fun _ => p, fun _ => h, fun _ => tendsto_const_nhds⟩
