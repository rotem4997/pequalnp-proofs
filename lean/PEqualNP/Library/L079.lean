import PEqualNP.Library.Helpers.AlgCollapseFacts

/-- Every oracle has a multiquadratic extension: its multilinear extension. -/
theorem PEqualNP.Library.L079 : ∀ A : Language Bool, ∃ E : PEqualNP.Library.AlgExtension, PEqualNP.Library.IsMultiquadraticExtension A E :=
  fun A => ⟨_, PEqualNP.Library.Helpers.AlgCollapseFacts.mlext_ext A⟩
