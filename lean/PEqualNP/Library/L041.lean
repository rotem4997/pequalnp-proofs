import PEqualNP.Library.L009

/-- NP-hardness transfers along reductions, because reductions compose. -/
theorem PEqualNP.Library.L041 : ∀ L₁ L₂ : Language Bool, PEqualNP.Library.NPHard L₁ →
    PEqualNP.Library.PolyTimeReducible L₁ L₂ → PEqualNP.Library.NPHard L₂ :=
  fun L₁ L₂ h hr L' hL' => PEqualNP.Library.L009 L' L₁ L₂ (h L' hL') hr
