import PEqualNP.Library.L009

/-- NP-completeness transfers along reductions inside NP: every NP language reduces to `L₁`,
which reduces to `L₂`, and reductions compose. -/
theorem PEqualNP.Library.L020 : ∀ L₁ L₂ : Language Bool, PEqualNP.Library.NPComplete L₁ →
    L₂ ∈ PEqualNP.Library.NP → PEqualNP.Library.PolyTimeReducible L₁ L₂ →
    PEqualNP.Library.NPComplete L₂ :=
  fun L₁ L₂ h₁ h₂ hr =>
    ⟨h₂, fun L' hL' => PEqualNP.Library.L009 L' L₁ L₂ (h₁.2 L' hL') hr⟩
