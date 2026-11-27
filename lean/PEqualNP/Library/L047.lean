import PEqualNP.Library.L008
import PEqualNP.Library.L046

/-- P is closed under union: by complement and intersection. -/
theorem PEqualNP.Library.L047 : ∀ L₁ L₂ : Language Bool, L₁ ∈ PEqualNP.Library.P →
    L₂ ∈ PEqualNP.Library.P → L₁ ⊔ L₂ ∈ PEqualNP.Library.P := by
  intro L₁ L₂ h₁ h₂
  have := PEqualNP.Library.L008 _ (PEqualNP.Library.L046 _ _ (PEqualNP.Library.L008 L₁ h₁)
    (PEqualNP.Library.L008 L₂ h₂))
  rwa [compl_inf, compl_compl, compl_compl] at this
