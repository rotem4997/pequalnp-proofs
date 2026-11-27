import PEqualNP.Defs

/-- A reduction also reduces the complements, by the same function. -/
theorem PEqualNP.Library.L040 : ∀ L₁ L₂ : Language Bool,
    PEqualNP.Library.PolyTimeReducible L₁ L₂ → PEqualNP.Library.PolyTimeReducible L₁ᶜ L₂ᶜ :=
  fun L₁ L₂ ⟨f, hf, h⟩ => ⟨f, hf, fun x => (show x ∉ L₁ ↔ f x ∉ L₂ from not_congr (h x))⟩
