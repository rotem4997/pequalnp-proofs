import PEqualNP.Library.L007

/-- Polynomial-time reducibility is transitive: compose the two reductions. -/
theorem PEqualNP.Library.L009 : ∀ L₁ L₂ L₃ : Language Bool,
    PEqualNP.Library.PolyTimeReducible L₁ L₂ → PEqualNP.Library.PolyTimeReducible L₂ L₃ →
    PEqualNP.Library.PolyTimeReducible L₁ L₃ :=
  fun _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩ =>
    ⟨fun x => g (f x), PEqualNP.Library.L007 _ _ _ _ _ _ _ _ _ f g hf hg,
      fun x => (hf' x).trans (hg' (f x))⟩
