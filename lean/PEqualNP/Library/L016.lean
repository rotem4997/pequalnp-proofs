import PEqualNP.Library.L007

/-- P is closed under polynomial-time reductions: run the reduction, then the decider. -/
theorem PEqualNP.Library.L016 : ∀ L₁ L₂ : Language Bool,
    PEqualNP.Library.PolyTimeReducible L₁ L₂ → L₂ ∈ PEqualNP.Library.P →
    L₁ ∈ PEqualNP.Library.P :=
  fun _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩ =>
    ⟨fun x => g (f x), fun x => (hf' x).trans (hg (f x)),
      PEqualNP.Library.L007 _ _ _ _ _ _ _ _ _ f g hf hg'⟩
