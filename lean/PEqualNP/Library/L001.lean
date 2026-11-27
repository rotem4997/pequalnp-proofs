import PEqualNP.Defs

/-- Polynomial-time reducibility is reflexive: the identity map reduces a language to itself. -/
theorem PEqualNP.Library.L001 : ∀ L : Language Bool, PEqualNP.Library.PolyTimeReducible L L :=
  fun _ => ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun _ => Iff.rfl⟩
