import PEqualNP.Defs

/-- Splitting rule: a formula is satisfiable exactly when one of its two branches on a variable
is satisfiable. -/
theorem PEqualNP.Library.L025 : ∀ (φ : PEqualNP.Search.CNF) (i : ℕ),
    PEqualNP.Search.Satisfiable φ ↔ (PEqualNP.Search.Satisfiable ([(i, true)] :: φ) ∨
      PEqualNP.Search.Satisfiable ([(i, false)] :: φ)) := by
  intro φ i
  simp only [PEqualNP.Search.Satisfiable, PEqualNP.Search.CNF.eval, List.all_cons,
    Bool.and_eq_true, PEqualNP.Search.Clause.eval, List.any_cons, List.any_nil,
    Bool.or_false, PEqualNP.Search.Literal.eval]
  constructor
  · rintro ⟨σ, hσ⟩
    cases h : σ i
    · exact Or.inr ⟨σ, by simp [h], hσ⟩
    · exact Or.inl ⟨σ, by simp [h], hσ⟩
  · rintro (⟨σ, -, hσ⟩ | ⟨σ, -, hσ⟩) <;> exact ⟨σ, hσ⟩
