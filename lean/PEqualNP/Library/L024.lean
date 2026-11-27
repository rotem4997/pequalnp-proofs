import PEqualNP.Defs

/-- The resolution rule is sound. -/
theorem PEqualNP.Library.L024 : ∀ (σ : PEqualNP.Search.Assignment)
    (C D : PEqualNP.Search.Clause) (i : ℕ),
    PEqualNP.Search.Clause.eval σ ((i, true) :: C) = true →
    PEqualNP.Search.Clause.eval σ ((i, false) :: D) = true →
    PEqualNP.Search.Clause.eval σ (C ++ D) = true := by
  intro σ C D i h1 h2
  simp only [PEqualNP.Search.Clause.eval, List.any_cons, List.any_append,
    Bool.or_eq_true, PEqualNP.Search.Literal.eval] at *
  cases hσ : σ i <;> simp_all
