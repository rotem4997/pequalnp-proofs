import PEqualNP.Defs

/-- A CNF formula in which every clause has a positive literal is satisfiable: the all-true
assignment satisfies it. -/
theorem PEqualNP.Library.L023 : ∀ φ : PEqualNP.Search.CNF,
    (∀ c ∈ φ, ∃ i : ℕ, (i, true) ∈ c) → PEqualNP.Search.Satisfiable φ := by
  intro φ h
  refine ⟨fun _ => true, List.all_eq_true.mpr fun c hc => ?_⟩
  obtain ⟨i, hi⟩ := h c hc
  exact List.any_eq_true.mpr ⟨(i, true), hi, rfl⟩
