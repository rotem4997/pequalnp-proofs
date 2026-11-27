import PEqualNP.Defs

/-- A CNF formula containing the empty clause is unsatisfiable. -/
theorem PEqualNP.Library.L022 : ∀ φ : PEqualNP.Search.CNF, [] ∈ φ →
    ¬ PEqualNP.Search.Satisfiable φ := by
  rintro φ h ⟨σ, hσ⟩
  have := List.all_eq_true.mp hσ [] h
  simp [PEqualNP.Search.Clause.eval] at this
