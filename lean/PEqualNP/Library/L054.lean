import PEqualNP.Library.SearchHelpers.ResLin

/-- Res(lin) is sound: a formula with a Res(lin) refutation is unsatisfiable. -/
theorem PEqualNP.Library.L054 : ∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (π : List (PEqualNP.Search.LinClause n)), PEqualNP.Search.IsResLinRefutation F π →
    ¬ PEqualNP.ProofComplexity.Satisfiable F := by
  rintro n F π ⟨hd, he⟩ ⟨a, ha⟩
  obtain ⟨e, he', -⟩ :=
    PEqualNP.Library.SearchHelpers.resLin_lines_hold F a ha π hd [] he
  simp at he'
