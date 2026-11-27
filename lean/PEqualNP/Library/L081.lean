import PEqualNP.Search.Helpers.ResLinQ

/-- Res(lin) over the integers is sound. -/
theorem PEqualNP.Library.L081 : ∀ {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.Search.QLine V)),
    PEqualNP.Search.IsResLinQRefutation F π → ¬ PEqualNP.ProofComplexity.Satisfiable F := by
  intro V _ _ F π ⟨hd, he⟩ ⟨a, ha⟩
  obtain ⟨e, he', -⟩ := PEqualNP.Search.Helpers.resLinQ_lines_hold F a ha π hd [] he
  simp at he'
