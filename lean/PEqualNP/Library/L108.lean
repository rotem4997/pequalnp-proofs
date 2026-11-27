import PEqualNP.Search.Helpers.CPComplete.Complete

/-- Cutting planes is complete (Cook, Coullard and Turan 1987): every unsatisfiable set of
clauses over a finite variable type has a cutting planes refutation. -/
theorem PEqualNP.Library.L108 : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)), ¬ PEqualNP.ProofComplexity.Satisfiable F →
    ∃ π : List (PEqualNP.Search.CPLine V), PEqualNP.Search.IsCPRefutation F π :=
  fun _ _ _ F hF => PEqualNP.Search.Helpers.CPComplete.complete F hF
