import PEqualNP.Search.Helpers.RUP.Quad

/-- Clause learning by unit propagation is simulated by resolution: a run of RUP clauses that
learns the empty clause yields a resolution refutation of at most
`(number of learned clauses) * (2 * number of variables + 1) ^ 2` lines. -/
theorem PEqualNP.Library.L112 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (ρ : List (PEqualNP.ProofComplexity.Clause V)), PEqualNP.Search.IsRUPRun F ρ → (∅ : PEqualNP.ProofComplexity.Clause V) ∈ ρ → ∃ π : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F π ∧ π.length ≤ ρ.length * (2 * Fintype.card V + 1) ^ 2 :=
  fun _ _ _ _ _ h he => PEqualNP.Search.Helpers.RUP.refutation_of_run_quad h he
