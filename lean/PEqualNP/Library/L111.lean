import PEqualNP.Search.Helpers.RUP.Trivial

/-- Clause learning by unit propagation is simulated by resolution with linear overhead: a run
of RUP clauses that learns the empty clause yields a resolution refutation of at most
`c * (number of learned clauses) * (number of variables + 1)` lines (Beame, Kautz and
Sabharwal 2004). -/
theorem PEqualNP.Library.L111 : ∃ c : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (ρ : List (PEqualNP.ProofComplexity.Clause V)), PEqualNP.Search.IsRUPRun F ρ → (∅ : PEqualNP.ProofComplexity.Clause V) ∈ ρ → ∃ π : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.ProofComplexity.IsRefutation F π ∧ π.length ≤ c * (ρ.length * (Fintype.card V + 1)) :=
  ⟨4, fun _ _ _ _ _ h he => PEqualNP.Search.Helpers.RUP.refutation_of_run h he⟩
