import PEqualNP.Search.Helpers.RUPWitness.FromResolution
import PEqualNP.ProofComplexity.Helpers.Completeness

/-- Every unsatisfiable CNF has a run of RUP clause learning that learns the empty clause:
a resolution refutation (completeness of resolution), read line by line, is such a run. -/
theorem PEqualNP.Library.L114 : ∀ (V : Type) [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)), ¬ PEqualNP.ProofComplexity.Satisfiable F →
    ∃ ρ : List (PEqualNP.ProofComplexity.Clause V), PEqualNP.Search.IsRUPRun F ρ ∧
      (∅ : PEqualNP.ProofComplexity.Clause V) ∈ ρ := by
  intro V _ _ F h
  obtain ⟨π, ⟨hπ, hempty⟩, -⟩ := PEqualNP.ProofComplexity.Helpers.completeness F h
  exact ⟨π, PEqualNP.Search.Helpers.RUPWitness.isRUPRun_of_derivation hπ, hempty⟩
