import PEqualNP.Defs

/-- A CNF formula is satisfiable exactly when its set of clauses, each read as the finite set of
its literals, is satisfiable in the sense of the proof complexity definitions. -/
theorem PEqualNP.Library.L038 : ∀ φ : PEqualNP.Search.CNF, PEqualNP.Search.Satisfiable φ ↔
    PEqualNP.ProofComplexity.Satisfiable
      {C : PEqualNP.ProofComplexity.Clause ℕ | ∃ c ∈ φ, C = c.toFinset} := by
  intro φ
  simp only [PEqualNP.Search.Satisfiable, PEqualNP.ProofComplexity.Satisfiable,
    PEqualNP.ProofComplexity.Satisfies, PEqualNP.ProofComplexity.ClauseSat,
    PEqualNP.Search.CNF.eval, List.all_eq_true, PEqualNP.Search.Clause.eval, List.any_eq_true,
    PEqualNP.Search.Literal.eval, beq_iff_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    rintro C ⟨c, hc, rfl⟩
    obtain ⟨l, hl, h⟩ := hσ c hc
    exact ⟨l, List.mem_toFinset.mpr hl, h⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, fun c hc => ?_⟩
    obtain ⟨l, hl, h⟩ := hσ c.toFinset ⟨c, hc, rfl⟩
    exact ⟨l, List.mem_toFinset.mp hl, h⟩
