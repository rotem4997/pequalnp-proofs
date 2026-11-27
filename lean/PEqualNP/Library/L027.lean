import PEqualNP.Defs

/-- Pure literal rule: if the negation of `l` occurs in no clause, deleting the clauses that
contain `l` does not change satisfiability. -/
theorem PEqualNP.Library.L027 : ∀ (φ : PEqualNP.Search.CNF) (l : PEqualNP.Search.Literal),
    (∀ c ∈ φ, (l.1, !l.2) ∉ c) →
    (PEqualNP.Search.Satisfiable φ ↔
      PEqualNP.Search.Satisfiable (φ.filter (fun c => decide (l ∉ c)))) := by
  intro φ l hpure
  simp only [PEqualNP.Search.Satisfiable, PEqualNP.Search.CNF.eval, List.all_eq_true,
    List.mem_filter, decide_eq_true_eq, and_imp]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun c hc _ => hσ c hc⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨Function.update σ l.1 l.2, fun c hc => ?_⟩
    simp only [PEqualNP.Search.Clause.eval, List.any_eq_true, PEqualNP.Search.Literal.eval,
      beq_iff_eq] at hσ ⊢
    by_cases hl : l ∈ c
    · exact ⟨l, hl, by simp⟩
    · obtain ⟨m, hm, hmv⟩ := hσ c hc hl
      refine ⟨m, hm, ?_⟩
      by_cases hv : m.1 = l.1
      · exfalso
        obtain ⟨i, b⟩ := m
        obtain ⟨j, b'⟩ := l
        simp only at hv
        subst hv
        cases b <;> cases b' <;> simp_all
      · rw [Function.update_of_ne hv]
        exact hmv
