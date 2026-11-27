import PEqualNP.Library.Helpers.OracleVerifier

open Classical in
/-- Relative to any oracle `B`, the set of strings `x` such that `B` has a member of the same
length as `x` is in NP^B. -/
theorem PEqualNP.Library.L060 : ∀ B : Language Bool, ({x : List Bool | ∃ w ∈ B, w.length = x.length} : Language Bool) ∈ PEqualNP.Library.OracleNP B := by
  intro B
  refine ⟨{p | p.2.length = p.1.length ∧ p.2 ∈ B}, Polynomial.X, ?_, ?_⟩
  · refine ⟨Polynomial.C 2 * Polynomial.X + Polynomial.C 4, ?_⟩
    refine ⟨fun p => decide (p.2.length = p.1.length ∧ p.2 ∈ B),
      PEqualNP.Library.Helpers.OracleVerifier.ovM, Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    · intro p
      simp
    · rintro ⟨x, w⟩
      obtain ⟨h⟩ := PEqualNP.Library.Helpers.OracleVerifier.ov_run B x w
      refine ⟨⟨h.toEvalsTo, ?_⟩⟩
      have := h.steps_le_m
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
  · intro x
    simp only [Set.mem_ofPred_eq, Polynomial.eval_X]
    constructor
    · rintro ⟨w, hw, hl⟩
      exact ⟨w, hl.le, hl, hw⟩
    · rintro ⟨w, -, hl, hw⟩
      exact ⟨w, hw, hl⟩
