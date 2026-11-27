import PEqualNP.MetaComplexity.Helpers.Shannon

/-- Every Boolean function on `n` inputs has a circuit with at most `5 * 2 ^ n` gates: the
Shannon expansion, one variable at a time. -/
theorem PEqualNP.MetaComplexity.L001 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    PEqualNP.MetaComplexity.HasCircuitSize n f (5 * 2 ^ n) := by
  intro n f
  obtain ⟨gs, out, ok, len, _, ev⟩ := PEqualNP.MetaComplexity.Helpers.shannon n f n le_rfl
  refine ⟨⟨gs, out⟩, ok, by simp only [PEqualNP.CircuitLowerBounds.Circuit.size]; omega, ?_⟩
  intro x
  have h := ev (List.ofFn x) (by simp)
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.MetaComplexity.Helpers.wires_eq, h]
  congr 1; funext i; simp
