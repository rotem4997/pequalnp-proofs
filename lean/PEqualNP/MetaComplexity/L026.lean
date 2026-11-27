import PEqualNP.MetaComplexity.Helpers.XorChain

/-- The parity of `n` inputs has a fan-in two circuit with `4 (n - 1)` gates: each exclusive or
is `(a or b) and not (a and b)`. -/
theorem PEqualNP.MetaComplexity.L026 : ∀ n : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) (4 * (n - 1)) := by
  intro n
  cases n with
  | zero =>
    refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
    intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
  | succ k =>
    obtain ⟨gs, out, ok, len, _, ev⟩ :=
      PEqualNP.MetaComplexity.Helpers.xorChain k (k + 1) le_rfl
    refine ⟨⟨gs, out⟩, ok, by simp only [PEqualNP.CircuitLowerBounds.Circuit.size]; omega, ?_⟩
    intro x
    have h := ev (List.ofFn x) (by simp)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.MetaComplexity.Helpers.wires_eq, h, PEqualNP.MetaComplexity.Helpers.getD_ofFn]
    rfl
