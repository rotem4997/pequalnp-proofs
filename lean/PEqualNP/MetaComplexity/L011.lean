import PEqualNP.MetaComplexity.Helpers.Support

/-- A Boolean function that depends on each of its `n` inputs has no fan-in two circuit with
fewer than `n - 1` gates. -/
theorem PEqualNP.MetaComplexity.L011 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
    (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → n ≤ s + 1 :=
  PEqualNP.MetaComplexity.Helpers.dep_lower
