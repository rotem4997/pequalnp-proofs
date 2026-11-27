import PEqualNP.MetaComplexity.Helpers.OrChain

/-- The OR of `n` inputs has a fan-in two circuit with `s` gates exactly when `n ≤ s + 1`: its
circuit size is `n - 1`. -/
theorem PEqualNP.MetaComplexity.L012 : ∀ n s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i : Fin n, x i = true)) s ↔ n ≤ s + 1 :=
  PEqualNP.MetaComplexity.Helpers.or_size
