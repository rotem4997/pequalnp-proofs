import PEqualNP.MetaComplexity.Helpers.Parity4

/-- Parity of `n` inputs has no circuit of AND, OR and NOT gates of fan-in two with fewer than
`4 (n - 1)` gates. -/
theorem PEqualNP.MetaComplexity.L031 : ∀ (n s : ℕ), PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s → 4 * (n - 1) ≤ s :=
  PEqualNP.MetaComplexity.Helpers.parity_lower4
