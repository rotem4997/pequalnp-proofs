import PEqualNP.MetaComplexity.Helpers.LocalClose

/-- The target of the local reduction chain. For an exponent `a / b` below one half and a
constant `c`, at every large enough length `n` no map from `n`-bit inputs to strings of length
at most `n ^ c + c` reduces parity to partial MCSP while being `q`-local with `q ^ b ≤ n ^ a`
and sending the all-false input to a table with a consistent circuit of at most
`q (log n + 1) ^ c` gates. -/
theorem PEqualNP.MetaComplexity.L033 : ∀ (a b c : ℕ), 2 * a < b → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ ∃ (q : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q ∧ q ^ b ≤ n ^ a ∧ PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length ≤ n ^ c + c) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f (q * (Nat.log 2 n + 1) ^ c) :=
  PEqualNP.MetaComplexity.Helpers.LocalClose.asymptotic
