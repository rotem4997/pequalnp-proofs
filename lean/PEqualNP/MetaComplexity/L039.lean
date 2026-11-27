import PEqualNP.MetaComplexity.Helpers.TotalLocal

/-- The local obstruction for total MCSP. For an exponent `a / b` below one half and a constant
`c`, at every large enough length `n` no map from `n`-bit inputs to strings of length at most
`n ^ c + c` reduces parity to MCSP while being `q`-local with `q ^ b ≤ n ^ a` and sending the
all-false input to a table with a circuit of at most `q (log n + 1) ^ c` gates. -/
theorem PEqualNP.MetaComplexity.L039 : ∀ (a b c : ℕ), 2 * a < b → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ ∃ (q : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q ∧ q ^ b ≤ n ^ a ∧ PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length ≤ n ^ c + c) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.MCSP) ∧ ∀ (n' s : ℕ) (T : List Bool), w (fun _ : Fin n => false) = List.replicate s true ++ false :: T → T.length = 2 ^ n' → PEqualNP.MetaComplexity.HasCircuitSize n' (PEqualNP.MetaComplexity.tableFun n' T) (q * (Nat.log 2 n + 1) ^ c) :=
  PEqualNP.MetaComplexity.Helpers.TotalLocal.asymptotic
