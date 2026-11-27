import PEqualNP.MetaComplexity.Helpers.LocalFormat

/-- A `q`-local map on `n`-bit inputs with outputs of length at most `M` that sends every input
of odd weight into partial MCSP sends the all-false input to a word of the instance format
(a unary bound, a `false`, the code of a partial table of length a power of two), as soon as
`2 * q * (log M + 2) < n`. -/
theorem PEqualNP.MetaComplexity.L029 : ∀ (n q M : ℕ) (w : (Fin n → Bool) → List Bool),
    PEqualNP.MetaComplexity.QueryLocal n q w →
    (∀ x : Fin n → Bool, (w x).length ≤ M) →
    (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 →
      w x ∈ PEqualNP.MetaComplexity.PartialMCSP) →
    2 * q * (Nat.log 2 M + 2) < n →
    ∃ (n' s : ℕ) (T : List (Option Bool)),
      w (fun _ : Fin n => false) =
        List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T ∧
      T.length = 2 ^ n' :=
  PEqualNP.MetaComplexity.Helpers.LocalFormat.formed_of_odd
