import PEqualNP.MetaComplexity.Helpers.Machines.ExpandPoly

/-- Partial MCSP has a polynomial-time verifier, sound on every string, with short witnesses:
an instance with size bound `s` and a table on `n` inputs consistent with a circuit of size
`t ≤ s` has a witness of length at most `a * (n + t + 1) ^ 2`, whatever the length of the table
and whatever `s`. The witness is one row of the full witness; the verifier rebuilds the other
rows from it and from the table of the instance. -/
theorem PEqualNP.MetaComplexity.L023 :
    ∃ (V : Set (List Bool × List Bool)) (a : ℕ), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair V ∧ (∀ y c : List Bool, (y, c) ∈ V → y ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ∀ (n s t : ℕ) (T : List (Option Bool)) (f : (Fin n → Bool) → Bool), T.length = 2 ^ n → PEqualNP.MetaComplexity.Consistent n T f → PEqualNP.MetaComplexity.HasCircuitSize n f t → t ≤ s → ∃ c : List Bool, c.length ≤ a * (n + t + 1) ^ 2 ∧ (List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T, c) ∈ V :=
  PEqualNP.MetaComplexity.Helpers.Machines.shortWitness
