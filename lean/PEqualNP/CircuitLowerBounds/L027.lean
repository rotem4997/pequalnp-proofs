import PEqualNP.CircuitLowerBounds.Helpers.EncodeLength

/-- A language with depth-two threshold circuits with `s n` bottom gates has, at every length
`n`, such a circuit as data whose binary code has length at most `100 * (n + s n + 3) ^ 4`
(small integer weights, clamped thresholds, and a bit count). -/
theorem PEqualNP.CircuitLowerBounds.L027 :
    ∀ (s : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.CircuitLowerBounds.THRTHR s → ∀ n : ℕ,
      ∃ c : PEqualNP.CircuitLowerBounds.ThrCircuit, c.inputs = n ∧
        (∀ x : Fin n → Bool, List.ofFn x ∈ L ↔ c.eval (List.ofFn x) = true) ∧
        (PEqualNP.CircuitLowerBounds.encodeThr c).length ≤ 100 * (n + s n + 3) ^ 4 :=
  PEqualNP.CircuitLowerBounds.Helpers.thrthr_short_code
