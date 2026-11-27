import PEqualNP.CircuitLowerBounds.Helpers.ThrThrXor

/-- Depth-two threshold circuits are closed under symmetric difference with a polynomial
blow-up: the exclusive or of two languages with such circuits with `s1 n` and `s2 n` bottom
gates has such circuits with at most `c * (s1 n + s2 n + n + 1) ^ c` bottom gates, for one
constant `c` (Chen and Williams 2019, by way of the exact threshold gates of Hansen and
Podolskii 2010). -/
theorem PEqualNP.CircuitLowerBounds.L030 :
    ∃ c : ℕ, ∀ (s1 s2 : ℕ → ℕ) (L1 L2 : Language Bool), L1 ∈ PEqualNP.CircuitLowerBounds.THRTHR s1 → L2 ∈ PEqualNP.CircuitLowerBounds.THRTHR s2 → ({x : List Bool | (x ∈ L1 ∧ x ∉ L2) ∨ (x ∉ L1 ∧ x ∈ L2)} : Language Bool) ∈ PEqualNP.CircuitLowerBounds.THRTHR (fun n : ℕ => c * (s1 n + s2 n + n + 1) ^ c) :=
  PEqualNP.CircuitLowerBounds.Helpers.thrthr_xor
