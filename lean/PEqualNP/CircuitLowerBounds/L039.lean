import PEqualNP.CircuitLowerBounds.L037

/-- A circuit of AND, OR and NOT gates of fan-in at most two that decides SAT at length
`6 * q` (for `q ≥ 2`) has at least `6 * q - 1` gates. -/
theorem PEqualNP.CircuitLowerBounds.L039 :
    ∀ q : ℕ, 2 ≤ q → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) → D.Decides PEqualNP.Search.SAT (6 * q) → 6 * q ≤ D.size + 1 :=
  PEqualNP.CircuitLowerBounds.Helpers.SatSlice.s2_of PEqualNP.CircuitLowerBounds.L037
