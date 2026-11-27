import PEqualNP.CircuitLowerBounds.Helpers.SatFiveMain

/-- A circuit of AND, OR and NOT gates of fan-in at most two that decides SAT at length
`4 * k + 2` (for `k ≥ 4`) has at least `5 * k + 1` gates. -/
theorem PEqualNP.CircuitLowerBounds.L041 :
    ∀ k : ℕ, 4 ≤ k → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2) → D.Decides PEqualNP.Search.SAT (4 * k + 2) → 5 * k + 1 ≤ D.size :=
  PEqualNP.CircuitLowerBounds.Helpers.SatFive.main
