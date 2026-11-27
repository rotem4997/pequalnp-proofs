import PEqualNP.CircuitLowerBounds.Helpers.SmolenskyAvg

/-- Parity is hard on average for AC0[`p`], `p` an odd prime: for every polynomial size bound,
depth `d` and `K`, at every large input length `n` a circuit over AND, OR, NOT and MOD `p`
gates agrees with parity on at most `(1 / 2 + 1 / (2 * K)) * 2 ^ n` inputs (Razborov 1987,
Smolensky 1987). -/
theorem PEqualNP.CircuitLowerBounds.L032 :
    ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ∀ (P : Polynomial ℕ) (d K : ℕ), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not, PEqualNP.CircuitLowerBounds.GateOp.mod p} : Set PEqualNP.CircuitLowerBounds.GateOp)) → C.size ≤ P.eval n → C.depth n ≤ d → (Finset.univ.filter fun x : Fin n → Bool => C.eval (List.ofFn x) = decide ((List.ofFn x).count true % 2 = 1)).card * (2 * K) ≤ (K + 1) * 2 ^ n :=
  PEqualNP.CircuitLowerBounds.Helpers.parity_avg_hard
