import PEqualNP.CircuitLowerBounds.Helpers.Switching.Chain
import PEqualNP.CircuitLowerBounds.Helpers.Switching.Core

/-- L-lib-034: Hastad's bound for parity. For one constant `c`, every depth `d ≥ 2` and all
large `n`, a circuit of AND, OR and NOT gates of depth at most `d` deciding parity on `n` bits
has size `s` with `n ≤ (c log2 s)^(d - 1)`. By the switching lemma (counting form, by
encoding) and induction on the depth. -/
theorem PEqualNP.Library.L034 :
    ∃ c : ℕ, ∀ d : ℕ, 2 ≤ d → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) → C.depth n ≤ d → C.Decides ({x : List Bool | x.count true % 2 = 1} : Language Bool) n → n ≤ (c * Nat.log 2 C.size) ^ (d - 1) :=
  PEqualNP.CircuitLowerBounds.Switching.stmt034_of_switching
    PEqualNP.CircuitLowerBounds.Switching.Core.switchingSem
