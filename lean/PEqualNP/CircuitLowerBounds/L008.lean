import PEqualNP.CircuitLowerBounds.Helpers.Approx
import PEqualNP.CircuitLowerBounds.Helpers.Smolensky3

/-- MOD `q` is not in AC0[`p`] for distinct primes `p` and `q`: no family of circuits of
polynomial size and constant depth over AND, OR, NOT and MOD `p` gates decides whether the
number of true bits is divisible by `q` (Razborov 1987, Smolensky 1987). -/
theorem PEqualNP.CircuitLowerBounds.L008 :
    ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≠ q → ({x : List Bool | x.count true % q = 0} : Language Bool) ∉ PEqualNP.CircuitLowerBounds.AC0Mod p :=
  PEqualNP.CircuitLowerBounds.Helpers.modq_not_in_ac0p_of
    PEqualNP.CircuitLowerBounds.Helpers.approx
