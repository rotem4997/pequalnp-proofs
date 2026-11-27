import PEqualNP.MetaComplexity.Helpers.LupanovTwoLevel
import PEqualNP.MetaComplexity.Helpers.LupanovCount

/-- Every Boolean function on `n ≥ 1` inputs has a circuit with at most `56 * 2^n / n` gates: a
library of all functions of the first `k` inputs and a multiplexer on the rest, with
`k = log2 n - 1` (Lupanov's upper bound up to the constant). -/
theorem PEqualNP.MetaComplexity.L003 : ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ f : (Fin n → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize n f (c * 2 ^ n / n) := by
  refine ⟨56, fun n hn f => ?_⟩
  have hk : Nat.log 2 n - 1 ≤ n := (Nat.sub_le _ _).trans (Nat.log_le_self 2 n)
  exact PEqualNP.MetaComplexity.Helpers.hasCircuitSize_mono
    (PEqualNP.MetaComplexity.Helpers.lupanovTwoLevel _ n hk f)
    ((Nat.le_div_iff_mul_le (by omega)).2 (PEqualNP.MetaComplexity.Helpers.lupanovCount n hn))
