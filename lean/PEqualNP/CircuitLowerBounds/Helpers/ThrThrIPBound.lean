import Mathlib
import PEqualNP.CircuitLowerBounds.Helpers.ThrThrIP
import PEqualNP.CircuitLowerBounds.Helpers.WeightBound

/-!
The gate lower bound for inner product as a threshold of thresholds: the top-weight bound
(`ThrThrIP`) with the small-weights normal form of the top gate (`WeightBound`).
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

theorem ip_thrthr_gate_bound :
    ∀ s : ℕ → ℕ, ({x : List Bool | ((List.range (x.length / 2)).filter (fun i => x.getD i false && x.getD (i + x.length / 2) false)).length % 2 = 1} : Language Bool) ∈ PEqualNP.CircuitLowerBounds.THRTHR s → ∀ n : ℕ, 0 < n → (2 : ℤ) ^ n ≤ (2 * ((s (2 * n) : ℤ) + 2) ^ (s (2 * n) + 2) * ((n : ℤ) + 2)) ^ 2 := by
  intro s hs n hn
  refine ip_thrthr_gate_bound_of (fun k => ((k : ℤ) + 2) ^ (k + 2)) threshold_small_weights ?_ s hs n hn
  intro k l hkl
  have h1 : ((k : ℤ) + 2) ^ (k + 2) ≤ ((l : ℤ) + 2) ^ (k + 2) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 2) _
  have h2 : ((l : ℤ) + 2) ^ (k + 2) ≤ ((l : ℤ) + 2) ^ (l + 2) :=
    pow_le_pow_right₀ (by linarith [Int.natCast_nonneg l]) (by omega)
  exact h1.trans h2

end PEqualNP.CircuitLowerBounds.Helpers
