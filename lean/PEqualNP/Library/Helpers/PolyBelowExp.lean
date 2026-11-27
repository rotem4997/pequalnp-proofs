import Mathlib.Analysis.SpecificLimits.Normed
import PEqualNP.Library.Helpers.PolyExp

/-!
# A polynomial is below `2 ^ (n ^ k)` up to constants, for `k ≥ 1`

Helper module (proofs only, no statement may use it).
-/

namespace PEqualNP.Library.Helpers

open Filter Topology

/-- A power of `n` is below `2 ^ n` plus a constant. -/
theorem pow_le_two_pow_add_const (d : ℕ) : ∃ C : ℕ, ∀ n : ℕ, n ^ d ≤ 2 ^ n + C := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1 : ℝ) < 2)
  have hev := h.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N ^ d, fun n => ?_⟩
  rcases Nat.lt_or_ge n N with hn | hn
  · exact (Nat.pow_le_pow_left hn.le d).trans (Nat.le_add_left _ _)
  · have h1 := hN n hn
    have hpos : (0 : ℝ) < 2 ^ n := by positivity
    rw [div_le_one hpos] at h1
    have h2 : n ^ d ≤ 2 ^ n := by exact_mod_cast h1
    exact h2.trans (Nat.le_add_right _ _)

/-- A polynomial with natural coefficients is below `2 ^ (n ^ k)` plus a constant, `k ≥ 1`. -/
theorem polynomial_le_two_pow_pow_add_const (p : Polynomial ℕ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, ∀ n : ℕ, p.eval n ≤ 2 ^ (n ^ k) + C := by
  obtain ⟨d, hd⟩ := polynomial_le_pow_add p
  obtain ⟨C, hC⟩ := pow_le_two_pow_add_const d
  refine ⟨C + d, fun n => ?_⟩
  have h1 := hd n
  have h2 := hC n
  have h3 : 2 ^ n ≤ 2 ^ (n ^ k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by omega) n)
  omega

end PEqualNP.Library.Helpers
