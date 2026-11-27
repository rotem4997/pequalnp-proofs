import Mathlib.Tactic

/-!
# Helper module (proofs only): polynomial bounds below an exponential

This is a helper module: it contains only auxiliary lemmas used in proofs of library lemmas,
and no definitions.

* `polynomial_le_pow_add`: every polynomial with natural coefficients is below `n ^ k + k`
  for some `k`.
* `polynomial_le_two_pow_pow_add`: hence below `2 ^ (n ^ k) + k` for some `k`.
-/

namespace PEqualNP.Library.Helpers

/-- Every polynomial with natural coefficients is below `n ^ k + k` for some `k`. -/
theorem polynomial_le_pow_add (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, Polynomial.eval n p ≤ n ^ k + k := by
  have small : ∀ (n e : ℕ), n < 2 → n ^ e ≤ 1 := fun n e hn => by
    have := Nat.pow_le_pow_left (show n ≤ 1 by omega) e
    rwa [Nat.one_pow] at this
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b + 2, fun n => ?_⟩
    rw [Polynomial.eval_add]
    have h1 := ha n
    have h2 := hb n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n a hn
      have e2 := small n b hn
      omega
    · have pa : n ^ a ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have pb : n ^ b ≤ n ^ (a + b) := Nat.pow_le_pow_right (by omega) (by omega)
      have ps : n ^ (a + b + 1) = n ^ (a + b) * n := Nat.pow_succ ..
      have pt : n ^ (a + b + 1) ≤ n ^ (a + b + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 * n ^ (a + b) ≤ n ^ (a + b) * n := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hn
      omega
  | monomial d c =>
    refine ⟨d + c, fun n => ?_⟩
    rw [Polynomial.eval_monomial]
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have e1 := small n d hn
      calc c * n ^ d ≤ c * 1 := Nat.mul_le_mul_left _ e1
        _ ≤ n ^ (d + c) + (d + c) := by omega
    · have hc : c ≤ n ^ c := (Nat.lt_pow_self (by omega)).le
      calc c * n ^ d ≤ n ^ c * n ^ d := Nat.mul_le_mul_right _ hc
        _ = n ^ (d + c) := by rw [Nat.add_comm, Nat.pow_add]
        _ ≤ n ^ (d + c) + (d + c) := Nat.le_add_right _ _

/-- Every polynomial with natural coefficients is below `2 ^ (n ^ k) + k` for some `k`. -/
theorem polynomial_le_two_pow_pow_add (p : Polynomial ℕ) :
    ∃ k : ℕ, ∀ n : ℕ, Polynomial.eval n p ≤ 2 ^ (n ^ k) + k := by
  obtain ⟨k, hk⟩ := polynomial_le_pow_add p
  exact ⟨k, fun n => (hk n).trans (Nat.add_le_add_right Nat.lt_two_pow_self.le k)⟩

end PEqualNP.Library.Helpers
