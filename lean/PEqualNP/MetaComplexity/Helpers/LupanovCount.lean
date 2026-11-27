import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# The Lupanov size count

The two-level Lupanov circuit (library of all functions on `k = Nat.log 2 n - 1` bits, then a
multiplexer) has size at most `2^(2^k) * (5 * 2^k) + 4 * 2^(n-k)`; times `n` it is at most
`56 * 2^n`.
-/

namespace PEqualNP.MetaComplexity.Helpers

/-- `t^2 ≤ 2 * 2^t` for every natural `t`. -/
theorem sq_le_two_mul_two_pow (t : ℕ) : t ^ 2 ≤ 2 * 2 ^ t := by
  rcases Nat.lt_or_ge t 4 with h | h
  · interval_cases t <;> norm_num
  · induction t, h using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ 2 m]
      nlinarith

theorem lupanovCount (n : ℕ) (hn : 1 ≤ n) :
    (2 ^ 2 ^ (Nat.log 2 n - 1) * (5 * 2 ^ (Nat.log 2 n - 1)) +
      4 * 2 ^ (n - (Nat.log 2 n - 1))) * n ≤ 56 * 2 ^ n := by
  rcases Nat.eq_or_lt_of_le hn with h1 | h2
  · subst h1; norm_num
  have hL : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  obtain ⟨k, hk⟩ : ∃ k, Nat.log 2 n = k + 1 := ⟨Nat.log 2 n - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  have hlo : 2 ^ (k + 1) ≤ n := hk ▸ Nat.pow_log_le_self 2 (by omega)
  have hhi : n < 2 ^ (k + 2) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [hk] at this; simpa using this
  set t := 2 ^ k with ht
  have hlo' : 2 * t ≤ n := by rw [pow_succ] at hlo; linarith
  have hhi' : n < 4 * t := by rw [pow_add] at hhi; norm_num at hhi; linarith
  have hkt : k < t := Nat.lt_two_pow_self
  have hkn : k ≤ n := by omega
  -- multiplexer term
  have hsplit : 2 ^ (n - k) * t = 2 ^ n := by
    rw [ht, ← pow_add, Nat.sub_add_cancel hkn]
  have hmux : 4 * 2 ^ (n - k) * n ≤ 16 * 2 ^ n := by
    have : 2 ^ (n - k) * n ≤ 2 ^ (n - k) * (4 * t) :=
      Nat.mul_le_mul_left _ hhi'.le
    nlinarith
  -- library term
  have h2t : 2 ^ t * 2 ^ t ≤ 2 ^ n := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq := sq_le_two_mul_two_pow t
  have hpos : 0 < 2 ^ t := by positivity
  have hlib : 2 ^ t * (5 * t) * n ≤ 40 * 2 ^ n := by
    have a : 2 ^ t * (5 * t) * n ≤ 2 ^ t * (5 * t) * (4 * t) :=
      Nat.mul_le_mul_left _ hhi'.le
    have b : 2 ^ t * (5 * t) * (4 * t) = 20 * (t ^ 2 * 2 ^ t) := by ring
    have c : t ^ 2 * 2 ^ t ≤ 2 * 2 ^ t * 2 ^ t := Nat.mul_le_mul_right _ hsq
    nlinarith
  nlinarith

end PEqualNP.MetaComplexity.Helpers
