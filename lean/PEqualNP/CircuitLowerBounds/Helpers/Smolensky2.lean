import Mathlib

/-!
# The numbers behind the Razborov and Smolensky bound

Helper module (proofs only, no statement may use it). An upper bound on the central binomial
coefficient, the resulting bound on the number of subsets of size at most `n / 2 + D` at an odd
`n`, and the choice of the parameters: for a polynomial size bound and a fixed depth there are
an input length and an error parameter at which the two bounds contradict each other.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

theorem centralBinom_sq_mul_le (m : ℕ) : (Nat.centralBinom m) ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrec := Nat.succ_mul_centralBinom_succ m
    have h : (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      calc (m + 1) ^ 2 * ((Nat.centralBinom (m + 1)) ^ 2 * (2 * (m + 1) + 1))
          = ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 * (2 * m + 3) := by ring
        _ = (2 * (2 * m + 1) * Nat.centralBinom m) ^ 2 * (2 * m + 3) := by rw [hrec]
        _ = ((Nat.centralBinom m) ^ 2 * (2 * m + 1)) * (4 * (2 * m + 1) * (2 * m + 3)) := by ring
        _ ≤ 16 ^ m * (4 * (2 * m + 1) * (2 * m + 3)) := Nat.mul_le_mul_right _ ih
        _ ≤ 16 ^ m * (16 * (m + 1) ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left h (by positivity)

theorem sum_choose_le (m D : ℕ) :
    ∑ i ∈ Finset.range (m + D + 1), (2 * m + 1).choose i ≤
      4 ^ m + D * Nat.centralBinom (m + 1) := by
  induction D with
  | zero => simp [Nat.sum_range_choose_halfway]
  | succ D ih =>
    have h1 : (2 * m + 1).choose (m + D + 1) ≤ Nat.centralBinom (m + 1) := by
      have h2 := Nat.choose_le_middle (m + D + 1) (2 * m + 1)
      have h3 : (2 * m + 1) / 2 = m := by omega
      rw [h3] at h2
      have h4 : Nat.centralBinom (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := by
        rw [Nat.centralBinom, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.choose_succ_succ]
      omega
    rw [show m + (D + 1) + 1 = (m + D + 1) + 1 by ring, Finset.sum_range_succ]
    calc _ ≤ 4 ^ m + D * Nat.centralBinom (m + 1) + Nat.centralBinom (m + 1) :=
          Nat.add_le_add ih h1
      _ = _ := by ring

theorem poly_eval_le (P : Polynomial ℕ) (N : ℕ) (hN : 1 ≤ N) :
    P.eval N ≤ P.eval 1 * N ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN (by
    have := Finset.mem_range.mp hi
    omega))

theorem exists_pow_lt_two_pow (c t : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ c * k ^ t < 2 ^ k := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt t (r := (2 : ℝ)) (by norm_num)
  have hpos : (0 : ℝ) < 1 / ((c : ℝ) + 1) := by positivity
  obtain ⟨k, hk, hk1⟩ := ((h.eventually (gt_mem_nhds hpos)).and
    (Filter.eventually_ge_atTop 1)).exists
  refine ⟨k, hk1, ?_⟩
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hk
  have h2 : ((c : ℝ)) * (k : ℝ) ^ t < 2 ^ k := by
    have : (0 : ℝ) ≤ (k : ℝ) ^ t := by positivity
    nlinarith
  exact_mod_cast h2

/-- The choice of parameters: an odd input length `2 * m + 1` (plus `q` padding inputs) and an
error parameter `l`, at which the size bound `P` is beaten by `2 ^ l` and the degree
`((p - 1) * l) ^ d` is small against the square root of the input length. -/
theorem exists_params (P : Polynomial ℕ) (p q d : ℕ) :
    ∃ m l : ℕ, 1 ≤ l ∧ 4 * q * P.eval (2 * m + 1 + q) * 2 ^ q ≤ 2 ^ l ∧
      64 * (((p - 1) * l) ^ d) ^ 2 < 2 * m + 3 := by
  set e := P.natDegree with he
  set c := P.eval 1 with hc
  set B := 2 + 2 * q + c + (q + 2) * e with hB
  set M := (p - 1) * (e + B) with hM
  obtain ⟨k, hk1, hk⟩ := exists_pow_lt_two_pow (64 * M ^ (2 * d)) (2 * d)
  refine ⟨2 ^ k, e * k + B, by omega, ?_, ?_⟩
  · have hN : 2 * 2 ^ k + 1 + q ≤ 2 ^ (k + q + 2) := by
      have h1 : q < 2 ^ q := Nat.lt_two_pow_self
      have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h3 : 2 ^ (k + q + 2) = 4 * (2 ^ k * 2 ^ q) := by ring
      nlinarith
    have hs : P.eval (2 * 2 ^ k + 1 + q) ≤ 2 ^ c * 2 ^ ((k + q + 2) * e) := by
      refine (poly_eval_le P _ (by omega)).trans ?_
      refine Nat.mul_le_mul Nat.lt_two_pow_self.le ?_
      rw [pow_mul]
      exact Nat.pow_le_pow_left hN _
    have hq : q ≤ 2 ^ q := Nat.lt_two_pow_self.le
    calc 4 * q * P.eval (2 * 2 ^ k + 1 + q) * 2 ^ q
        ≤ 4 * 2 ^ q * (2 ^ c * 2 ^ ((k + q + 2) * e)) * 2 ^ q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) hs)
      _ = 2 ^ (e * k + B) := by
          rw [hB]
          ring
  · have hl : (p - 1) * (e * k + B) ≤ M * k := by
      rw [hM, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      nlinarith
    calc 64 * (((p - 1) * (e * k + B)) ^ d) ^ 2
        ≤ 64 * ((M * k) ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_le_pow_left hl _) _)
      _ = 64 * M ^ (2 * d) * k ^ (2 * d) := by ring
      _ < 2 ^ k := hk
      _ ≤ 2 * 2 ^ k + 3 := by omega

end PEqualNP.CircuitLowerBounds.Helpers
