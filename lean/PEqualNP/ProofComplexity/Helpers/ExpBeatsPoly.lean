import Mathlib

namespace PEqualNP.ProofComplexity.Helpers

/-- A polynomial with natural coefficients is bounded by its coefficient sum times the
top power, at every argument that is at least one. -/
theorem poly_eval_le_coeffSum_mul_pow (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hi')

/-- The fourth power is below the power of two from sixteen on. -/
theorem pow_four_le_two_pow (l : ℕ) (hl : 16 ≤ l) : l ^ 4 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 16 * n ≤ n ^ 2 := by nlinarith
    have h3 : 16 * n ^ 2 ≤ n ^ 3 := by nlinarith
    have h4 : 16 * n ^ 3 ≤ n ^ 4 := by nlinarith
    have : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
      have e : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
      rw [e]; omega
    calc (n + 1) ^ 4 ≤ 2 * n ^ 4 := this
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

/-- The exponential bound of the bit pigeonhole size theorem eventually exceeds any
polynomial in the number of pigeons. -/
theorem exists_exp_beats_poly (p : Polynomial ℕ) :
    ∃ l : ℕ, 32 ≤ l ∧
      ((p.eval (2 ^ l) : ℕ) : ℝ) ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) := by
  set d := p.natDegree with hd
  set C := ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i with hC
  set K := C + d + 1 with hK
  obtain ⟨l, hl⟩ : ∃ l : ℕ, l = 32768 * K := ⟨_, rfl⟩
  refine ⟨l, by omega, ?_⟩
  have hl16 : 16 ≤ l := by omega
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    have : 0 < l := by omega
    exact_mod_cast this
  have hpoly : ((p.eval (2 ^ l) : ℕ) : ℝ) ≤ (C : ℝ) * ((2 : ℝ) ^ l) ^ d := by
    have := poly_eval_le_coeffSum_mul_pow p (2 ^ l) Nat.one_le_two_pow
    exact_mod_cast this
  have hpow : ((l : ℝ)) ^ 4 ≤ (2 : ℝ) ^ l := by
    have := pow_four_le_two_pow l hl16
    exact_mod_cast this
  have hCexp : (C : ℝ) ≤ Real.exp (C : ℝ) := by
    have := Real.add_one_le_exp (C : ℝ)
    linarith
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpd : ((2 : ℝ) ^ l) ^ d ≤ Real.exp ((l : ℝ) * (d : ℝ)) := by
    rw [← pow_mul]
    have e : Real.exp ((l : ℝ) * (d : ℝ)) = Real.exp 1 ^ (l * d) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) h2exp _
  have hlK : (l : ℝ) = 32768 * (K : ℝ) := by rw [hl]; push_cast; ring
  have hKreal : (K : ℝ) = (C : ℝ) + (d : ℝ) + 1 := by rw [hK]; push_cast; ring
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by
    have : 1 ≤ l := by omega
    exact_mod_cast this
  have hexpo : (C : ℝ) + (l : ℝ) * (d : ℝ) ≤ (2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (C : ℝ) + (l : ℝ) * (d : ℝ) ≤ (l : ℝ) * (K : ℝ) := by
      rw [hKreal]
      have := mul_le_mul_of_nonneg_right hl1 hCnn
      linarith
    have h2 : (l : ℝ) * (K : ℝ) * (32768 * (l : ℝ) ^ 2) = (l : ℝ) ^ 4 := by
      linear_combination (-(l : ℝ) ^ 3) * hlK
    calc ((C : ℝ) + (l : ℝ) * (d : ℝ)) * (32768 * (l : ℝ) ^ 2)
        ≤ (l : ℝ) * (K : ℝ) * (32768 * (l : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (l : ℝ) ^ 4 := h2
      _ ≤ (2 : ℝ) ^ l := hpow
  calc ((p.eval (2 ^ l) : ℕ) : ℝ) ≤ (C : ℝ) * ((2 : ℝ) ^ l) ^ d := hpoly
    _ ≤ Real.exp (C : ℝ) * Real.exp ((l : ℝ) * (d : ℝ)) :=
        mul_le_mul hCexp hpd (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((C : ℝ) + (l : ℝ) * (d : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) := Real.exp_le_exp.mpr hexpo

end PEqualNP.ProofComplexity.Helpers
