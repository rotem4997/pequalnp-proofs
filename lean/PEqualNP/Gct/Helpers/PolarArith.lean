import Mathlib
import PEqualNP.Defs

/-!
Arithmetic behind L-gct-041: a weighted count inequality, valid for all test points `(p, q)`,
forces `(r - 1) * (h + 1) ≤ 11 * n`.

Three ranges of `2 * n` against `h + 1`:
* `2 * n ≤ h + 1`: the test point `(4 ^ (h + 1), 1)` contradicts the hypothesis;
* `2 * n = h + 2`: the test point `(h + 1, 1)` gives `(r - 1) * (h + 1) < 4 * n`;
* `2 * n = m + h + 2` with `1 ≤ m`: the test point `(h + 1, m)` and
  `(1 + x / m) ^ m ≤ exp x` give `(r - 1) * (h + 1) < 2 * e * (2 * n - 1)`.
-/

namespace PEqualNP.Gct.Helpers

/-- When `2 * n ≤ h + 1` the weighted count inequality fails at `(4 ^ (h + 1), 1)`. -/
theorem polar_small (h n K : ℕ) (hK : 1 ≤ K) (hn : 2 * n ≤ h + 1)
    (hyp : ∀ p q : ℕ, K * p ^ (h + 1) * q ^ (2 * n) * (p + q)
      ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) : False := by
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = 4 ^ (h + 1) := ⟨_, rfl⟩
  have key := hyp P 1
  simp only [one_pow, mul_one] at key
  have hPpos : 0 < P := by rw [hP]; positivity
  have h1 : (P + 1) ^ (2 * n) ≤ (P + 1) ^ (h + 1) := Nat.pow_le_pow_right (by omega) hn
  have h2 : P ^ (h + 1) * (P + 1) ≤ K * P ^ (h + 1) * (P + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hK)
  have h3 : P ^ (h + 1) * (P + 1) ≤ 2 ^ h * (P + 1) ^ h * (P + 1) := by
    calc P ^ (h + 1) * (P + 1) ≤ K * P ^ (h + 1) * (P + 1) := h2
      _ ≤ 2 ^ h * (P + 1) ^ (2 * n) := key
      _ ≤ 2 ^ h * (P + 1) ^ (h + 1) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ h * (P + 1) ^ h * (P + 1) := by ring
  have h4 : P ^ (h + 1) ≤ 2 ^ h * (P + 1) ^ h :=
    Nat.le_of_mul_le_mul_right h3 (by omega)
  have h5 : 2 ^ h * (P + 1) ^ h ≤ 4 ^ h * P ^ h := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) h
  have h6 : 4 ^ h * P ^ h < P ^ (h + 1) := by
    have h7 : 4 ^ h < P := by
      rw [hP]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h8 : 0 < P ^ h := by positivity
    calc 4 ^ h * P ^ h < P * P ^ h := mul_lt_mul_of_pos_right h7 h8
      _ = P ^ (h + 1) := by ring
  omega

/-- The real estimate: the optimal test point and `(1 + x / m) ^ m ≤ exp x`. -/
theorem polar_real (h m a n : ℕ) (hm : 1 ≤ m) (hn : 2 * n = m + h + 2)
    (key : (a * (h + 1)) ^ (h + 1) * m ^ m
      ≤ 2 ^ h * (h + 1 + m) ^ (h + 1) * (h + 1 + m) ^ m) :
    a * (h + 1) ≤ 11 * n := by
  by_contra hcon
  push_neg at hcon
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (h : ℝ) + 1 + m := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp 1 := ⟨_, rfl⟩
  have keyR : ((a : ℝ) * (h + 1)) ^ (h + 1) * (m : ℝ) ^ m
      ≤ 2 ^ h * S ^ (h + 1) * S ^ m := by
    rw [hS]; exact_mod_cast key
  have hSpos : 0 < S := by rw [hS]; positivity
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos 1
  have hE9 : E < 2.7182818286 := by rw [hE]; exact Real.exp_one_lt_d9
  have e1 : S ≤ m * Real.exp (((h : ℝ) + 1) / m) := by
    have h1 := Real.add_one_le_exp (((h : ℝ) + 1) / m)
    have h2 : S = m * (((h : ℝ) + 1) / m + 1) := by rw [hS]; field_simp
    rw [h2]; exact mul_le_mul_of_nonneg_left h1 hmR.le
  have e2 : S ^ m ≤ (m : ℝ) ^ m * E ^ (h + 1) := by
    calc S ^ m ≤ (m * Real.exp (((h : ℝ) + 1) / m)) ^ m := pow_le_pow_left₀ hSpos.le e1 m
      _ = (m : ℝ) ^ m * Real.exp ((m : ℝ) * (((h : ℝ) + 1) / m)) := by
        rw [mul_pow, Real.exp_nat_mul]
      _ = (m : ℝ) ^ m * Real.exp (((h + 1 : ℕ) : ℝ) * 1) := by
        congr 2; push_cast; field_simp
      _ = (m : ℝ) ^ m * E ^ (h + 1) := by rw [Real.exp_nat_mul, hE]
  have e3 : ((a : ℝ) * (h + 1)) ^ (h + 1) * (m : ℝ) ^ m
      ≤ 2 ^ h * (S * E) ^ (h + 1) * (m : ℝ) ^ m := by
    calc ((a : ℝ) * (h + 1)) ^ (h + 1) * (m : ℝ) ^ m
        ≤ 2 ^ h * S ^ (h + 1) * S ^ m := keyR
      _ ≤ 2 ^ h * S ^ (h + 1) * ((m : ℝ) ^ m * E ^ (h + 1)) :=
        mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = 2 ^ h * (S * E) ^ (h + 1) * (m : ℝ) ^ m := by ring
  have e4 : ((a : ℝ) * (h + 1)) ^ (h + 1) ≤ 2 ^ h * (S * E) ^ (h + 1) :=
    le_of_mul_le_mul_right e3 (by positivity)
  have hnR : (2 : ℝ) * n = m + h + 2 := by exact_mod_cast hn
  have hconR : (11 : ℝ) * n + 1 ≤ a * (h + 1) := by exact_mod_cast hcon
  have e5 : 2 * (S * E) ≤ (a : ℝ) * (h + 1) := by
    have hS2 : S = 2 * n - 1 := by rw [hS]; linarith
    have hS1 : S * E ≤ S * 2.7182818286 := mul_le_mul_of_nonneg_left hE9.le hSpos.le
    rw [hS2] at hS1
    rw [hS2]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have e6 : (2 * (S * E)) ^ (h + 1) ≤ ((a : ℝ) * (h + 1)) ^ (h + 1) :=
    pow_le_pow_left₀ (by positivity) e5 _
  have e7 : (2 * (S * E)) ^ (h + 1) = 2 * (2 ^ h * (S * E) ^ (h + 1)) := by ring
  have e8 : 0 < 2 ^ h * (S * E) ^ (h + 1) := by positivity
  linarith

/-- The weighted count inequality at all test points forces `(r - 1) * (h + 1) ≤ 11 * n`. -/
theorem polar_arith (h n r K : ℕ) (hr : 2 ≤ r) (hK : (r - 1) ^ (h + 1) ≤ K)
    (hyp : ∀ p q : ℕ, K * p ^ (h + 1) * q ^ (2 * n) * (p + q)
      ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) :
    (r - 1) * (h + 1) ≤ 11 * n := by
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hK ⊢
  have ha : 1 ≤ a := by omega
  have hK1 : 1 ≤ K := le_trans (Nat.one_le_pow _ _ ha) hK
  have h3 : (a * (h + 1)) ^ (h + 1) ≤ K * (h + 1) ^ (h + 1) := by
    rw [mul_pow]; exact Nat.mul_le_mul_right _ hK
  rcases Nat.lt_or_ge (h + 1) (2 * n) with hlt | hge
  · obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + h + 2 := ⟨2 * n - h - 2, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · have key := hyp (h + 1) 1
      rw [hm] at key
      simp only [one_pow, mul_one, zero_add] at key
      have k2 : K * (h + 1) ^ (h + 1) ≤ 2 ^ h * (h + 1 + 1) ^ (h + 1) := by
        apply Nat.le_of_mul_le_mul_right _ (show 0 < h + 1 + 1 by omega)
        calc K * (h + 1) ^ (h + 1) * (h + 1 + 1) ≤ 2 ^ h * (h + 1 + 1) ^ (h + 2) := key
          _ = 2 ^ h * (h + 1 + 1) ^ (h + 1) * (h + 1 + 1) := by ring
      by_contra hcon
      push_neg at hcon
      have h1 : 2 * (h + 1 + 1) ≤ a * (h + 1) := by linarith
      have h2 := Nat.pow_le_pow_left h1 (h + 1)
      have h4 : (2 * (h + 1 + 1)) ^ (h + 1) = 2 * (2 ^ h * (h + 1 + 1) ^ (h + 1)) := by
        rw [mul_pow, pow_succ 2 h]; generalize (h + 1 + 1) ^ (h + 1) = X; ring
      have h5 : 0 < 2 ^ h * (h + 1 + 1) ^ (h + 1) := by positivity
      linarith
    · have key := hyp (h + 1) m
      rw [hm] at key
      have k2 : K * (h + 1) ^ (h + 1) * m ^ m
          ≤ 2 ^ h * (h + 1 + m) ^ (h + 1) * (h + 1 + m) ^ m := by
        apply Nat.le_of_mul_le_mul_right _
          (show 0 < m ^ (h + 2) * (h + 1 + m) from
            Nat.mul_pos (Nat.pow_pos hmpos) (by omega))
        calc K * (h + 1) ^ (h + 1) * m ^ m * (m ^ (h + 2) * (h + 1 + m))
            = K * (h + 1) ^ (h + 1) * m ^ (m + h + 2) * (h + 1 + m) := by ring
          _ ≤ 2 ^ h * m ^ (h + 2) * (h + 1 + m) ^ (m + h + 2) := key
          _ = 2 ^ h * (h + 1 + m) ^ (h + 1) * (h + 1 + m) ^ m
                * (m ^ (h + 2) * (h + 1 + m)) := by ring
      apply polar_real h m a n hmpos hm
      calc (a * (h + 1)) ^ (h + 1) * m ^ m ≤ K * (h + 1) ^ (h + 1) * m ^ m :=
            Nat.mul_le_mul_right _ h3
        _ ≤ 2 ^ h * (h + 1 + m) ^ (h + 1) * (h + 1 + m) ^ m := k2
  · exact (polar_small h n K hK1 hge hyp).elim

end PEqualNP.Gct.Helpers
