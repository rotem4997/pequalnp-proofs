import Mathlib
import PEqualNP.Defs

-- Take M = x2 + sum x1, so every number involved is at most M and has bit M clear, and let
-- x3 = 2^(M+1) - 1. A position at most M is its own witness; a larger one uses position M.

namespace PEqualNP.Outside.L_meta_7416

theorem bit_clear (n M k : ℕ) (h : n ≤ M) (hk : M ≤ k) : n.testBit k = false :=
  Nat.testBit_eq_false_of_lt (lt_of_le_of_lt h ((Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by norm_num) hk)))

theorem and_mask (n M : ℕ) (h : n ≤ M) : n &&& (2 ^ (M + 1) - 1) = n := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt h ((Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))

end PEqualNP.Outside.L_meta_7416

open PEqualNP.Outside.L_meta_7416 in
theorem PEqualNP.Outside.L_meta_7416 : ∀ (x1 : List ℕ) (x2 : ℕ), ∃ (x3 : ℕ), (∀ (x4 : ℕ), ∃ (x5 : ℕ), x3.testBit x5 = Bool.true ∧ x2.testBit x5 = x2.testBit x4 ∧ ∀ x6 ∈ x1, x6.testBit x5 = x6.testBit x4) ∧ (∀ x4 ∈ x1, x4 &&& x3 = x4) ∧ x2 &&& x3 = x2 := by
  intro x1 x2
  have hle : ∀ x6 ∈ x1, x6 ≤ x2 + x1.sum := fun x6 h => (List.le_sum_of_mem h).trans (by omega)
  have h2 : x2 ≤ x2 + x1.sum := by omega
  refine ⟨2 ^ (x2 + x1.sum + 1) - 1, ?_, ?_, ?_⟩
  · intro x4
    by_cases hx : x4 ≤ x2 + x1.sum
    · refine ⟨x4, ?_, rfl, fun _ _ => rfl⟩
      rw [Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true_eq]
      omega
    · refine ⟨x2 + x1.sum, ?_, ?_, ?_⟩
      · rw [Nat.testBit_two_pow_sub_one]
        simp
      · rw [bit_clear _ _ _ h2 le_rfl, bit_clear _ _ _ h2 (by omega)]
      · intro x6 hx6
        rw [bit_clear _ _ _ (hle x6 hx6) le_rfl, bit_clear _ _ _ (hle x6 hx6) (by omega)]
  · intro x4 hx4
    exact and_mask _ _ (hle x4 hx4)
  · exact and_mask _ _ h2
