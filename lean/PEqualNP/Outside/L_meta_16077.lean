import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16077_aux

theorem inv (r : ℕ → ℕ) (K e : ℕ) (he : 1 ≤ e)
    (h : ∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) :
    ∀ j : ℕ, j * 2 ^ (K + j) + 2 * e ≤ 2 * e * r (K + j) + 2 * e * 2 ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := h (K + j) (Nat.le_add_right K j)
    have hq : 2 ^ (K + j) < e * (2 ^ (K + j) / e) + e := by
      have h1 := Nat.div_add_mod (2 ^ (K + j)) e
      have h2 := Nat.mod_lt (2 ^ (K + j)) (show e > 0 by omega)
      linarith
    have hm : e * (2 * r (K + j) + 2 ^ (K + j) / e) ≤ e * r (K + j + 1) :=
      Nat.mul_le_mul_left e hs
    have e1 : 2 ^ (K + (j + 1)) = 2 * 2 ^ (K + j) := by
      rw [← Nat.add_assoc, pow_succ]; ring
    have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    rw [e1, e2, ← Nat.add_assoc]
    nlinarith

end PEqualNP.Outside.L_meta_16077_aux

theorem PEqualNP.Outside.L_meta_16077 : ∀ (r : ℕ → ℕ) (K e : ℕ), 1 ≤ e → (∀ k : ℕ, K ≤ k → 2 * r k + 2 ^ k / e ≤ r (k + 1)) → ∀ d : ℕ, 1 ≤ d → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := by
  intro r K e he h d hd
  refine ⟨K + (12 * e + 1), fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = K + j := ⟨k - K, by omega⟩
  have hI := PEqualNP.Outside.L_meta_16077_aux.inv r K e he h j
  have hj : 12 * e + 1 ≤ j := by omega
  have hp : 2 ^ j ≤ 2 ^ (K + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq : e * 2 ^ j ≤ e * 2 ^ (K + j) := Nat.mul_le_mul_left e hp
  have hdv : 2 ^ (K + j) / d ≤ 2 ^ (K + j) := Nat.div_le_self _ _
  have h1 : (12 * e + 1) * 2 ^ (K + j) ≤ j * 2 ^ (K + j) := Nat.mul_le_mul_right _ hj
  have h2 : (2 * e) * (5 * 2 ^ (K + j)) < (2 * e) * r (K + j) := by nlinarith
  have h3 := Nat.lt_of_mul_lt_mul_left h2
  linarith
