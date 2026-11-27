import PEqualNP.Defs
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-! The Erdos-Littlewood-Offord bound (Erdos 1945): with `k` nonzero integer coefficients, a fixed
value of the 0/1 linear form is taken by at most `C(k, k/2)` points, so `count^2 * k ≤ 4^k`.
Proof: flip the coordinates with negative coefficient, observe the solution set is an antichain,
apply Sperner, then bound the central binomial coefficient. -/

namespace PEqualNP.Search.Helpers.Width

/-- `centralBinom n ^ 2 * (2n+1) ≤ 16^n`. -/
theorem lo_centralBinom_sq_le (n : ℕ) :
    n.centralBinom ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrec := Nat.succ_mul_centralBinom_succ n
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have key : (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1))
        = 4 * (2 * n + 1) * (2 * n + 3) * (n.centralBinom ^ 2 * (2 * n + 1)) := by
      have : (n + 1) ^ 2 * (n + 1).centralBinom ^ 2
          = (2 * (2 * n + 1) * n.centralBinom) ^ 2 := by
        rw [← hrec]; ring
      calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (2 * (n + 1) + 1))
          = ((n + 1) ^ 2 * (n + 1).centralBinom ^ 2) * (2 * n + 3) := by ring
        _ = _ := by rw [this]; ring
    rw [key]
    calc 4 * (2 * n + 1) * (2 * n + 3) * (n.centralBinom ^ 2 * (2 * n + 1))
        ≤ 4 * (2 * n + 1) * (2 * n + 3) * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := by
          apply Nat.mul_le_mul_right; nlinarith
      _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring

/-- `C(k, k/2)^2 * k ≤ 4^k`. -/
theorem lo_choose_half_sq_le (k : ℕ) : (k.choose (k / 2)) ^ 2 * k ≤ 4 ^ k := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h2 : 2 * n / 2 = n := by omega
    rw [h2, ← Nat.centralBinom_eq_two_mul_choose]
    have := lo_centralBinom_sq_le n
    have h16 : (4 : ℕ) ^ (2 * n) = 16 ^ n := by rw [pow_mul]; norm_num
    rw [h16]
    calc n.centralBinom ^ 2 * (2 * n) ≤ n.centralBinom ^ 2 * (2 * n + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := this
  · have h2 : (2 * n + 1) / 2 = n := by omega
    rw [h2]
    have hc : (n + 1).centralBinom = 2 * (2 * n + 1).choose n := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      rw [this, Nat.choose_succ_succ', Nat.choose_symm_half]; ring
    have := lo_centralBinom_sq_le (n + 1)
    rw [hc] at this
    have h16 : (16 : ℕ) ^ (n + 1) = 4 * 4 ^ (2 * n + 1) := by
      rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul]; ring
    rw [h16] at this
    have h' : 4 * ((2 * n + 1).choose n ^ 2 * (2 * n + 1)) ≤ 4 * 4 ^ (2 * n + 1) := by
      calc 4 * ((2 * n + 1).choose n ^ 2 * (2 * n + 1))
          ≤ (2 * (2 * n + 1).choose n) ^ 2 * (2 * (n + 1) + 1) := by
            have : (2 * (2 * n + 1).choose n) ^ 2 = 4 * (2 * n + 1).choose n ^ 2 := by ring
            rw [this, mul_assoc]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
        _ ≤ _ := this
    omega

/-- Erdos-Littlewood-Offord: with `k` nonzero integer coefficients, a fixed value is taken by at
most `C(k, k/2)` of the `2^k` 0/1 points; in squared form, `count^2 * k ≤ 4^k`. -/
theorem lo_bound (k : ℕ) (a : Fin k → ℤ) (ha : ∀ j, a j ≠ 0) (c : ℤ) :
    (Finset.univ.filter fun y : Fin k → Bool =>
      (∑ j, a j * (if y j then 1 else 0)) = c).card ^ 2 * k ≤ 4 ^ k := by
  classical
  set S := Finset.univ.filter fun y : Fin k → Bool =>
      (∑ j, a j * (if y j then 1 else 0)) = c with hS
  -- the flipped support
  let sOf : (Fin k → Bool) → Finset (Fin k) := fun y =>
    Finset.univ.filter fun j => (y j = true) ≠ (a j < 0)
  have hinj : Set.InjOn sOf S := by
    intro y _ y' _ h
    funext j
    have hj : j ∈ sOf y ↔ j ∈ sOf y' := by rw [h]
    simp only [sOf, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    cases hy : y j <;> cases hy' : y' j <;> simp_all
    all_goals (by_cases h1 : a j < 0 <;> simp_all <;> omega)
  -- the linear form rewritten through the flipped support
  have hform : ∀ y : Fin k → Bool,
      (∑ j, a j * (if y j then 1 else 0))
        = (∑ j ∈ sOf y, |a j|) + ∑ j, (if a j < 0 then a j else 0) := by
    intro y
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hneg : a j < 0
    · rw [abs_of_neg hneg]
      cases y j <;> simp [hneg]
    · rw [abs_of_nonneg (not_lt.mp hneg)]
      cases y j <;> simp [hneg]
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (S.image sOf)) := by
    intro s hs t ht hne hst
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs ht
    obtain ⟨y, hy, rfl⟩ := hs
    obtain ⟨y', hy', rfl⟩ := ht
    have e1 := (Finset.mem_filter.mp hy).2
    have e2 := (Finset.mem_filter.mp hy').2
    rw [hform] at e1 e2
    have heq : (∑ j ∈ sOf y, |a j|) = ∑ j ∈ sOf y', |a j| := by linarith
    have hssub : sOf y ⊂ sOf y' := Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩
    obtain ⟨i, hi, hni⟩ := Finset.exists_of_ssubset hssub
    have hlt : (∑ j ∈ sOf y, |a j|) < ∑ j ∈ sOf y', |a j| :=
      Finset.sum_lt_sum_of_subset hst hi hni (abs_pos.mpr (ha i))
        (fun j _ _ => abs_nonneg (a j))
    linarith
  have hsp := hanti.sperner
  rw [Fintype.card_fin, Finset.card_image_of_injOn hinj] at hsp
  calc S.card ^ 2 * k ≤ (k.choose (k / 2)) ^ 2 * k :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsp 2)
    _ ≤ 4 ^ k := lo_choose_half_sq_le k

end PEqualNP.Search.Helpers.Width
