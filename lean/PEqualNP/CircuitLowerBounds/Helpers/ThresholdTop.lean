import Mathlib
import PEqualNP.CircuitLowerBounds.Helpers.Discriminator
import PEqualNP.CircuitLowerBounds.Helpers.Staircase

/-!
Helper for L-clb-021: the staircase bound for one threshold gate of any weights, fed to the
discriminator lemma, bounds the total top weight of a depth-two threshold circuit for inner
product from below.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

theorem gate_stair_bound (n : ℕ) (a b : (Fin n → Bool) → ℤ) (t : ℤ) :
    |((∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      (if t ≤ a x + b y then ipSign n x y else 0) : ℤ) : ℝ)| ≤
      ((n + 1 : ℕ) : ℝ) * (Real.sqrt (2 ^ n)) ^ 3 := by
  have h := stairSum_bound n a b t n univ univ (by simp)
  have hc : ((univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by simp
  rw [hc] at h
  have hs : Real.sqrt ((2 : ℝ) ^ n * 2 ^ n * 2 ^ n) = (Real.sqrt (2 ^ n)) ^ 3 := by
    have h0 : (0 : ℝ) ≤ 2 ^ n := by positivity
    have : (2 : ℝ) ^ n * 2 ^ n * 2 ^ n = ((Real.sqrt (2 ^ n)) ^ 3) ^ 2 := by
      have := Real.sq_sqrt h0
      calc (2 : ℝ) ^ n * 2 ^ n * 2 ^ n
          = (Real.sqrt (2 ^ n) ^ 2) * (Real.sqrt (2 ^ n) ^ 2) * (Real.sqrt (2 ^ n) ^ 2) := by
            rw [this]
        _ = ((Real.sqrt (2 ^ n)) ^ 3) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hs] at h
  unfold stairSum at h
  push_cast
  push_cast at h
  exact h

theorem ip_top_weight_bound : ∀ (n m : ℕ) (c : Fin m → ℤ) (t0 : ℤ)
    (a b : Fin m → (Fin n → Bool) → ℤ) (t : Fin m → ℤ), 0 < n →
    (∀ x y : Fin n → Bool,
      (t0 ≤ ∑ j : Fin m, c j * (if t j ≤ a j x + b j y then 1 else 0)) ↔
        (Finset.univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card % 2 = 1) →
    (2 : ℤ) ^ n ≤ (2 * (∑ j : Fin m, |c j|) * ((n : ℤ) + 2)) ^ 2 := by
  intro n m c t0 a b t hn hip
  have h := ip_bound_of_gate_bound n m (n + 1) c t0 a b t hn hip
    (fun j => gate_stair_bound n (a j) (b j) (t j))
  have e : (((n + 1 : ℕ) : ℤ) + 1) = (n : ℤ) + 2 := by push_cast; ring
  rw [e] at h
  exact h

end PEqualNP.CircuitLowerBounds.Helpers
