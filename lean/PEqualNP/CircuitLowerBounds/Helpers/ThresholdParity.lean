import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-clb-014: parity as a threshold of thresholds.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

theorem altSum (n c : ℕ) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * (if ((j : ℤ) + 1) ≤ (c : ℤ) then 1 else 0)
      = ((min n c % 2 : ℕ) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : n < c
    · have h' : ((n : ℤ) + 1) ≤ (c : ℤ) := by exact_mod_cast h
      rw [if_pos h', min_eq_left (le_of_lt h), min_eq_left h]
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow]; have := Nat.even_iff.mp he; omega
      · rw [ho.neg_one_pow]; have := Nat.odd_iff.mp ho; omega
    · have h' : ¬ ((n : ℤ) + 1) ≤ (c : ℤ) := by intro h2; exact h (by exact_mod_cast h2)
      rw [if_neg h', min_eq_right (by omega), min_eq_right (by omega)]; simp

theorem count_ofFn (n : ℕ) (x : Fin n → Bool) :
    (((List.ofFn x).count true : ℕ) : ℤ) = ∑ i : Fin n, (1 : ℤ) * (if x i = true then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, Nat.cast_add, ih]
    cases x 0 <;> simp; ring

theorem parity_mem_THRTHR :
    ({x : List Bool | x.count true % 2 = 1} : Language Bool) ∈ THRTHR (fun n => n) := by
  intro n
  refine ⟨n, fun _ _ => 1, fun j => (j : ℤ) + 1, fun j => (-1) ^ (j : ℕ), 1, le_rfl, fun x => ?_⟩
  have hc := count_ofFn n x
  have hle : (List.ofFn x).count true ≤ n := by
    simpa using List.count_le_length (a := true) (l := List.ofFn x)
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (-1 : ℤ) ^ j * (if ((j : ℤ) + 1) ≤
      ∑ i : Fin n, (1 : ℤ) * (if x i = true then 1 else 0) then 1 else 0)) n,
    ← hc, altSum, min_eq_right hle]
  show (List.ofFn x).count true % 2 = 1 ↔ _
  omega

end PEqualNP.CircuitLowerBounds.Helpers
