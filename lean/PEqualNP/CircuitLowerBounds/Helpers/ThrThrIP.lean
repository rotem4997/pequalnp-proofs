import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.Helpers.ThresholdTop

/-!
# Inner product against depth-two threshold circuits, given a top weight normalization

`ip_thrthr_gate_bound_of` takes a bound `B s` on the total weight needed by a threshold gate
on `s` inputs, and turns the top weight bound of `ThresholdTop.lean` into a bound on the number
of bottom gates of a depth-two threshold circuit family for inner product.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open Finset

/-- Counting the indices below `n` that satisfy `p`, as a list and as a finset of `Fin n`. -/
theorem range_filter_length_eq_card (n : ℕ) (p : ℕ → Bool) :
    ((List.range n).filter p).length =
      (Finset.univ.filter (fun i : Fin n => p i.val = true)).card := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.card_filter,
      Finset.card_filter, Fin.sum_univ_castSucc]
    by_cases h : p m = true
    · simp [h]
    · simp [h]

/-- The concatenation of two inputs of length `n`, as an input of length `2 * n`. -/
def joinBits (n : ℕ) (y z : Fin n → Bool) : Fin (2 * n) → Bool :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩ else z ⟨i.val - n, by omega⟩

theorem joinBits_ip (n : ℕ) (y z : Fin n → Bool) :
    ((List.range ((List.ofFn (joinBits n y z)).length / 2)).filter
        (fun i => (List.ofFn (joinBits n y z)).getD i false &&
          (List.ofFn (joinBits n y z)).getD (i + (List.ofFn (joinBits n y z)).length / 2)
            false)).length =
      (Finset.univ.filter (fun i : Fin n => y i = true ∧ z i = true)).card := by
  have hl : (List.ofFn (joinBits n y z)).length / 2 = n := by
    rw [List.length_ofFn]; omega
  rw [hl, range_filter_length_eq_card]
  congr 1
  apply Finset.filter_congr
  intro i _
  have h1 : (List.ofFn (joinBits n y z)).getD i.val false = y i := by
    have hi : i.val < 2 * n := by omega
    simp [List.getD_eq_getElem?_getD, hi, joinBits]
  have h2 : (List.ofFn (joinBits n y z)).getD (i.val + n) false = z i := by
    have hi : i.val + n < 2 * n := by omega
    simp [List.getD_eq_getElem?_getD, hi, joinBits]
  rw [h1, h2, Bool.and_eq_true]

theorem joinBits_sum (n : ℕ) (y z : Fin n → Bool) (w : Fin (2 * n) → ℤ) :
    ∑ i : Fin (2 * n), w i * (if joinBits n y z i = true then 1 else 0) =
      (∑ i : Fin n, w ⟨i.val, by omega⟩ * (if y i = true then 1 else 0)) +
        ∑ i : Fin n, w ⟨n + i.val, by omega⟩ * (if z i = true then 1 else 0) := by
  have h : n + n = 2 * n := by omega
  rw [← Equiv.sum_comp (finCongr h)
    (fun i : Fin (2 * n) => w i * (if joinBits n y z i = true then 1 else 0)),
    Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have e : finCongr h (Fin.castAdd n i) = ⟨i.val, by omega⟩ := Fin.ext (by simp)
    rw [e]
    simp [joinBits]
  · apply Finset.sum_congr rfl
    intro i _
    have e : finCongr h (Fin.natAdd n i) = ⟨n + i.val, by omega⟩ :=
      Fin.ext (by simp [Nat.add_comm])
    rw [e]
    simp [joinBits]

theorem ip_thrthr_gate_bound_of (B : ℕ → ℤ)
    (hB : ∀ (s : ℕ) (c : Fin s → ℤ) (t0 : ℤ), ∃ (c' : Fin s → ℤ) (t0' : ℤ),
      (∑ j : Fin s, |c' j| ≤ B s) ∧ ∀ g : Fin s → Bool,
        (t0 ≤ ∑ j : Fin s, c j * (if g j = true then 1 else 0)) ↔
          (t0' ≤ ∑ j : Fin s, c' j * (if g j = true then 1 else 0)))
    (hmono : ∀ k l : ℕ, k ≤ l → B k ≤ B l) :
    ∀ s : ℕ → ℕ,
      ({x : List Bool | ((List.range (x.length / 2)).filter
        (fun i => x.getD i false && x.getD (i + x.length / 2) false)).length % 2 = 1} :
          Language Bool) ∈ PEqualNP.CircuitLowerBounds.THRTHR s →
      ∀ n : ℕ, 0 < n → (2 : ℤ) ^ n ≤ (2 * B (s (2 * n)) * ((n : ℤ) + 2)) ^ 2 := by
  intro s hL n hn
  obtain ⟨k, w, t, a, t0, hk, hx⟩ := hL (2 * n)
  obtain ⟨c', t0', hc', hg⟩ := hB k a t0
  have key := ip_top_weight_bound n k c' t0'
    (fun j y => ∑ i : Fin n, w j ⟨i.val, by omega⟩ * (if y i = true then 1 else 0))
    (fun j z => ∑ i : Fin n, w j ⟨n + i.val, by omega⟩ * (if z i = true then 1 else 0))
    t hn (by
      intro y z
      have h1 := hx (joinBits n y z)
      have h2 := hg (fun j => decide (t j ≤
        ∑ i : Fin (2 * n), w j i * (if joinBits n y z i = true then 1 else 0)))
      simp only [decide_eq_true_eq, joinBits_sum] at h2
      simp only [joinBits_sum] at h1
      rw [← h2, ← h1, ← joinBits_ip n y z]
      rfl)
  have h0 : (0 : ℤ) ≤ ∑ j : Fin k, |c' j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hle : (∑ j : Fin k, |c' j|) ≤ B (s (2 * n)) := le_trans hc' (hmono _ _ hk)
  refine le_trans key ?_
  have hn2 : (0 : ℤ) ≤ (n : ℤ) + 2 := by positivity
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_right _ hn2
  linarith

end PEqualNP.CircuitLowerBounds.Helpers
