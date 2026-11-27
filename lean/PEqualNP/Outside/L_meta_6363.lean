import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6363 : ∀ (x1 : List ℕ) (x2 : ℕ), ∃ (x3 : ℕ), x2 &&& x3 = x2 ∧ (∀ x4 ∈ x1, x4 &&& x3 = x4) ∧ ∀ (x4 : ℕ), ∃ (x5 : ℕ), x3.testBit x5 = Bool.true ∧ x2.testBit x5 = x2.testBit x4 ∧ ∀ x6 ∈ x1, x6.testBit x5 = x6.testBit x4 := by
  intro L a
  have hmemle : ∀ (M : List ℕ) (x : ℕ), x ∈ M → x ≤ M.sum := by
    intro M
    induction M with
    | nil => intro x hx; simp at hx
    | cons y t ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | h
      · simp
      · have := ih x h
        simp
        omega
  have hpow : ∀ n i : ℕ, n ≤ i → n < 2 ^ i := by
    intro n i hni
    calc n < 2 ^ n := Nat.lt_two_pow_self
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hni
  have hlt : ∀ n, n ≤ a + L.sum → ∀ i, a + L.sum ≤ i → n.testBit i = false := by
    intro n hn i hi
    exact Nat.testBit_eq_false_of_lt (hpow n i (by omega))
  have hand : ∀ n, n ≤ a + L.sum → n &&& (2 ^ (a + L.sum + 1) - 1) = n := by
    intro n hn
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hpow n _ (by omega))]
  refine ⟨2 ^ (a + L.sum + 1) - 1, hand a (by omega),
    fun x hx => hand x (by have := hmemle L x hx; omega), fun i => ?_⟩
  by_cases hi : i < a + L.sum + 1
  · exact ⟨i, by simp [Nat.testBit_two_pow_sub_one, hi], rfl, fun x _ => rfl⟩
  · refine ⟨a + L.sum, by simp [Nat.testBit_two_pow_sub_one], ?_, fun x hx => ?_⟩
    · rw [hlt a (by omega) _ (le_refl _), hlt a (by omega) i (by omega)]
    · have := hmemle L x hx
      rw [hlt x (by omega) _ (le_refl _), hlt x (by omega) i (by omega)]
