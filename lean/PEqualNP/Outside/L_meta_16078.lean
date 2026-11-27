import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16078_aux

theorem inv (r : ℕ → ℕ) (K e d : ℕ) (he : 1 ≤ e)
    (h : ∀ k : ℕ, K ≤ k → r k ≤ 4 * 2 ^ k + 2 ^ k / d → 2 * r k + 2 ^ k / e ≤ r (k + 1)) :
    ∀ j : ℕ, (∀ i : ℕ, i < j → r (K + i) ≤ 4 * 2 ^ (K + i) + 2 ^ (K + i) / d) →
      j * 2 ^ (K + j) + 2 * e ≤ 2 * e * r (K + j) + 2 * e * 2 ^ j := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih' := ih (fun i hi => hj i (by omega))
    have hs := h (K + j) (Nat.le_add_right K j) (hj j (by omega))
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

theorem divtwo (x d : ℕ) (hd : 1 ≤ d) : (2 * x) / d ≤ 2 * (x / d) + 1 := by
  have hd0 : 0 < d := by omega
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.mod_lt x hd0
  have h3 : (2 * x) / d < 2 * (x / d) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    nlinarith
  omega

end PEqualNP.Outside.L_meta_16078_aux

theorem PEqualNP.Outside.L_meta_16078 : ∀ (r : ℕ → ℕ) (K e d : ℕ), 1 ≤ e → 1 ≤ d → (∀ k : ℕ, K ≤ k → (r k ≤ 4 * 2 ^ k + 2 ^ k / d → 2 * r k + 2 ^ k / e ≤ r (k + 1)) ∧ (4 * 2 ^ k + 2 ^ k / d < r k → 2 * r k ≤ r (k + 1))) → ∃ K' : ℕ, ∀ k : ℕ, K' ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k := by
  intro r K e d he hd h
  have hpers : ∀ k : ℕ, K ≤ k → 4 * 2 ^ k + 2 ^ k / d < r k →
      4 * 2 ^ (k + 1) + 2 ^ (k + 1) / d < r (k + 1) := by
    intro k hk hlt
    have h1 := (h k hk).2 hlt
    have h2 := PEqualNP.Outside.L_meta_16078_aux.divtwo (2 ^ k) d hd
    have e1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    rw [e1]
    omega
  have hex : ∃ k0 : ℕ, K ≤ k0 ∧ 4 * 2 ^ k0 + 2 ^ k0 / d < r k0 := by
    by_cases hall : ∀ i : ℕ, i < 12 * e + 1 → r (K + i) ≤ 4 * 2 ^ (K + i) + 2 ^ (K + i) / d
    · refine ⟨K + (12 * e + 1), Nat.le_add_right _ _, ?_⟩
      have hI := PEqualNP.Outside.L_meta_16078_aux.inv r K e d he
        (fun k hk hle => (h k hk).1 hle) (12 * e + 1) hall
      set j := 12 * e + 1 with hjdef
      have hp : 2 ^ j ≤ 2 ^ (K + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hq : e * 2 ^ j ≤ e * 2 ^ (K + j) := Nat.mul_le_mul_left e hp
      have hdv : 2 ^ (K + j) / d ≤ 2 ^ (K + j) := Nat.div_le_self _ _
      have h1 : (12 * e + 1) * 2 ^ (K + j) ≤ j * 2 ^ (K + j) := le_of_eq (by rw [hjdef])
      have h2 : (2 * e) * (5 * 2 ^ (K + j)) < (2 * e) * r (K + j) := by nlinarith
      have h3 := Nat.lt_of_mul_lt_mul_left h2
      linarith
    · push_neg at hall
      obtain ⟨i, _, hi⟩ := hall
      exact ⟨K + i, Nat.le_add_right _ _, hi⟩
  obtain ⟨k0, hk0, hlt0⟩ := hex
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = k0 + m := ⟨k - k0, by omega⟩
  induction m with
  | zero => simpa using hlt0
  | succ m ih =>
    have := hpers (k0 + m) (by omega) (ih (by omega))
    simpa [Nat.add_assoc] using this
