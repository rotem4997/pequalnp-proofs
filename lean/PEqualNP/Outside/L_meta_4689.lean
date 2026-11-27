import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4689

lemma core (a b m s : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hs : s ≤ 4512) (hsum : a + b ≤ s + 1)
    (h : m * m ≤ b * (a * (a - 1) + m)) : m ≤ 24 * s := by
  by_contra hc0
  have hc : 24 * s < m := not_le.mp hc0
  have hM : 24 * (a + b) - 23 ≤ m := by linarith
  have h1 : (24 * (a + b) - 23) * (24 * (a + b) - 23 - b) ≤ m * (m - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hM)
      (show (0 : ℤ) ≤ m + (24 * (a + b) - 23) - b by linarith)]
  have hd : 0 ≤ (b - a) * (552 * (b - a) - 1081) + 529 := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ b - a - 1 by linarith)
        (show (0 : ℤ) ≤ 552 * (b - a) - 529 by linarith)]
  have hB : 1 ≤ a * (2257 - b) + 2233 * (b - a) - 2185 := by
    rcases le_or_gt b 2256 with hb | hb
    · rcases eq_or_lt_of_le hab with heq | hlt
      · subst heq
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ a - 1 by linarith)
          (show (0 : ℤ) ≤ 2256 - a by linarith)]
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ a by linarith)
          (show (0 : ℤ) ≤ 2257 - b by linarith)]
    · have he : 0 ≤ b - 2257 := by linarith
      have hg : 0 ≤ 4513 - a - b := by linarith
      nlinarith [mul_nonneg he he, mul_nonneg he hg]
  have hF : (24 * (a + b) - 23) * (24 * (a + b) - 23 - b) - a * b * (a - 1)
      = a * (a * (2257 - b) + 2233 * (b - a) - 2185)
        + ((b - a) * (552 * (b - a) - 1081) + 529) := by ring
  have h2 : m * (m - b) ≤ a * b * (a - 1) := by nlinarith
  have h3 : a * 1 ≤ a * (a * (2257 - b) + 2233 * (b - a) - 2185) :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  linarith

lemma nat_core (a b m s : ℕ) (hab : a ≤ b) (hs : s ≤ 4512) (hsum : a + 1 + (b + 1) ≤ s + 1)
    (h : m * m ≤ (b + 1) * ((a + 1) * a + m)) : m ≤ 24 * s := by
  have hz : (m : ℤ) * m ≤ ((b : ℤ) + 1) * (((a : ℤ) + 1) * (((a : ℤ) + 1) - 1) + m) := by
    have h' : ((m * m : ℕ) : ℤ) ≤ (((b + 1) * ((a + 1) * a + m) : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have := core ((a : ℤ) + 1) ((b : ℤ) + 1) m s (by have := Int.natCast_nonneg a; linarith) (by exact_mod_cast Nat.succ_le_succ hab)
    (by exact_mod_cast hs) (by exact_mod_cast hsum) hz
  exact_mod_cast this

end PEqualNP.Outside.L_meta_4689

theorem PEqualNP.Outside.L_meta_4689 : ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro s a b m hs hsum hm h1 h2
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp at hm
    omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp at hm
    omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hb)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h1 h2
  rcases le_total a b with hab | hab
  · exact PEqualNP.Outside.L_meta_4689.nat_core a b m s hab hs hsum h1
  · exact PEqualNP.Outside.L_meta_4689.nat_core b a m s hab hs (by omega) h2
