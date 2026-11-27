import PEqualNP.Library.Evasion.Plan
import PEqualNP.Library.L088

/-!
# The padding form of the time hierarchy, from its pieces

Note 210 of the evasion route, item 3.9, with `p' := P`, `q := Q`; the scaled family of
inclusions (item 3.5) is the hypothesis of `StmtNoScaledCollapse`. The pieces T5b (patch), T5d,
T5e, CLK and item 3.1 are taken as hypotheses; the hierarchy is the checked L-lib-088.
-/

namespace PEqualNP.Library.Evasion

theorem noScaledCollapse_of_pieces :
    StmtT5b → StmtT5d → StmtT5e → StmtCLK → StmtDtimeoO → StmtNoScaledCollapse := by
  intro hT5b hT5d hT5e hCLK hO P Q hP hPQ hscale
  obtain ⟨k, hk⟩ := PEqualNP.Library.L088
  obtain ⟨C0, hpatch⟩ := hT5b
  obtain ⟨i, hi⟩ := hT5d P Q hPQ k
  have hA : 1 ≤ P ^ i := Nat.one_le_pow _ _ hP
  set A := P ^ i with hAdef
  set t : ℕ → ℕ := fun m => (C0 + 1) * 2 ^ (2 * A * m) + (C0 + 1) with ht
  obtain ⟨_, hlin, hclk⟩ := hCLK (2 * A) (C0 + 1) (by omega) (by omega)
  obtain ⟨L, ⟨c1, h1⟩, h2⟩ := hk t hlin hclk
  -- step (4): L in DTIMEO (2^(Q^i * 1 * m))
  have hL1 : L ∈ DTIMEO (fun n => t n ^ k) := ⟨c1, h1⟩
  have hbound : ∀ n, t n ^ k ≤ (2 * C0 + 2) ^ k * 2 ^ (Q ^ i * 1 * n) +
      (2 * C0 + 2) ^ k := by
    intro n
    have hx : 1 ≤ 2 ^ (2 * A * n) := Nat.one_le_two_pow
    have h1' : t n ≤ (2 * C0 + 2) * 2 ^ (2 * A * n) := by
      simp only [ht]; nlinarith
    have h2' : t n ^ k ≤ (2 * C0 + 2) ^ k * 2 ^ (2 * A * n * k) := by
      calc t n ^ k ≤ ((2 * C0 + 2) * 2 ^ (2 * A * n)) ^ k := Nat.pow_le_pow_left h1' k
        _ = (2 * C0 + 2) ^ k * 2 ^ (2 * A * n * k) := by rw [mul_pow, ← pow_mul]
    have hexp : 2 * A * n * k ≤ Q ^ i * 1 * n := by
      have : 2 * A * n * k = (2 * k * P ^ i) * n := by rw [hAdef]; ring
      rw [this, mul_one]
      exact Nat.mul_le_mul_right n hi
    have h3' : 2 ^ (2 * A * n * k) ≤ 2 ^ (Q ^ i * 1 * n) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    calc t n ^ k ≤ (2 * C0 + 2) ^ k * 2 ^ (2 * A * n * k) := h2'
      _ ≤ (2 * C0 + 2) ^ k * 2 ^ (Q ^ i * 1 * n) := Nat.mul_le_mul_left _ h3'
      _ ≤ _ := Nat.le_add_right _ _
  have hL2 : L ∈ DTIMEO (fun m => 2 ^ (Q ^ i * 1 * m)) := hO _ _ _ hbound hL1
  -- step (5): T5e at r = 1
  have hL3 : L ∈ DTIMEO (fun m => 2 ^ (P ^ i * 1 * m)) :=
    hT5e P Q hP hPQ hscale i 1 le_rfl hL2
  obtain ⟨K, hK⟩ := hL3
  -- step (6): the patch
  apply h2
  refine hpatch L (fun m => 2 ^ (P ^ i * 1 * m)) t K hK ⟨2 * K + 3, ?_⟩ ?_
  · intro n hn
    have hnX : n < 2 ^ (A * n) := by
      calc n < 2 ^ n := Nat.lt_two_pow_self
        _ ≤ 2 ^ (A * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hsq : 2 ^ (2 * A * n) = 2 ^ (A * n) * 2 ^ (A * n) := by
      rw [← pow_add]; congr 1; ring
    simp only [ht, hsq, ← hAdef, mul_one]
    set X := 2 ^ (A * n)
    nlinarith
  · intro n
    have hnX : n < 2 ^ (2 * A * n) := by
      calc n < 2 ^ n := Nat.lt_two_pow_self
        _ ≤ 2 ^ (2 * A * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    simp only [ht]
    nlinarith

end PEqualNP.Library.Evasion
