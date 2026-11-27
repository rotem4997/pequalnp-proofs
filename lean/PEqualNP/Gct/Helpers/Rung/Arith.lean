import PEqualNP.Gct.Helpers.Rung.Statements

/-!
# The rung: the choice of parameters

Proof of the step statement `PEqualNP.Gct.Rung.Arith`: pure arithmetic of natural numbers.
A helper module; nothing here is a recorded lemma.
-/

namespace PEqualNP.Gct.Rung

theorem arith : Arith := by
  intro R M m0 r hr
  refine ⟨M + m0 + 2, by omega, ?_⟩
  set N := M + m0 + 2 with hN
  have hr48 : 48 ≤ r := by omega
  have hNM : M < N := by omega
  have hNm : m0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  -- p = r * N
  have hpN : N ≤ r * N := Nat.le_mul_of_pos_left N (by omega)
  have hpr : r ≤ r * N := Nat.le_mul_of_pos_right r (by omega)
  have e1 : 3 * r * N = 3 * (r * N) := by ring
  have e2 : N * (2 * r + r) = 3 * (r * N) := by ring
  rw [e1, e2]
  set p := r * N with hp
  have hA : 2 * p ≤ 3 * p - M := by omega
  have hm : 3 * p + 3 * p - r ≤ 6 * p := by omega
  -- d is large
  have hd : 2 * p * (r + 1) * N ≤ N * ((3 * p - M) * (r + 1)) := by
    calc 2 * p * (r + 1) * N = N * (2 * p * (r + 1)) := by ring
      _ ≤ N * ((3 * p - M) * (r + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hA)
  have hpp : 48 ≤ p := le_trans hr48 hpr
  have hbig : 2 * p * (r + 1) * N ≥ 2 * p * p := by
    have : p ≤ (r + 1) * N := by rw [hp]; nlinarith
    calc 2 * p * (r + 1) * N = 2 * p * ((r + 1) * N) := by ring
      _ ≥ 2 * p * p := Nat.mul_le_mul_left _ this
  refine ⟨by omega, by omega, by omega, by nlinarith, ?_⟩
  -- main inequality
  set d := N * ((3 * p - M) * (r + 1)) with hdd
  have hd1 : 2 * p * (r + 1) * N - 1 ≤ d - 1 := Nat.sub_le_sub_right hd 1
  have hR : 48 * R + 48 ≤ r := hr
  calc R * (3 * p + 3 * p - r) ^ 2 ≤ R * (6 * p) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 2)
    _ ≤ (r - 1) * (2 * p * (r + 1) * N - 1) := by
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        have h2 : 1 ≤ 2 * p * (s + 1 + 1) * N := by nlinarith
        have h3 : 2 * p * (s + 1 + 1) * N - 1 ≥ p * (s + 1 + 1) * N := by
          have : p * (s + 1 + 1) * N ≥ 1 := by nlinarith
          have e : 2 * p * (s + 1 + 1) * N = 2 * (p * (s + 1 + 1) * N) := by ring
          omega
        have h4 : p * (s + 1 + 1) * N ≥ p * p := by
          have : p ≤ (s + 1 + 1) * N := by rw [hp]; nlinarith
          calc p * (s + 1 + 1) * N = p * ((s + 1 + 1) * N) := by ring
            _ ≥ p * p := Nat.mul_le_mul_left _ this
        have h5 : 36 * R ≤ s := by omega
        simp only [Nat.add_sub_cancel]
        calc R * (6 * p) ^ 2 = 36 * R * (p * p) := by ring
          _ ≤ s * (p * p) := Nat.mul_le_mul_right _ h5
          _ ≤ s * (2 * p * (s + 1 + 1) * N - 1) :=
            Nat.mul_le_mul_left _ (le_trans h4 h3)
    _ ≤ (r - 1) * (d - 1) := Nat.mul_le_mul_left _ hd1

end PEqualNP.Gct.Rung
