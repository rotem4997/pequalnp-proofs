import PEqualNP.Library.Evasion.Plan
import PEqualNP.Library.L002

/-!
# Evasion chain: the machine-free pieces

Pieces T3d, T5a, T5d, T5e and 3.1 (`dtimeoO`) of the plan module, the facts about `rootUp`
used by the assembly (`rootUp_spec`, `rootUp_mono`, `rootUp_pow_le`), and three helper lemmas:
`dtime_subset_dtimeo` (DTIME t inside DTIMEO t), `dtimeo_absorb` (constants absorbed by
DTIMEO), `alt_congr` (Alt respects pointwise equivalence of the predicate).
-/

namespace PEqualNP.Library.Evasion

open PEqualNP.Library

/-- T3d: the first two levels of `Alt` unfolded, and its negation. -/
theorem t3d : StmtT3d := by
  refine ⟨?_, ?_, ?_⟩
  · intro s Q
    simp [Alt]
  · intro s Q
    simp [Alt]
  · intro i s Q
    simp only [Alt, not_exists, not_and, not_not]

/-- Helper (x3): `Alt` respects pointwise equivalence of the predicate. -/
theorem alt_congr (i s : ℕ) (P Q : List Bool → Prop) (h : ∀ w, P w ↔ Q w) :
    Alt i s P ↔ Alt i s Q := by
  have : P = Q := funext fun w => propext (h w)
  subst this
  exact Iff.rfl

/-- Helper (x1): DTIME t is inside DTIMEO t. -/
theorem dtime_subset_dtimeo (t : ℕ → ℕ) : DTIME t ⊆ DTIMEO t := by
  intro L hL
  refine ⟨1, L002 t _ (fun n => ?_) hL⟩
  omega

/-- T5a: DTIMEO is monotone in the time bound. -/
theorem t5a : StmtT5a := by
  intro t t' h L ⟨K, hK⟩
  refine ⟨K, L002 _ _ (fun n => ?_) hK⟩
  have := Nat.mul_le_mul_left K (h n)
  omega

/-- Helper (x2): DTIMEO absorbs a multiplicative and an additive constant. -/
theorem dtimeo_absorb (t : ℕ → ℕ) (K K' : ℕ) :
    DTIMEO (fun n => K * t n + K') ⊆ DTIMEO t := by
  intro L ⟨M, hM⟩
  refine ⟨M * K + M * K' + M, L002 _ _ (fun n => ?_) hM⟩
  dsimp only
  have h1 : M * K * t n ≤ (M * K + M * K' + M) * t n :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : M * (K * t n + K') + M = M * K * t n + (M * K' + M) := by ring
  omega

/-- Bernoulli-type bound used for T5d. -/
private lemma pow_succ_bound (p : ℕ) : ∀ i : ℕ, p ^ i * (p + i) ≤ (p + 1) ^ i * p
  | 0 => by simp
  | i + 1 => by
    have ih := pow_succ_bound p i
    have key : p * (p + (i + 1)) ≤ (p + 1) * (p + i) := by nlinarith
    calc p ^ (i + 1) * (p + (i + 1)) = p ^ i * (p * (p + (i + 1))) := by ring
      _ ≤ p ^ i * ((p + 1) * (p + i)) := Nat.mul_le_mul_left _ key
      _ = (p + 1) * (p ^ i * (p + i)) := by ring
      _ ≤ (p + 1) * ((p + 1) ^ i * p) := Nat.mul_le_mul_left _ ih
      _ = (p + 1) ^ (i + 1) * p := by ring

/-- T5d. -/
theorem t5d : StmtT5d := by
  intro p' q hpq k
  rcases Nat.eq_zero_or_pos p' with h0 | hp
  · subst h0
    exact ⟨1, by simp⟩
  · refine ⟨2 * k * p', ?_⟩
    set i := 2 * k * p'
    have hb := pow_succ_bound p' i
    have hq : (p' + 1) ^ i ≤ q ^ i := Nat.pow_le_pow_left (by omega) i
    -- p'^i * (p' + 2 k p') ≤ q^i * p', then cancel p'
    have h1 : p' ^ i * (1 + 2 * k) * p' ≤ q ^ i * p' := by
      calc p' ^ i * (1 + 2 * k) * p' = p' ^ i * (p' + i) := by simp only [i]; ring
        _ ≤ (p' + 1) ^ i * p' := hb
        _ ≤ q ^ i * p' := Nat.mul_le_mul_right _ hq
    have h2 : p' ^ i * (1 + 2 * k) ≤ q ^ i := Nat.le_of_mul_le_mul_right h1 hp
    calc 2 * k * p' ^ i ≤ p' ^ i * (1 + 2 * k) := by nlinarith [Nat.zero_le (p' ^ i)]
      _ ≤ q ^ i := h2

/-- T5e. -/
theorem t5e : StmtT5e := by
  intro p' q hp hpq H i
  induction i with
  | zero => intro r _; exact le_refl _
  | succ i ih =>
    intro r hr
    have hqr : 1 ≤ q * r := Nat.one_le_iff_ne_zero.mpr (by
      have : 0 < q := by omega
      positivity)
    have hs : 1 ≤ p' ^ i * r := Nat.one_le_iff_ne_zero.mpr (by
      have : 0 < p' := by omega
      positivity)
    have e1 : (fun m => 2 ^ (q ^ (i + 1) * r * m)) = (fun m => 2 ^ (q ^ i * (q * r) * m)) := by
      funext m; ring_nf
    have e2 : (fun m => 2 ^ (p' ^ i * (q * r) * m)) = (fun m => 2 ^ (q * (p' ^ i * r) * m)) := by
      funext m; ring_nf
    have e3 : (fun m => 2 ^ (p' * (p' ^ i * r) * m)) = (fun m => 2 ^ (p' ^ (i + 1) * r * m)) := by
      funext m; ring_nf
    rw [e1]
    refine (ih (q * r) hqr).trans ?_
    rw [e2, ← e3]
    exact H _ hs

/-- 3.1 of note 210: DTIMEO is monotone up to a constant factor and an additive constant. -/
theorem dtimeoO : StmtDtimeoO := by
  intro t t' A h L ⟨K, hK⟩
  refine ⟨K * A + K, L002 _ _ (fun n => ?_) hK⟩
  have h1 := Nat.mul_le_mul_left K (h n)
  have h2 : K * (A * t' n + A) + K = K * A * t' n + (K * A + K) := by ring
  have h3 : K * A * t' n ≤ (K * A + K) * t' n := Nat.mul_le_mul_right _ (by omega)
  omega

/-- `rootUp v x` is the least `r` with `x ≤ r ^ v`. -/
theorem rootUp_spec (v x : ℕ) (hv : 1 ≤ v) :
    x ≤ rootUp v x ^ v ∧ ∀ r, x ≤ r ^ v → rootUp v x ≤ r := by
  have hne : ({r : ℕ | x ≤ r ^ v} : Set ℕ).Nonempty := by
    refine ⟨x, ?_⟩
    show x ≤ x ^ v
    rcases Nat.eq_zero_or_pos x with h0 | hx
    · simp [h0]
    · calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ v := Nat.pow_le_pow_right hx hv
  exact ⟨Nat.sInf_mem hne, fun r hr => Nat.sInf_le hr⟩

/-- `rootUp v` is monotone. -/
theorem rootUp_mono (v : ℕ) (hv : 1 ≤ v) : Monotone (rootUp v) := by
  intro x y hxy
  exact (rootUp_spec v x hv).2 _ (hxy.trans (rootUp_spec v y hv).1)

/-- Below the ceiling of the root: `(rootUp v x - 1) ^ v < x` once `rootUp v x ≥ 1`. -/
theorem rootUp_pred_pow_lt (v x : ℕ) (hv : 1 ≤ v) (hr : 1 ≤ rootUp v x) :
    (rootUp v x - 1) ^ v < x := by
  by_contra hc
  have := (rootUp_spec v x hv).2 (rootUp v x - 1) (Nat.le_of_not_lt hc)
  omega

/-- The ceiling of the root is at most twice the root: `rootUp v x ^ v ≤ 2 ^ v * x`. -/
theorem rootUp_pow_le_two_pow_mul (v x : ℕ) (hv : 1 ≤ v) : rootUp v x ^ v ≤ 2 ^ v * x := by
  rcases Nat.eq_zero_or_pos (rootUp v x) with h0 | hpos
  · rw [h0, zero_pow (by omega)]; exact Nat.zero_le _
  · have hlt := rootUp_pred_pow_lt v x hv hpos
    rcases Nat.lt_or_ge (rootUp v x) 2 with h1 | h2
    · have he : rootUp v x = 1 := by omega
      rw [he, one_pow]
      have hx : 1 ≤ x := by
        rw [he, Nat.sub_self, zero_pow (by omega)] at hlt; omega
      calc 1 ≤ 2 ^ v := Nat.one_le_two_pow
        _ = 2 ^ v * 1 := (mul_one _).symm
        _ ≤ 2 ^ v * x := Nat.mul_le_mul_left _ hx
    · calc rootUp v x ^ v ≤ (2 * (rootUp v x - 1)) ^ v := Nat.pow_le_pow_left (by omega) v
        _ = 2 ^ v * (rootUp v x - 1) ^ v := mul_pow _ _ _
        _ ≤ 2 ^ v * x := Nat.mul_le_mul_left _ hlt.le

/-- The assembly form: `rootUp v (n ^ u) ^ v ≤ 2 ^ v * n ^ u`. -/
theorem rootUp_pow_le (u v n : ℕ) (hv : 1 ≤ v) : rootUp v (n ^ u) ^ v ≤ 2 ^ v * n ^ u :=
  rootUp_pow_le_two_pow_mul v (n ^ u) hv

end PEqualNP.Library.Evasion
