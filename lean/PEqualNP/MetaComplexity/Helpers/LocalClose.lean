import PEqualNP.MetaComplexity.Helpers.LocalFinite

/-!
# The asymptotic form of the local reduction chain

Helper for `L-meta-033`. With `q ^ b ≤ n ^ a`, `2 a < b`, lengths at most `n ^ c + c` and
`B = q (log n + 1) ^ c`, the inequality of the finite form (`LocalFinite.finite`) fails for
large `n`. The arithmetic is crude: with `l = log n + 1`, the right side is at most
`2 ^ (4 (c + 3) l B)`, and `(16 c + 55) q ^ 2 l ^ (c + 1) ≤ n` puts the exponent on the left
above that.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalClose

open PEqualNP.MetaComplexity

/-! ## The arithmetic of the asymptotic form -/

/-- A power of the logarithm is eventually below any fixed fraction of `n`. -/
theorem polylog (C d : ℕ) : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → C * (Nat.log 2 n + 1) ^ d ≤ n := by
  obtain ⟨A, hA⟩ : ∃ A, A = C * (d + 1) ^ d := ⟨_, rfl⟩
  refine ⟨2 ^ ((d + 1) * (A + 2)), fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by
    have : 0 < 2 ^ ((d + 1) * (A + 2)) := by positivity
    omega
  have hlog : (d + 1) * (A + 2) ≤ Nat.log 2 n := by
    have := Nat.log_mono_right (b := 2) hn
    rwa [Nat.log_pow (by norm_num)] at this
  obtain ⟨l, hl⟩ : ∃ l, l = Nat.log 2 n + 1 := ⟨_, rfl⟩
  rw [← hl]
  obtain ⟨t, ht⟩ : ∃ t, t = l / (d + 1) := ⟨_, rfl⟩
  have ht1 : A + 2 ≤ t := by
    rw [ht, Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact hlog.trans (by omega)
  have ht2 : (d + 1) * t ≤ l := by rw [ht]; exact Nat.mul_div_le _ _
  have ht3 : l ≤ (d + 1) * 2 ^ t := by
    have h1 : l < (d + 1) * (l / (d + 1) + 1) := Nat.lt_mul_div_succ _ (by omega)
    rw [← ht] at h1
    have h2 : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
    exact h1.le.trans (Nat.mul_le_mul_left _ h2)
  have h4 : C * l ^ d ≤ A * 2 ^ (t * d) := by
    calc C * l ^ d ≤ C * ((d + 1) * 2 ^ t) ^ d :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht3 d)
      _ = A * 2 ^ (t * d) := by rw [hA, mul_pow, pow_mul, mul_assoc]
  have h5 : A ≤ 2 ^ A := Nat.lt_two_pow_self.le
  calc C * l ^ d ≤ A * 2 ^ (t * d) := h4
    _ ≤ 2 ^ A * 2 ^ (t * d) := Nat.mul_le_mul_right _ h5
    _ = 2 ^ (A + t * d) := (pow_add 2 A (t * d)).symm
    _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by
        rw [hl] at ht2
        linarith)
    _ ≤ n := Nat.pow_log_le_self 2 hn0

/-- With `q ^ b ≤ n ^ a` and `2 a < b`, the square of `q` times a power of the logarithm is
eventually below `n`. -/
theorem key (a b c : ℕ) (hab : 2 * a < b) : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ q : ℕ,
    q ^ b ≤ n ^ a → (16 * c + 55) * (q ^ 2 * (Nat.log 2 n + 1) ^ (c + 1)) ≤ n := by
  obtain ⟨n0, h0⟩ := polylog ((16 * c + 55) ^ b) (b * (c + 1))
  refine ⟨n0 + 1, fun n hn q hq => ?_⟩
  have h := h0 n (by omega)
  have hb : b ≠ 0 := by omega
  rw [← Nat.pow_le_pow_iff_left hb]
  have e1 : (q ^ 2) ^ b = (q ^ b) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : ((Nat.log 2 n + 1) ^ (c + 1)) ^ b = (Nat.log 2 n + 1) ^ (b * (c + 1)) := by
    rw [← pow_mul, mul_comm]
  calc ((16 * c + 55) * (q ^ 2 * (Nat.log 2 n + 1) ^ (c + 1))) ^ b
      = (16 * c + 55) ^ b * (Nat.log 2 n + 1) ^ (b * (c + 1)) * (q ^ b) ^ 2 := by
        rw [mul_pow, mul_pow, e1, e2, mul_comm ((q ^ b) ^ 2), mul_assoc]
    _ ≤ n * (n ^ a) ^ 2 := Nat.mul_le_mul h (Nat.pow_le_pow_left hq 2)
    _ = n ^ (2 * a + 1) := by ring
    _ ≤ n ^ b := Nat.pow_le_pow_right (by omega) (by omega)

theorem logM_le (n c : ℕ) : Nat.log 2 (n ^ c + c) ≤ c * (Nat.log 2 n + 1 + 1) := by
  have h1 : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self (by norm_num) n).le
  have h2 : n ^ c ≤ 2 ^ ((Nat.log 2 n + 1) * c) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 c
  have h3 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
  have hpos : 0 < 2 ^ ((Nat.log 2 n + 1) * c) := by positivity
  have h4 : n ^ c + c ≤ 2 ^ (c * (Nat.log 2 n + 1 + 1)) := by
    calc n ^ c + c ≤ 2 ^ ((Nat.log 2 n + 1) * c) * (c + 1) := by
          linarith [Nat.le_mul_of_pos_left c hpos]
      _ ≤ 2 ^ ((Nat.log 2 n + 1) * c) * 2 ^ c := Nat.mul_le_mul_left _ h3
      _ = 2 ^ (c * (Nat.log 2 n + 1 + 1)) := by rw [← pow_add]; congr 1; ring
  have := Nat.log_mono_right (b := 2) h4
  rwa [Nat.log_pow (by norm_num)] at this

/-- The two inequalities the asymptotic form needs, from the one of `key`. Here `l` stands for
`log n + 1`, `Lm` for the logarithm of the length bound and `B` for the size bound. -/
theorem arith (n q c l Lm B : ℕ) (hq : 0 < q) (hl : 1 ≤ l) (hnl : n < 2 ^ l)
    (hLm : Lm ≤ c * (l + 1)) (hB : B = q * l ^ c)
    (hK : (16 * c + 55) * (q ^ 2 * l ^ (c + 1)) ≤ n) :
    2 * q * (Lm + 2) < n ∧
    8 * q * (B * (B * ((3 * ((Lm + B + 1) * (Lm + B + 1))) ^ (B - 1) * (Lm + B)))) <
      2 ^ ((n - 3 * q) / (4 * q)) := by
  obtain ⟨P, hP⟩ : ∃ P, P = q ^ 2 * l ^ (c + 1) := ⟨_, rfl⟩
  rw [← hP] at hK
  have hlc : 1 ≤ l ^ c := Nat.one_le_pow _ _ hl
  have hqB : q ≤ B := by rw [hB]; exact Nat.le_mul_of_pos_right _ hlc
  have hqP : q * l ≤ P := by
    rw [hP, pow_succ l c, sq]
    calc q * l = (q * 1) * (1 * l) := by ring
      _ ≤ (q * q) * (l ^ c * l) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hq) (Nat.mul_le_mul_right _ hlc)
  have hqP' : q ≤ P := le_trans (Nat.le_mul_of_pos_right _ hl) hqP
  have hPpos : 0 < P := by omega
  have hBP : l * B * q = P := by rw [hB, hP]; ring
  have hqn : q ≤ n := le_trans hqP' (le_trans (Nat.le_mul_of_pos_left _ (by omega)) hK)
  have hcl : c ≤ c * l := Nat.le_mul_of_pos_right _ hl
  constructor
  · calc 2 * q * (Lm + 2) ≤ 2 * q * ((2 * c + 2) * l) :=
          Nat.mul_le_mul_left _ (by linarith)
      _ = (4 * c + 4) * (q * l) := by ring
      _ ≤ (4 * c + 4) * P := Nat.mul_le_mul_left _ hqP
      _ < (16 * c + 55) * P := by linarith [Nat.zero_le (c * P)]
      _ ≤ n := hK
  · obtain ⟨X, hX⟩ : ∃ X, X = Lm + B + 1 := ⟨_, rfl⟩
    rw [← hX]
    obtain ⟨k, hk⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    have e : B - 1 = k := by omega
    rw [e]
    have h2 : 8 * q * (B * (B * ((3 * (X * X)) ^ k * (Lm + B)))) ≤ (4 * (X * X)) ^ (k + 2) := by
      have a1 : 8 * q * (B * (B * (Lm + B))) ≤ (4 * (X * X)) ^ 2 := by
        have : q * (B * (B * (Lm + B))) ≤ X * (X * (X * X)) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
            (Nat.mul_le_mul (by omega) (by omega)))
        calc 8 * q * (B * (B * (Lm + B))) = 8 * (q * (B * (B * (Lm + B)))) := by ring
          _ ≤ 8 * (X * (X * (X * X))) := Nat.mul_le_mul_left _ this
          _ ≤ (4 * (X * X)) ^ 2 := by linarith [Nat.zero_le (X * (X * (X * X)))]
      have a2 : (3 * (X * X)) ^ k ≤ (4 * (X * X)) ^ k :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (by norm_num)) k
      calc 8 * q * (B * (B * ((3 * (X * X)) ^ k * (Lm + B))))
          = 8 * q * (B * (B * (Lm + B))) * (3 * (X * X)) ^ k := by ring
        _ ≤ (4 * (X * X)) ^ 2 * (4 * (X * X)) ^ k := Nat.mul_le_mul a1 a2
        _ = (4 * (X * X)) ^ (k + 2) := by rw [← pow_add, add_comm]
    have h3 : 2 * X ≤ 2 ^ (l * (c + 3)) := by
      have hl2 : l ≤ 2 ^ l := Nat.lt_two_pow_self.le
      have b1 : B ≤ 2 ^ l * 2 ^ (l * c) := by
        rw [hB, pow_mul]
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hl2 c)
      have b2 : Lm + 1 ≤ 2 ^ c * 2 ^ l := by
        have c1 : c + 1 ≤ 2 ^ c := Nat.lt_two_pow_self
        have c2 : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
        calc Lm + 1 ≤ (c + 1) * (l + 1) := by linarith
          _ ≤ 2 ^ c * 2 ^ l := Nat.mul_le_mul c1 c2
      have b3 : 2 ^ c * 2 ^ l ≤ 2 ^ (l * (c + 1)) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by linarith [Nat.le_mul_of_pos_left c hl])
      have b4 : 2 ^ l * 2 ^ (l * c) = 2 ^ (l * (c + 1)) := by
        rw [← pow_add]; congr 1; ring
      calc 2 * X = 2 * ((Lm + 1) + B) := by rw [hX]; ring
        _ ≤ 2 * (2 ^ (l * (c + 1)) + 2 ^ (l * (c + 1))) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (b2.trans b3) (b1.trans b4.le))
        _ = 2 ^ (l * (c + 1) + 2) := by ring
        _ ≤ 2 ^ (l * (c + 3)) := Nat.pow_le_pow_right (by norm_num) (by linarith)
    have h4 : (4 * (X * X)) ^ (k + 2) ≤ 2 ^ (4 * (c + 3) * l * B) := by
      calc (4 * (X * X)) ^ (k + 2) = ((2 * X) ^ 2) ^ (k + 2) := by congr 1; ring
        _ ≤ ((2 ^ (l * (c + 3))) ^ 2) ^ (k + 2) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) _
        _ = 2 ^ (l * (c + 3) * 2 * (k + 2)) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
        _ ≤ 2 ^ (4 * (c + 3) * l * B) := Nat.pow_le_pow_right (by norm_num) (by
            rw [hk]
            linarith [Nat.zero_le (l * c * k), Nat.zero_le (l * k)])
    have h5 : 4 * (c + 3) * l * B + 1 ≤ (n - 3 * q) / (4 * q) := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      apply Nat.le_sub_of_add_le
      have e1 : (4 * (c + 3) * l * B + 1) * (4 * q) = 16 * (c + 3) * (l * B * q) + 4 * q := by
        ring
      rw [e1, hBP]
      have e2 : (16 * c + 55) * P = 16 * (c + 3) * P + 7 * P := by ring
      rw [e2] at hK
      linarith
    calc 8 * q * (B * (B * ((3 * (X * X)) ^ k * (Lm + B))))
        ≤ (4 * (X * X)) ^ (k + 2) := h2
      _ ≤ 2 ^ (4 * (c + 3) * l * B) := h4
      _ < 2 ^ (4 * (c + 3) * l * B + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ ((n - 3 * q) / (4 * q)) := Nat.pow_le_pow_right (by norm_num) h5

/-- The asymptotic form. -/
theorem asymptotic : ∀ (a b c : ℕ), 2 * a < b → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ¬ ∃ (q : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q ∧ q ^ b ≤ n ^ a ∧ PEqualNP.MetaComplexity.QueryLocal n q w ∧ (∀ x : Fin n → Bool, (w x).length ≤ n ^ c + c) ∧ (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) ∧ ∀ (n' s : ℕ) (T : List (Option Bool)), w (fun _ : Fin n => false) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f (q * (Nat.log 2 n + 1) ^ c) := by
  intro a b c hab
  obtain ⟨n0, h0⟩ := key a b c hab
  refine ⟨n0, fun n hn => ?_⟩
  rintro ⟨q, w, hq, hqb, hloc, hlen, hcor, hsim⟩
  have hK := h0 n hn q hqb
  obtain ⟨g1, g2⟩ := arith n q c (Nat.log 2 n + 1) (Nat.log 2 (n ^ c + c))
    (q * (Nat.log 2 n + 1) ^ c) hq (by omega) (Nat.lt_pow_succ_log_self (by norm_num) n)
    (logM_le n c) rfl hK
  exact absurd (LocalFinite.finite n q (n ^ c + c) (q * (Nat.log 2 n + 1) ^ c) w hq hloc hlen hcor hsim g1)
    (not_le.mpr g2)

end PEqualNP.MetaComplexity.Helpers.LocalClose
