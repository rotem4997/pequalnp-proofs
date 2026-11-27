import PEqualNP.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_gct_241

noncomputable def epsVal : ℝ := 39 / 250000
noncomputable def cVal : ℝ := 1678911 / 20000000

noncomputable def g0 : Polynomial ℝ :=
  Polynomial.monomial 6402 1 - Polynomial.monomial 12802 epsVal

noncomputable def g1 : Polynomial ℝ :=
  Polynomial.monomial 0 epsVal - Polynomial.monomial 6400 1

noncomputable def g2 : Polynomial ℝ :=
  Polynomial.monomial 8449 cVal - Polynomial.monomial 4353 cVal

noncomputable def gVec : Fin 3 → Polynomial ℝ
  | ⟨0, _⟩ => g0
  | ⟨1, _⟩ => g1
  | ⟨2, _⟩ => g2

noncomputable def sVec : Fin 3 → ℝ := fun _ => 1

noncomputable def P : Polynomial ℝ :=
  (Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (sVec i) * gVec i ^ 3

lemma P_eq : P = g0 ^ 3 + g1 ^ 3 + g2 ^ 3 := by
  simp only [P, Fin.sum_univ_three, sVec, gVec, map_one, one_mul]

lemma support_monomial_sub_card_le_two (n m : ℕ) (a b : ℝ) :
    (Polynomial.monomial n a - Polynomial.monomial m b).support.card ≤ 2 := by
  have hsub : (Polynomial.monomial n a - Polynomial.monomial m b).support ⊆ {n, m} := by
    intro k hk
    rw [sub_eq_add_neg] at hk
    have h1 := Polynomial.support_add hk
    rw [Finset.mem_union, Polynomial.support_neg] at h1
    rcases h1 with h1 | h1
    · have hn : k ∈ ({n} : Finset ℕ) := Polynomial.support_monomial_subset n a h1
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    · have hm : k ∈ ({m} : Finset ℕ) := Polynomial.support_monomial_subset m b h1
      simp only [Finset.mem_singleton] at hm
      simp [hm]
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le n {m}).trans (by simp))

lemma gVec_support_card_le_two (i : Fin 3) : (gVec i).support.card ≤ 2 := by
  fin_cases i
  · exact support_monomial_sub_card_le_two 6402 12802 1 epsVal
  · exact support_monomial_sub_card_le_two 0 6400 epsVal 1
  · exact support_monomial_sub_card_le_two 8449 4353 cVal cVal

noncomputable def sqrt8 (q : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt q)))))))

lemma sqrt8_nonneg (q : ℝ) : 0 ≤ sqrt8 q := Real.sqrt_nonneg _

lemma pow256_eq (x : ℝ) :
    x ^ 256 = (((((((x ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
  have h256 : (256 : ℕ) = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 := by norm_num
  rw [h256]
  simp only [pow_mul]

lemma lt_of_sq_lt_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  nlinarith

lemma pow16_eq (x : ℝ) : x ^ 16 = (((x ^ 2) ^ 2) ^ 2) ^ 2 := by
  have h16 : (16 : ℕ) = 2 * 2 * 2 * 2 := by norm_num
  rw [h16]
  simp only [pow_mul]

lemma lt_of_pow16_lt {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 16 < b ^ 16) : a < b := by
  rw [pow16_eq a, pow16_eq b] at h
  have h3 := lt_of_sq_lt_sq (sq_nonneg _) h
  have h2 := lt_of_sq_lt_sq (sq_nonneg _) h3
  have h1 := lt_of_sq_lt_sq (sq_nonneg _) h2
  exact lt_of_sq_lt_sq hb h1

set_option maxRecDepth 4000 in
lemma lt_of_pow256_lt {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 256 < b ^ 256) : a < b := by
  have h256 : (256 : ℕ) = 16 * 16 := by norm_num
  rw [h256, pow_mul, pow_mul] at h
  have h16 := lt_of_pow16_lt (pow_nonneg hb 16) h
  exact lt_of_pow16_lt hb h16

lemma sqrt8_pow {q : ℝ} (hq : 0 ≤ q) : (sqrt8 q) ^ 256 = q := by
  rw [pow256_eq]
  unfold sqrt8
  rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hq]

lemma sqrt8_lt_sqrt8 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : sqrt8 a < sqrt8 b := by
  apply lt_of_pow256_lt (sqrt8_nonneg b)
  rw [sqrt8_pow ha, sqrt8_pow (ha.trans hab.le)]
  exact hab

lemma one_lt_sqrt8 {q : ℝ} (hq : 1 < q) : 1 < sqrt8 q := by
  apply lt_of_pow256_lt (sqrt8_nonneg q)
  rw [one_pow, sqrt8_pow (by linarith)]
  exact hq

lemma sqrt8_two_lt_two : sqrt8 2 < 2 := by
  apply lt_of_pow256_lt (by norm_num)
  rw [sqrt8_pow (by norm_num)]
  norm_num

lemma lt_sqrt8_of_chain {q c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ}
    (hq0 : 0 ≤ q)
    (h1 : c0 ^ 2 ≤ c1) (h2 : c1 ^ 2 ≤ c2) (h3 : c2 ^ 2 ≤ c3) (h4 : c3 ^ 2 ≤ c4)
    (h5 : c4 ^ 2 ≤ c5) (h6 : c5 ^ 2 ≤ c6) (h7 : c6 ^ 2 ≤ c7) (h8 : c7 ^ 2 ≤ c8)
    (h9 : c8 < q) : c0 < sqrt8 q := by
  have s2 : (c0 ^ 2) ^ 2 ≤ c2 := (pow_le_pow_left₀ (sq_nonneg c0) h1 2).trans h2
  have s3 : ((c0 ^ 2) ^ 2) ^ 2 ≤ c3 := (pow_le_pow_left₀ (sq_nonneg _) s2 2).trans h3
  have s4 : (((c0 ^ 2) ^ 2) ^ 2) ^ 2 ≤ c4 := (pow_le_pow_left₀ (sq_nonneg _) s3 2).trans h4
  have s5 : ((((c0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ c5 := (pow_le_pow_left₀ (sq_nonneg _) s4 2).trans h5
  have s6 : (((((c0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ c6 := (pow_le_pow_left₀ (sq_nonneg _) s5 2).trans h6
  have s7 : ((((((c0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ c7 := (pow_le_pow_left₀ (sq_nonneg _) s6 2).trans h7
  have s8 : (((((((c0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 ≤ c8 := (pow_le_pow_left₀ (sq_nonneg _) s7 2).trans h8
  apply lt_of_pow256_lt (sqrt8_nonneg q)
  rw [pow256_eq c0, sqrt8_pow hq0]
  linarith

lemma sqrt8_lt_of_chain {q d0 d1 d2 d3 d4 d5 d6 d7 d8 : ℝ}
    (hq0 : 0 ≤ q) (hd0 : 0 ≤ d0)
    (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3) (hd4 : 0 ≤ d4)
    (hd5 : 0 ≤ d5) (hd6 : 0 ≤ d6) (hd7 : 0 ≤ d7)
    (h1 : d1 ≤ d0 ^ 2) (h2 : d2 ≤ d1 ^ 2) (h3 : d3 ≤ d2 ^ 2) (h4 : d4 ≤ d3 ^ 2)
    (h5 : d5 ≤ d4 ^ 2) (h6 : d6 ≤ d5 ^ 2) (h7 : d7 ≤ d6 ^ 2) (h8 : d8 ≤ d7 ^ 2)
    (h9 : q < d8) : sqrt8 q < d0 := by
  have s2 : d2 ≤ (d0 ^ 2) ^ 2 := h2.trans (pow_le_pow_left₀ hd1 h1 2)
  have s3 : d3 ≤ ((d0 ^ 2) ^ 2) ^ 2 := h3.trans (pow_le_pow_left₀ hd2 s2 2)
  have s4 : d4 ≤ (((d0 ^ 2) ^ 2) ^ 2) ^ 2 := h4.trans (pow_le_pow_left₀ hd3 s3 2)
  have s5 : d5 ≤ ((((d0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := h5.trans (pow_le_pow_left₀ hd4 s4 2)
  have s6 : d6 ≤ (((((d0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := h6.trans (pow_le_pow_left₀ hd5 s5 2)
  have s7 : d7 ≤ ((((((d0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := h7.trans (pow_le_pow_left₀ hd6 s6 2)
  have s8 : d8 ≤ (((((((d0 ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := h8.trans (pow_le_pow_left₀ hd7 s7 2)
  apply lt_of_pow256_lt hd0
  rw [pow256_eq d0, sqrt8_pow hq0]
  linarith

lemma eval_P_of_pow {u q : ℝ} (hq : u ^ 256 = q) :
    P.eval u =
      (q ^ 25 * (1 - epsVal * q ^ 25)) ^ 3 * (u ^ 3) ^ 2 +
      (cVal * q ^ 17 * (q ^ 16 - 1)) ^ 3 * u ^ 3 +
      (epsVal - q ^ 25) ^ 3 := by
  rw [P_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_monomial, g0, g1, g2, pow_zero, mul_one, one_mul]
  have hu6400 : u ^ 6400 = q ^ 25 := by
    rw [show (6400 : ℕ) = 256 * 25 by norm_num, pow_mul, hq]
  have hu6402 : u ^ 6402 = u ^ 2 * q ^ 25 := by
    rw [show (6402 : ℕ) = 2 + 256 * 25 by norm_num, pow_add, pow_mul, hq]
  have hu12802 : u ^ 12802 = u ^ 2 * q ^ 50 := by
    rw [show (12802 : ℕ) = 2 + 256 * 50 by norm_num, pow_add, pow_mul, hq]
  have hu4353 : u ^ 4353 = u * q ^ 17 := by
    rw [show (4353 : ℕ) = 1 + 256 * 17 by norm_num, pow_add, pow_one, pow_mul, hq]
  have hu8449 : u ^ 8449 = u * q ^ 33 := by
    rw [show (8449 : ℕ) = 1 + 256 * 33 by norm_num, pow_add, pow_one, pow_mul, hq]
  rw [hu6400, hu6402, hu12802, hu4353, hu8449]
  ring

lemma eval_P_one : P.eval 1 = 0 := by
  rw [P_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_monomial, g0, g1, g2, one_pow, mul_one]
  ring

lemma mul_inv_pow_eq {x : ℝ} (hx : x ≠ 0) {a b c : ℕ} (hab : a = b + c) :
    x ^ a * (x ^ c)⁻¹ = x ^ b := by
  rw [hab, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero c hx), mul_one]

lemma eval_P_inv {x : ℝ} (hx : x ≠ 0) :
    x ^ 38406 * P.eval (1 / x) = - P.eval x := by
  rw [P_eq]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_monomial, g0, g1, g2, pow_zero, mul_one, one_mul, one_div, inv_pow]
  have h0 : x ^ 12802 * ((x ^ 6402)⁻¹ - epsVal * (x ^ 12802)⁻¹) = -(epsVal - x ^ 6400) := by
    rw [mul_sub, mul_inv_pow_eq hx (by norm_num : 12802 = 6400 + 6402)]
    rw [← mul_assoc, mul_comm (x ^ 12802) epsVal, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero 12802 hx), mul_one]
    ring
  have h1 : x ^ 12802 * (epsVal - (x ^ 6400)⁻¹) = -(x ^ 6402 - epsVal * x ^ 12802) := by
    rw [mul_sub, mul_inv_pow_eq hx (by norm_num : 12802 = 6402 + 6400)]
    ring
  have h2 : x ^ 12802 * (cVal * (x ^ 8449)⁻¹ - cVal * (x ^ 4353)⁻¹) =
      -(cVal * x ^ 8449 - cVal * x ^ 4353) := by
    rw [mul_sub]
    rw [← mul_assoc, mul_comm (x ^ 12802) cVal, mul_assoc,
        mul_inv_pow_eq hx (by norm_num : 12802 = 4353 + 8449)]
    rw [← mul_assoc, mul_comm (x ^ 12802) cVal, mul_assoc,
        mul_inv_pow_eq hx (by norm_num : 12802 = 8449 + 4353)]
    ring
  have hpow : x ^ 38406 = (x ^ 12802) ^ 3 := by
    rw [show (38406 : ℕ) = 12802 * 3 by norm_num, pow_mul]
  rw [hpow, mul_add, mul_add, ← mul_pow, ← mul_pow, ← mul_pow, h0, h1, h2]
  ring

lemma eval_P_pos_of_lo {u q l : ℝ} (hq : u ^ 256 = q) (hl0 : 0 ≤ l) (hlu : l < u)
    (hA : 0 ≤ (q ^ 25 * (1 - epsVal * q ^ 25)) ^ 3)
    (hB : 0 ≤ (cVal * q ^ 17 * (q ^ 16 - 1)) ^ 3)
    (hval : 0 < (q ^ 25 * (1 - epsVal * q ^ 25)) ^ 3 * (l ^ 3) ^ 2 +
                (cVal * q ^ 17 * (q ^ 16 - 1)) ^ 3 * l ^ 3 +
                (epsVal - q ^ 25) ^ 3) :
    0 < P.eval u := by
  rw [eval_P_of_pow hq]
  have h3 : l ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hl0 hlu.le 3
  have h6 : (l ^ 3) ^ 2 ≤ (u ^ 3) ^ 2 := pow_le_pow_left₀ (pow_nonneg hl0 3) h3 2
  have t1 := mul_le_mul_of_nonneg_left h6 hA
  have t2 := mul_le_mul_of_nonneg_left h3 hB
  linarith

lemma eval_P_neg_of_hi {u q h : ℝ} (hq : u ^ 256 = q) (hu0 : 0 ≤ u) (huh : u < h)
    (hA : 0 ≤ (q ^ 25 * (1 - epsVal * q ^ 25)) ^ 3)
    (hB : 0 ≤ (cVal * q ^ 17 * (q ^ 16 - 1)) ^ 3)
    (hval : (q ^ 25 * (1 - epsVal * q ^ 25)) ^ 3 * (h ^ 3) ^ 2 +
            (cVal * q ^ 17 * (q ^ 16 - 1)) ^ 3 * h ^ 3 +
            (epsVal - q ^ 25) ^ 3 < 0) :
    P.eval u < 0 := by
  rw [eval_P_of_pow hq]
  have h3 : u ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ hu0 huh.le 3
  have h6 : (u ^ 3) ^ 2 ≤ (h ^ 3) ^ 2 := pow_le_pow_left₀ (pow_nonneg hu0 3) h3 2
  have t1 := mul_le_mul_of_nonneg_left h6 hA
  have t2 := mul_le_mul_of_nonneg_left h3 hB
  linarith

noncomputable def x1 : ℝ := sqrt8 (26 / 25)
noncomputable def x2 : ℝ := sqrt8 (27 / 25)
noncomputable def x3 : ℝ := sqrt8 (17 / 15)
noncomputable def x4 : ℝ := sqrt8 (13 / 11)
noncomputable def x5 : ℝ := sqrt8 (7 / 5)
noncomputable def x6 : ℝ := sqrt8 2

lemma eval_x1_pos : 0 < P.eval x1 := by
  have hu : (1000153216 / 1000000000 : ℝ) < x1 :=
    lt_sqrt8_of_chain
      (c1 := 1000306456 / 1000000000) (c2 := 1000613006 / 1000000000)
      (c3 := 1001226388 / 1000000000) (c4 := 1002454281 / 1000000000)
      (c5 := 1004914586 / 1000000000) (c6 := 1009853326 / 1000000000)
      (c7 := 1019803741 / 1000000000) (c8 := 1039999671 / 1000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact eval_P_pos_of_lo (sqrt8_pow (by norm_num)) (by norm_num) hu
    (by unfold epsVal; norm_num) (by unfold cVal; norm_num)
    (by unfold epsVal cVal; norm_num)

lemma eval_x2_neg : P.eval x2 < 0 := by
  have hu : x2 < (1000300676 / 1000000000 : ℝ) :=
    sqrt8_lt_of_chain
      (d1 := 1000601442 / 1000000000) (d2 := 1001203245 / 1000000000)
      (d3 := 1002407937 / 1000000000) (d4 := 1004821672 / 1000000000)
      (d5 := 1009666592 / 1000000000) (d6 := 1019426627 / 1000000000)
      (d7 := 1039230647 / 1000000000) (d8 := 1080000337 / 1000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  exact eval_P_neg_of_hi (sqrt8_pow (by norm_num)) (sqrt8_nonneg _) hu
    (by unfold epsVal; norm_num) (by unfold cVal; norm_num)
    (by unfold epsVal cVal; norm_num)

lemma eval_x3_pos : 0 < P.eval x3 := by
  have hu : (1000489037 / 1000000000 : ℝ) < x3 :=
    lt_sqrt8_of_chain
      (c1 := 1000978314 / 1000000000) (c2 := 1001957586 / 1000000000)
      (c3 := 1003919005 / 1000000000) (c4 := 1007853369 / 1000000000)
      (c5 := 1015768414 / 1000000000) (c6 := 1031785471 / 1000000000)
      (c7 := 1064581259 / 1000000000) (c8 := 1133333258 / 1000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact eval_P_pos_of_lo (sqrt8_pow (by norm_num)) (by norm_num) hu
    (by unfold epsVal; norm_num) (by unfold cVal; norm_num)
    (by unfold epsVal cVal; norm_num)

lemma eval_x4_neg : P.eval x4 < 0 := by
  have hu : x4 < (1000652769 / 1000000000 : ℝ) :=
    sqrt8_lt_of_chain
      (d1 := 1001305964 / 1000000000) (d2 := 1002613633 / 1000000000)
      (d3 := 1005234097 / 1000000000) (d4 := 1010495589 / 1000000000)
      (d5 := 1021101335 / 1000000000) (d6 := 1042647936 / 1000000000)
      (d7 := 1087114718 / 1000000000) (d8 := 1181818410 / 1000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  exact eval_P_neg_of_hi (sqrt8_pow (by norm_num)) (sqrt8_nonneg _) hu
    (by unfold epsVal; norm_num) (by unfold cVal; norm_num)
    (by unfold epsVal cVal; norm_num)

lemma eval_x5_pos : 0 < P.eval x5 := by
  have hu : (1001315207 / 1000000000 : ℝ) < x5 :=
    lt_sqrt8_of_chain
      (c1 := 1002632144 / 1000000000) (c2 := 1005271217 / 1000000000)
      (c3 := 1010570220 / 1000000000) (c4 := 1021252170 / 1000000000)
      (c5 := 1042955995 / 1000000000) (c6 := 1087757208 / 1000000000)
      (c7 := 1183215744 / 1000000000) (c8 := 1399999497 / 1000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact eval_P_pos_of_lo (sqrt8_pow (by norm_num)) (by norm_num) hu
    (by unfold epsVal; norm_num) (by unfold cVal; norm_num)
    (by unfold epsVal cVal; norm_num)

lemma eval_x6_neg : P.eval x6 < 0 := by
  have h1 : (1 : ℝ) < x6 := one_lt_sqrt8 (by norm_num)
  have h2 : x6 < 2 := sqrt8_two_lt_two
  have h3 : x6 ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (sqrt8_nonneg _) h2.le 3
  have h6 : (1 : ℝ) ≤ (x6 ^ 3) ^ 2 := by
    have h13 : (1 : ℝ) ≤ x6 ^ 3 := one_le_pow₀ h1.le
    nlinarith
  have hA : ((2 : ℝ) ^ 25 * (1 - epsVal * (2 : ℝ) ^ 25)) ^ 3 ≤ 0 := by unfold epsVal; norm_num
  have hB : 0 ≤ (cVal * (2 : ℝ) ^ 17 * ((2 : ℝ) ^ 16 - 1)) ^ 3 := by unfold cVal; norm_num
  have t1 : ((2 : ℝ) ^ 25 * (1 - epsVal * (2 : ℝ) ^ 25)) ^ 3 * (x6 ^ 3) ^ 2 ≤
      ((2 : ℝ) ^ 25 * (1 - epsVal * (2 : ℝ) ^ 25)) ^ 3 * 1 :=
    mul_le_mul_of_nonpos_left h6 hA
  have t2 : (cVal * (2 : ℝ) ^ 17 * ((2 : ℝ) ^ 16 - 1)) ^ 3 * x6 ^ 3 ≤
      (cVal * (2 : ℝ) ^ 17 * ((2 : ℝ) ^ 16 - 1)) ^ 3 * 2 ^ 3 :=
    mul_le_mul_of_nonneg_left h3 hB
  have hnum : ((2 : ℝ) ^ 25 * (1 - epsVal * (2 : ℝ) ^ 25)) ^ 3 * 1 +
      (cVal * (2 : ℝ) ^ 17 * ((2 : ℝ) ^ 16 - 1)) ^ 3 * 2 ^ 3 +
      (epsVal - (2 : ℝ) ^ 25) ^ 3 < 0 := by
    unfold epsVal cVal
    norm_num
  have hev : P.eval x6 =
      ((2 : ℝ) ^ 25 * (1 - epsVal * (2 : ℝ) ^ 25)) ^ 3 * (x6 ^ 3) ^ 2 +
      (cVal * (2 : ℝ) ^ 17 * ((2 : ℝ) ^ 16 - 1)) ^ 3 * x6 ^ 3 +
      (epsVal - (2 : ℝ) ^ 25) ^ 3 :=
    eval_P_of_pow (sqrt8_pow (by norm_num : (0 : ℝ) ≤ 2))
  linarith

lemma P_ne_zero : P ≠ 0 := by
  intro h
  have hp := eval_x1_pos
  rw [h, Polynomial.eval_zero] at hp
  exact lt_irrefl 0 hp

lemma exists_zero_pos_neg {a b : ℝ} (hab : a < b) (ha : 0 < P.eval a) (hb : P.eval b < 0) :
    ∃ r ∈ Set.Ioo a b, P.eval r = 0 := by
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) := P.continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := ⟨hb, ha⟩
  exact intermediate_value_Ioo' hab.le hcont hmem

lemma exists_zero_neg_pos {a b : ℝ} (hab : a < b) (ha : P.eval a < 0) (hb : 0 < P.eval b) :
    ∃ r ∈ Set.Ioo a b, P.eval r = 0 := by
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) := P.continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := ⟨ha, hb⟩
  exact intermediate_value_Ioo hab.le hcont hmem

lemma eval_inv_zero {r : ℝ} (hr0 : r ≠ 0) (hr : P.eval r = 0) : P.eval (1 / r) = 0 := by
  have h := eval_P_inv hr0
  rw [hr, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 38406 hr0)

lemma eleven_pos_roots :
    11 ≤ (P.roots.toFinset.filter (fun x : ℝ => 0 < x)).card := by
  have h1x1 : 1 < x1 := one_lt_sqrt8 (by norm_num)
  have hx12 : x1 < x2 := sqrt8_lt_sqrt8 (by norm_num) (by norm_num)
  have hx23 : x2 < x3 := sqrt8_lt_sqrt8 (by norm_num) (by norm_num)
  have hx34 : x3 < x4 := sqrt8_lt_sqrt8 (by norm_num) (by norm_num)
  have hx45 : x4 < x5 := sqrt8_lt_sqrt8 (by norm_num) (by norm_num)
  have hx56 : x5 < x6 := sqrt8_lt_sqrt8 (by norm_num) (by norm_num)
  obtain ⟨r1, hr1, hpr1⟩ := exists_zero_pos_neg hx12 eval_x1_pos eval_x2_neg
  obtain ⟨r2, hr2, hpr2⟩ := exists_zero_neg_pos hx23 eval_x2_neg eval_x3_pos
  obtain ⟨r3, hr3, hpr3⟩ := exists_zero_pos_neg hx34 eval_x3_pos eval_x4_neg
  obtain ⟨r4, hr4, hpr4⟩ := exists_zero_neg_pos hx45 eval_x4_neg eval_x5_pos
  obtain ⟨r5, hr5, hpr5⟩ := exists_zero_pos_neg hx56 eval_x5_pos eval_x6_neg
  have h1r1 : 1 < r1 := h1x1.trans hr1.1
  have hr12 : r1 < r2 := hr1.2.trans hr2.1
  have hr23 : r2 < r3 := hr2.2.trans hr3.1
  have hr34 : r3 < r4 := hr3.2.trans hr4.1
  have hr45 : r4 < r5 := hr4.2.trans hr5.1
  have hr1p : 0 < r1 := by linarith
  have hr2p : 0 < r2 := by linarith
  have hr3p : 0 < r3 := by linarith
  have hr4p : 0 < r4 := by linarith
  have hr5p : 0 < r5 := by linarith
  let ρ : Fin 11 → ℝ := ![1 / r5, 1 / r4, 1 / r3, 1 / r2, 1 / r1, 1, r1, r2, r3, r4, r5]
  have hstep : ∀ i : Fin 10, ρ i.castSucc < ρ i.succ := by
    intro i
    fin_cases i
    · dsimp only [ρ]; exact one_div_lt_one_div_of_lt hr4p hr45
    · dsimp only [ρ]; exact one_div_lt_one_div_of_lt hr3p hr34
    · dsimp only [ρ]; exact one_div_lt_one_div_of_lt hr2p hr23
    · dsimp only [ρ]; exact one_div_lt_one_div_of_lt hr1p hr12
    · dsimp only [ρ]; exact (div_lt_one hr1p).mpr h1r1
    · dsimp only [ρ]; exact h1r1
    · dsimp only [ρ]; exact hr12
    · dsimp only [ρ]; exact hr23
    · dsimp only [ρ]; exact hr34
    · dsimp only [ρ]; exact hr45
  have hmono : StrictMono ρ := Fin.strictMono_iff_lt_succ.mpr hstep
  have hmem : ∀ i : Fin 11, ρ i ∈ P.roots.toFinset.filter (fun x : ℝ => 0 < x) := by
    intro i
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots P_ne_zero]
    fin_cases i
    · exact ⟨eval_inv_zero hr5p.ne' hpr5, div_pos one_pos hr5p⟩
    · exact ⟨eval_inv_zero hr4p.ne' hpr4, div_pos one_pos hr4p⟩
    · exact ⟨eval_inv_zero hr3p.ne' hpr3, div_pos one_pos hr3p⟩
    · exact ⟨eval_inv_zero hr2p.ne' hpr2, div_pos one_pos hr2p⟩
    · exact ⟨eval_inv_zero hr1p.ne' hpr1, div_pos one_pos hr1p⟩
    · exact ⟨eval_P_one, one_pos⟩
    · exact ⟨hpr1, hr1p⟩
    · exact ⟨hpr2, hr2p⟩
    · exact ⟨hpr3, hr3p⟩
    · exact ⟨hpr4, hr4p⟩
    · exact ⟨hpr5, hr5p⟩
  have hsub : Finset.univ.image ρ ⊆ P.roots.toFinset.filter (fun x : ℝ => 0 < x) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact hmem i
  have hcard : (Finset.univ.image ρ).card = 11 := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_fin]
  exact hcard ▸ Finset.card_le_card hsub

end PEqualNP.Outside.L_gct_241

theorem PEqualNP.Outside.L_gct_241 : ¬ (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3)).roots.toFinset.filter (fun x : ℝ => 0 < x)).card ≤ 9) := by
  intro hall
  have h9 := hall PEqualNP.Outside.L_gct_241.sVec PEqualNP.Outside.L_gct_241.gVec
    (fun _ => Or.inl rfl) PEqualNP.Outside.L_gct_241.gVec_support_card_le_two
  have h11 := PEqualNP.Outside.L_gct_241.eleven_pos_roots
  dsimp only [PEqualNP.Outside.L_gct_241.P] at h11
  omega
