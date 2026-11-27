import Mathlib
import PEqualNP.Gct.L097

/-! Helpers for L-gct-218: with `t = Nat.clog 2 n` one has `n ≤ 2 ^ t < 2 n`, the riffle rank
of `pairId (Fin n)` is at most `3 ^ t`, and `3 ^ t` is eventually below `c n ^ 2 / (log₂ n) ^ d`
because `t ^ d / (4 / 3) ^ t → 0`. -/

namespace PEqualNP.Gct.Helpers.RiffleBelow

open Filter Topology

/-- Eventually in `t`, `4 t ^ d 3 ^ t < c 4 ^ t`. -/
theorem eventually_geom (c : ℝ) (d : ℕ) (hc : 0 < c) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → 4 * (t : ℝ) ^ d * 3 ^ t < c * 4 ^ t := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt d (r := (4 / 3 : ℝ)) (by norm_num)
  have hc4 : (0 : ℝ) < c / 4 := by positivity
  have hev := (h.eventually (gt_mem_nhds hc4))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  refine ⟨T, fun t ht => ?_⟩
  have h1 := hT t ht
  have h3 : (0 : ℝ) < 3 ^ t := by positivity
  have h43 : ((4 / 3 : ℝ)) ^ t = 4 ^ t / 3 ^ t := by rw [div_pow]
  rw [h43, div_div_eq_mul_div, div_lt_iff₀ (by positivity)] at h1
  nlinarith

/-- For `n ≥ 2` and `t = Nat.clog 2 n`: `n ≤ 2 ^ t` and `2 ^ t < 2 n`. -/
theorem clog_bounds {n : ℕ} (hn : 2 ≤ n) :
    n ≤ 2 ^ Nat.clog 2 n ∧ 2 ^ Nat.clog 2 n < 2 * n := by
  refine ⟨Nat.le_pow_clog (by norm_num) n, ?_⟩
  have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn
  have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by simpa [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self (b := 2) (x := n) (by omega)
  have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem main : ∀ (F : Type) [Field F] (c : ℝ) (d : ℕ), 0 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ r : ℕ, (r : ℝ) < c * (n : ℝ) ^ 2 / (Real.logb 2 (n : ℝ)) ^ d ∧
      PEqualNP.RiffleRank.RiffleRankLe r (PEqualNP.RiffleRank.pairId (Fin n) F) := by
  intro F _ c d hc
  obtain ⟨T, hT⟩ := eventually_geom c d hc
  refine ⟨max 2 (2 ^ T), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hnT : 2 ^ T ≤ n := le_of_max_le_right hn
  set t := Nat.clog 2 n with ht
  obtain ⟨hle, hlt⟩ := clog_bounds hn2
  have hTt : T ≤ t := by
    rw [ht, ← Nat.clog_pow 2 T (by norm_num)]
    exact Nat.clog_mono_right 2 hnT
  refine ⟨3 ^ t, ?_, PEqualNP.Gct.L097 F n t hle⟩
  have key := hT t hTt
  -- real facts
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hleR : (n : ℝ) ≤ 2 ^ t := by exact_mod_cast hle
  have hltR : (2 : ℝ) ^ t < 2 * n := by exact_mod_cast hlt
  have hlogpos : 0 < Real.logb 2 (n : ℝ) :=
    Real.logb_pos (by norm_num) (by linarith)
  have hlogle : Real.logb 2 (n : ℝ) ≤ t := by
    have : Real.logb 2 ((2 : ℝ) ^ t) = t := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    rw [← this]
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hleR
  have hpowle : (Real.logb 2 (n : ℝ)) ^ d ≤ (t : ℝ) ^ d :=
    pow_le_pow_left₀ hlogpos.le hlogle d
  have hlogdpos : 0 < (Real.logb 2 (n : ℝ)) ^ d := pow_pos hlogpos d
  rw [lt_div_iff₀ hlogdpos]
  have h4 : (4 : ℝ) ^ t = (2 ^ t) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  have hsq : (4 : ℝ) ^ t < 4 * (n : ℝ) ^ 2 := by
    rw [h4]; nlinarith
  have h3 : (0 : ℝ) < 3 ^ t := by positivity
  push_cast
  calc (3 : ℝ) ^ t * Real.logb 2 (n : ℝ) ^ d ≤ 3 ^ t * (t : ℝ) ^ d :=
        mul_le_mul_of_nonneg_left hpowle h3.le
    _ < c * (n : ℝ) ^ 2 := by nlinarith

end PEqualNP.Gct.Helpers.RiffleBelow
