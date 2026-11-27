import PEqualNP.ProofComplexity.Helpers.DegSizeArith
import PEqualNP.ProofComplexity.Helpers.DegSizeGainK
import PEqualNP.ProofComplexity.Helpers.LinKOne
import PEqualNP.ProofComplexity.Helpers.LinKPlan

/-!
# Helpers: the arithmetic of the degree to size theorem for inputs of degree `k`

The degree `k` twin of the arithmetic of `DegSizeArith`. Everything here is about numbers:
the proof system enters only through the assembly inequality, which is a hypothesis, with the
number of lines replaced by a real number `S`.

* `numMono_ratio_iter`, `eta_k_ge`: the binomial estimate
  `(1 / 2) * ((K - k + 1) / (n + 1)) ^ k ≤ eta_k n K k` for `k ≤ K ≤ n + 1`. It fails at
  `K = n + 2` (for `k = 1`: `numMono` is constant from `n` on, so `eta_k = 1 / 2`).
* `eta_k_le_half`, `eta_k_le_one`, `eta_k_nonneg`, `one_sub_eta_k_nonneg`.
* `asm_of_max`: the assembly inequality with budget `K + max (2 t k + 2 k) (t k + w) ≤ D`
  gives the robust form with budget `K + 2 t k + 2 k + w ≤ D` used below.
* `size_of_assembly_k`: for every admissible `K`, `t`:
  `exp (t * ((1 / 2) * ((K - k + 1) / (n + 1)) ^ k)) ≤ S`.
* `final_of_assembly_k`: with `1 ≤ k`, `16 k ≤ D`, `8 w ≤ D`, `D < n`:
  `exp (D / (24 k) * (D / (3 n)) ^ k) ≤ S` (choice `K = D / 2`, `t = D / (8 k)`).
* `final_of_assembly_k_w4`: with `4 w ≤ D` in place of `8 w ≤ D`:
  `exp (D / (24 k) * (D / (6 n)) ^ k) ≤ S` (choice `K = D / 4`, `t = D / (8 k)`).
* `exp_beats_poly_k`: if `n ≤ A * D` then `n / (24 k A (c A) ^ k) ≤ D / (24 k) * (D / (c n)) ^ k`.
* `final_linear_k`, `pow_le_exp_lin`, `final_superpoly_k`: the exponent is linear in `n`, so
  `S` exceeds `n ^ d` as soon as `(d + 1)! / c ^ (d + 1) ≤ n`, with `c = 1 / (24 k A (3 A) ^ k)`.

* `linK_refutation_unsat`: soundness of Res(k, ⊕) with termwise weakening (a statement of
  `LinKPlan`, proved here because the arithmetic link needs `D < card V`).
* `etaK_le_one`, `etaK_ge`, `final_of_assembly_plan`: the three arithmetic statements of
  `LinKPlan`, as stated there; the last from `final_plan_num` (budget in the `max` form,
  `K = D / 2`, `t = D / (4 k) - 1`, `4 w ≤ D`): `exp (D / (16 k) * (D / (4 n)) ^ k) ≤ S`.

At `k = 1` the bound of `final_of_assembly_k` is `exp (D ^ 2 / (72 n))`, under `16 ≤ D` and
`8 w ≤ D`; the checked `final_of_assembly_256` has `exp (D ^ 2 / (256 n))` under `32 ≤ D` and
`2 w ≤ D`. So the constant here is better, the width condition is stronger.
-/

namespace PEqualNP.ProofComplexity.DegSizeArithK

open PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan
open PEqualNP.ProofComplexity.DegSizeGainK (eta_k)

/-! ## The binomial estimate -/

/-- The counting core, iterated `k` times, over the naturals. -/
theorem numMono_ratio_iter (n j k : ℕ) (h : j + k ≤ n + 1) :
    (j + 1) ^ k * numMono n (j + k) ≤ (n + 1) ^ k * numMono n j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hr := DegSizeArith.numMono_ratio n (j + k) (by omega)
    calc (j + 1) ^ (k + 1) * numMono n (j + (k + 1))
        = (j + 1) ^ k * ((j + 1) * numMono n (j + k + 1)) := by
          rw [show j + (k + 1) = j + k + 1 from rfl]; ring
      _ ≤ (j + 1) ^ k * ((j + k + 1) * numMono n (j + k + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ (j + 1) ^ k * ((n + 1) * numMono n (j + k)) := Nat.mul_le_mul_left _ hr
      _ = (n + 1) * ((j + 1) ^ k * numMono n (j + k)) := by ring
      _ ≤ (n + 1) * ((n + 1) ^ k * numMono n j) := Nat.mul_le_mul_left _ ih'
      _ = (n + 1) ^ (k + 1) * numMono n j := by ring

theorem eta_k_nonneg (n K k : ℕ) : 0 ≤ eta_k n K k := by
  unfold eta_k
  positivity

theorem eta_k_le_half (n K k : ℕ) : eta_k n K k ≤ 1 / 2 := by
  unfold eta_k
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeArith.numMono_pos n K
  have hle : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem eta_k_le_one (n K k : ℕ) : eta_k n K k ≤ 1 :=
  (eta_k_le_half n K k).trans (by norm_num)

theorem one_sub_eta_k_nonneg (n K k : ℕ) : 0 ≤ 1 - eta_k n K k := by
  have := eta_k_le_one n K k
  linarith

/-- The binomial estimate at degree `k`: `η_k ≥ (1/2) ((K - k + 1) / (n + 1))^k` for
`k ≤ K ≤ n + 1`. The subtraction is the truncated one of the naturals, under `k ≤ K`. -/
theorem eta_k_ge (n K k : ℕ) (hk : k ≤ K) (hK : K ≤ n + 1) :
    (1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k ≤ eta_k n K k := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + k := ⟨K - k, by omega⟩
  have hnat := numMono_ratio_iter n j k hK
  unfold eta_k
  rw [Nat.add_sub_cancel]
  have hN : (0 : ℝ) < numMono n (j + k) := by
    exact_mod_cast DegSizeArith.numMono_pos n (j + k)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : ((j : ℝ) + 1) ^ k * (numMono n (j + k) : ℝ)
      ≤ ((n : ℝ) + 1) ^ k * (numMono n j : ℝ) := by exact_mod_cast hnat
  push_cast
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hn k) (by linarith)]
  nlinarith [hr]

/-! ## From the assembly inequality to a size bound -/

/-- The assembly inequality with the budget in the `max` form gives the robust form. -/
theorem asm_of_max (n k w D : ℕ) (S : ℝ)
    (h : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D → 1 ≤ S * (1 - eta_k n K k) ^ t := by
  intro K t hk hb
  apply h K t hk
  have e : 2 * t * k = t * k + t * k := by ring
  rw [e] at hb ⊢
  rcases max_cases (t * k + t * k + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
    rw [h'] <;> omega

/-- One use of `1 - x ≤ exp (-x)`. -/
theorem exp_le_of_one_le (S x : ℝ) (t : ℕ) (hx : x ≤ 1) (h : 1 ≤ S * (1 - x) ^ t) :
    Real.exp ((t : ℝ) * x) ≤ S := by
  have hp0 : (0 : ℝ) ≤ (1 - x) ^ t := pow_nonneg (by linarith) t
  have hS : 0 ≤ S := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hp0
    linarith
  have hpow : (1 - x) ^ t ≤ Real.exp (-((t : ℝ) * x)) := by
    have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have h2 : (1 - x) ^ t ≤ Real.exp (-x) ^ t := pow_le_pow_left₀ (by linarith) h1 t
    rw [← Real.exp_nat_mul] at h2
    rwa [mul_neg] at h2
  have h3 : 1 ≤ S * Real.exp (-((t : ℝ) * x)) :=
    h.trans (mul_le_mul_of_nonneg_left hpow hS)
  have hpos : 0 < Real.exp ((t : ℝ) * x) := Real.exp_pos _
  calc Real.exp ((t : ℝ) * x) = Real.exp ((t : ℝ) * x) * 1 := (mul_one _).symm
    _ ≤ Real.exp ((t : ℝ) * x) * (S * Real.exp (-((t : ℝ) * x))) :=
        mul_le_mul_of_nonneg_left h3 hpos.le
    _ = S * (Real.exp ((t : ℝ) * x) * Real.exp (-((t : ℝ) * x))) := by ring
    _ = S := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- The size bound from one instance of the assembly inequality. -/
theorem size_core (n k K t : ℕ) (S : ℝ) (hkK : k ≤ K) (hKn : K ≤ n + 1)
    (h : 1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S := by
  have h1 := exp_le_of_one_le S (eta_k n K k) t (eta_k_le_one n K k) h
  refine le_trans (Real.exp_le_exp.mpr ?_) h1
  exact mul_le_mul_of_nonneg_left (eta_k_ge n K k hkK hKn) (Nat.cast_nonneg t)

/-- The size bound for any admissible choice of `K` and `t`. -/
theorem size_of_assembly_k (n k w D : ℕ) (S : ℝ)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K t : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hbud : K + 2 * t * k + 2 * k + w ≤ D) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S :=
  size_core n k K t S hkK hKn (hasm K t hkK hbud)

/-- The common part of the two final theorems: `t = D / (8 k)`, any `K` that leaves room for
it, and any `r` below `(K - k + 1) / (n + 1)`. -/
theorem final_aux (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hKw : 8 * K + 8 * w ≤ 5 * D)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ ((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * r ^ k) ≤ S := by
  obtain ⟨t, ht⟩ : ∃ t, t = D / (8 * k) := ⟨_, rfl⟩
  have htk : t * (8 * k) ≤ D := by rw [ht]; exact Nat.div_mul_le_self D (8 * k)
  have ht2 : 2 ≤ t := by rw [ht]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 8 * k * (t + 1) := by rw [ht]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : t * (8 * k) = 8 * (t * k) := by ring
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have e3 : 8 * k * (t + 1) = 8 * (t * k) + 8 * k := by ring
  have h2k : 2 * k ≤ t * k := Nat.mul_le_mul_right k ht2
  have hbud : K + 2 * t * k + 2 * k + w ≤ D := by rw [e2]; omega
  have hDt : D ≤ 12 * (t * k) := by omega
  have hcore := size_of_assembly_k n k w D S hasm K t hkK hKn hbud
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDtR : (D : ℝ) ≤ 12 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have h1 : (D : ℝ) / (24 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hk24 : (0 : ℝ) ≤ (D : ℝ) / (24 * (k : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (24 * (k : ℝ)) * r ^ k
      ≤ (t : ℝ) / 2 * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring

/-- The final theorem from the assembly inequality, width up to `D / 8`:
`S ≥ exp (D / (24 k) * (D / (3 n))^k)`. Choice `K = D / 2`, `t = D / (8 k)`. -/
theorem final_of_assembly_k (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (3 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 7 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (3 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr

/-- The final theorem from the assembly inequality, width up to `D / 4`:
`S ≥ exp (D / (24 k) * (D / (6 n))^k)`. Choice `K = D / 4`, `t = D / (8 k)`. -/
theorem final_of_assembly_k_w4 (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (6 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 4 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 3 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 3 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (6 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr

/-! ## The exponent is linear in `n` when `n ≤ A * D` -/

/-- If `n ≤ A * D` then the exponent `D / (24 k) * (D / (c n))^k` is at least
`n / (24 k A (c A)^k)`. -/
theorem exp_beats_poly_k (n k A D c : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hn : 1 ≤ n)
    (hA : n ≤ A * D) :
    (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hAR : (n : ℝ) ≤ (A : ℝ) * (D : ℝ) := by exact_mod_cast hA
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h24 : (0 : ℝ) < 24 * (k : ℝ) := by linarith
  have h24A : (0 : ℝ) < 24 * (k : ℝ) * (A : ℝ) := mul_pos h24 hA0
  have hcA : (0 : ℝ) < (c : ℝ) * (A : ℝ) := mul_pos hc0 hA0
  have hcn : (0 : ℝ) < (c : ℝ) * (n : ℝ) := mul_pos hc0 hn0
  have h1 : (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) ≤ (D : ℝ) / (24 * (k : ℝ)) := by
    rw [div_le_div_iff₀ h24A h24]
    nlinarith [mul_le_mul_of_nonneg_left hAR h24.le]
  have h2 : 1 / ((c : ℝ) * (A : ℝ)) ≤ (D : ℝ) / ((c : ℝ) * (n : ℝ)) := by
    rw [div_le_div_iff₀ hcA hcn]
    nlinarith [mul_le_mul_of_nonneg_left hAR hc0.le]
  have h3 : (0 : ℝ) ≤ 1 / ((c : ℝ) * (A : ℝ)) := by positivity
  calc (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      = (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) * (1 / ((c : ℝ) * (A : ℝ))) ^ k := by
        rw [one_div_pow, div_mul_div_comm, mul_one]
    _ ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ h3 h2 k) (pow_nonneg h3 k) (div_nonneg hD0 h24.le)

/-- The size bound with an exponent linear in `n`, for `n ≤ A * D`. -/
theorem final_linear_k (n k w D A : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) * (n : ℝ)) ≤ S := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (final_of_assembly_k n k w D S hk hkD hwD hDn hasm)
  have h := exp_beats_poly_k n k A D 3 hk (by norm_num) (by omega) hA
  push_cast at h
  rw [one_div_mul_eq_div]
  exact h

/-- An exponential with a linear exponent exceeds `n ^ d` from an explicit point on. -/
theorem pow_le_exp_lin (c : ℝ) (hc : 0 < c) (d n : ℕ)
    (hn : ((d + 1).factorial : ℝ) / c ^ (d + 1) ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ Real.exp (c * (n : ℝ)) := by
  have hx : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
  have h := Real.pow_div_factorial_le_exp _ hx (d + 1)
  refine le_trans ?_ h
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [le_div_iff₀ hF]
  have hn' : ((d + 1).factorial : ℝ) ≤ (n : ℝ) * c ^ (d + 1) :=
    (div_le_iff₀ (pow_pos hc _)).mp hn
  calc (n : ℝ) ^ d * ((d + 1).factorial : ℝ) ≤ (n : ℝ) ^ d * ((n : ℝ) * c ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = (c * (n : ℝ)) ^ (d + 1) := by ring

/-- The size exceeds every fixed power of `n`, from an explicit point on, when `n ≤ A * D`. -/
theorem final_superpoly_k (n k w D A d : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (hn : ((d + 1).factorial : ℝ) / (1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) ^ (d + 1)
      ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ S := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hc : (0 : ℝ) < 1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k) := by positivity
  exact (pow_le_exp_lin _ hc d n hn).trans (final_linear_k n k w D A S hk hkD hwD hDn hA hasm)

/-! ## The three arithmetic links of `LinKPlan`, as stated there -/

section Plan

/-- Soundness of the complement: an assignment satisfying `e` falsifies `negLinEq e`. -/
theorem negLinEq_not_sat {V : Type} (a : V → Bool) (e : LinEq V) (h : LinEqSat a e) :
    ¬ LinEqSat a (negLinEq e) := by
  unfold LinEqSat at h
  unfold LinEqSat negLinEq
  intro h'
  cases hb : e.2 <;> simp_all

theorem linK_cut_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKCut C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) : LinKLineSat a R := by
  obtain ⟨T, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases hTT : T' = T
  · subst hTT
    refine ⟨U, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hU, ?_⟩), hsU⟩
    intro hmem
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    exact negLinEq_not_sat a e (hs' e he) (hsU _ (Finset.mem_singleton_self _))
  · exact ⟨T', Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT'⟩), hs'⟩

theorem linK_andIntro_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) :
    LinKLineSat a R := by
  obtain ⟨T₁, T₂, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases h1 : T' = T₁
  · by_cases h2 : U = T₂
    · subst h1 h2
      refine ⟨T' ∪ U, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hs' q hq
      · exact hsU q hq
    · exact ⟨U, Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2, hU⟩)), hsU⟩
  · exact ⟨T', Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1, hT'⟩)), hs'⟩

theorem linK_derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {k : ℕ}
    {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) (ha : ∀ C ∈ F, LinKLineSat a C) :
    ∀ C ∈ π, LinKLineSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | cut _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_cut_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | andIntro _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_andIntro_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | weak _ hC hw _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact LinKOne.weakening_sound hw (ih _ hC)
    · exact ih E hE

/-- Soundness of Res(k, ⊕) with termwise weakening. This is the statement of `LinKPlan`
headed "Soundness of Res(k, ⊕)"; it is proved here because the arithmetic link needs it. -/
theorem linK_refutation_unsat :
    ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (π : List (LinKLine V)),
      IsLinKRefutation k F π → ¬ Satisfiable F := by
  rintro V _ F k π h ⟨a, ha⟩
  have hax : ∀ C ∈ (fun C => linKOfClause C) '' F, LinKLineSat a C := by
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨l, hl, hs⟩ := ha C hC
    refine ⟨{(({l.1} : Finset V), l.2)},
      Finset.mem_image.mpr ⟨(({l.1} : Finset V), l.2), Finset.mem_image.mpr ⟨l, hl, rfl⟩, rfl⟩,
      ?_⟩
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact (linEqSat_singleton a l.1 l.2).mpr hs
  obtain ⟨T, hT, -⟩ := linK_derivation_sound a h.1 hax ∅ h.2
  exact absurd hT (Finset.notMem_empty T)

/-- `LinKPlan`, "etaK is at most one", as stated there. -/
theorem etaK_le_one : ∀ n K k : ℕ, LinKPlan.etaK n K k ≤ 1 :=
  fun n K k => eta_k_le_one n K k

/-- `LinKPlan`, "The binomial estimate", as stated there. -/
theorem etaK_ge :
    ∀ n K k : ℕ, k ≤ K → K ≤ n + 1 →
      (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k) ≤ LinKPlan.etaK n K k := by
  intro n K k hk hK
  have h := eta_k_ge n K k hk hK
  rw [div_pow] at h
  have e : (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k)
      = (1 / 2 : ℝ) * ((((K - k + 1 : ℕ) : ℝ)) ^ k / ((n : ℝ) + 1) ^ k) := by ring
  rw [e]
  exact h

/-- The arithmetic of the plan, about numbers only: budget in the `max` form, `K = D / 2`,
`t = D / (4 k) - 1`, width up to `D / 4`. -/
theorem final_plan_num (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = D / (4 * k) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = q - 1 := ⟨_, rfl⟩
  have hqk : q * (4 * k) ≤ D := by rw [hq]; exact Nat.div_mul_le_self D (4 * k)
  have hq4 : 4 ≤ q := by rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 4 * k * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : q * (4 * k) = 4 * (q * k) := by ring
  have e3 : 4 * k * (q + 1) = 4 * (q * k) + 4 * k := by ring
  have h4k : 4 * k ≤ q * k := Nat.mul_le_mul_right k hq4
  have etk : t * k = q * k - k := by rw [ht, Nat.sub_mul, one_mul]
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have hbud : K + max (2 * t * k + 2 * k) (t * k + w) ≤ D := by
    rw [e2]
    rcases max_cases (2 * (t * k) + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      rw [h'] <;> omega
  have hDt : D ≤ 8 * (t * k) := by omega
  have haD : 7 * D ≤ 16 * a := by omega
  have hcore := size_core n k K t S (by omega) (by omega) (hasm K t (by omega) hbud)
  rw [← ha] at hcore
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDtR : (D : ℝ) ≤ 8 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have h1 : (D : ℝ) / (16 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hr : (D : ℝ) / (4 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  have hr0 : (0 : ℝ) ≤ (D : ℝ) / (4 * (n : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k
      ≤ (t : ℝ) / 2 * ((a : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * ((a : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring

/-- `LinKPlan`, "The arithmetic: the final bound from the assembly inequality", as stated
there. -/
theorem final_of_assembly_plan :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
      (k w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
      ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
      (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - LinKPlan.etaK (Fintype.card V) K k) ^ t) →
      Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
        ≤ (π.length : ℝ) := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href hasm
  have hunsat : ¬ Satisfiable F := linK_refutation_unsat V F k π href
  have hDn : D < Fintype.card V := by
    by_contra hcon
    exact hnr (DegSizeArith.complete_deg V F w D hw hunsat (by omega) (by omega))
  exact final_plan_num (Fintype.card V) k w D _ hk hkD hwD hDn hasm

end Plan

end PEqualNP.ProofComplexity.DegSizeArithK
