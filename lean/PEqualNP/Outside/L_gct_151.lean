import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_151 :
    ∀ (q : ℕ) (Z : Submodule ℂ (Fin q → ℂ)) (y : Fin q → ℂ), y ∈ Z →
    (Finset.univ.sum fun j : Fin q => y j) ≠ 0 →
    (∀ y' ∈ Z, (Finset.univ.sum fun j : Fin q => y' j) ≠ 0 →
      (∀ j : Fin q, y j = 0 → y' j = 0) → ∀ j : Fin q, y' j = 0 → y j = 0) →
    ∀ x ∈ Z, (∀ j : Fin q, y j = 0 → x j = 0) → ∃ c : ℂ, x = c • y := by
  intro q Z y hy hsum hmin x hx hsupp
  let c := (∑ j, x j) / (∑ j, y j)
  let u := x - c • y
  have hu : u ∈ Z := Z.sub_mem hx (Z.smul_mem c hy)
  have husum : ∑ j, u j = 0 := by
    simp only [u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, c, div_mul_cancel₀ _ hsum, sub_self]
  have husupp (j : Fin q) (hj : y j = 0) : u j = 0 := by
    simp [u, hj, hsupp j hj]
  refine ⟨c, ?_⟩
  funext j
  by_contra h
  have hj : u j ≠ 0 := sub_ne_zero.mpr h
  -- A zero-sum direction can cancel coordinate j while preserving the sum.
  let d := y j / u j
  let v := y - d • u
  have hv : v ∈ Z := Z.sub_mem hy (Z.smul_mem d hu)
  have hvsum : ∑ i, v i ≠ 0 := by
    simpa only [v, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, husum, mul_zero, sub_zero] using hsum
  have hvsupp (i : Fin q) (hi : y i = 0) : v i = 0 := by
    simp [v, hi, husupp i hi]
  have hvj : v j = 0 := sub_eq_zero.mpr (div_mul_cancel₀ (y j) hj).symm
  exact hj (husupp j (hmin v hv hvsum hvsupp j hvj))
