import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PolarGeneric

/-!
Helpers for L-gct-043: the Fermat form `G = sum_j x_j ^ r` in `h + 2` variables has
`r * (r - 1) ^ h` simple polar points on the chart `x_1 = 1`, exhibited.

Coordinates: index `0` is the free coordinate `y`, index `1` is the chart coordinate `x_1`
(the covector is `a = e_1`), and index `k + 2` is `x_(k + 2)` for `k : Fin h`. The directions are
`v_k = e_1 - alpha e_(k + 2)`, so `D_(v_k) G = r (x_1 ^ (r - 1) - alpha x_(k + 2) ^ (r - 1))`.
With `beta = 1 / (h + 1)` and `alpha = beta ^ (-(r - 1))`, the points are
`(y, 1, zeta_k beta)` with `zeta_k ^ (r - 1) = 1` and `y ^ r = -(1 + beta ^ r * sum_k zeta_k)`;
the right side is nonzero since `beta ^ r * h < 1`. In these coordinates the Jacobian has a
first column that is zero below its top entry, and the remaining minor is lower triangular.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

theorem fermat_pderiv_X_pow {n : ℕ} (i m : Fin n) (s : ℕ) :
    pderiv m (X i ^ s : MvPolynomial (Fin n) ℂ) =
      if i = m then (s : MvPolynomial (Fin n) ℂ) * X i ^ (s - 1) else 0 := by
  rw [Derivation.leibniz_pow]
  split_ifs with h
  · subst h
    rw [pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul]
  · rw [pderiv_X_of_ne h, smul_zero, smul_zero]

theorem fermat_pderiv_G {n : ℕ} (r : ℕ) (i : Fin n) :
    pderiv i (∑ j, X j ^ r : MvPolynomial (Fin n) ℂ) = C (r : ℂ) * X i ^ (r - 1) := by
  rw [map_sum, Finset.sum_eq_single i]
  · rw [fermat_pderiv_X_pow, ite_eq_left rfl, map_natCast]
  · intro j _ hj
    rw [fermat_pderiv_X_pow, ite_eq_right hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem fermat_pderiv_polar {n : ℕ} (r : ℕ) (w : Fin n → ℂ) (m : Fin n) :
    pderiv m (∑ j, C (w j) * pderiv j (∑ j, X j ^ r : MvPolynomial (Fin n) ℂ)) =
      C (w m * (r : ℂ) * ((r - 1 : ℕ) : ℂ)) * X m ^ (r - 1 - 1) := by
  rw [map_sum, Finset.sum_eq_single m]
  · rw [pderiv_C_mul, fermat_pderiv_G, pderiv_C_mul, fermat_pderiv_X_pow, ite_eq_left rfl,
      ← map_natCast (C : ℂ →+* MvPolynomial (Fin n) ℂ) (r - 1)]
    simp only [map_mul]
    ring
  · intro j _ hj
    rw [pderiv_C_mul, fermat_pderiv_G, pderiv_C_mul, fermat_pderiv_X_pow, ite_eq_right hj, mul_zero,
      mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ m) hi

theorem fermat_eval_pderiv_G {n : ℕ} (r : ℕ) (x : Fin n → ℂ) (j : Fin n) :
    eval x (pderiv j (∑ j, X j ^ r : MvPolynomial (Fin n) ℂ)) = (r : ℂ) * x j ^ (r - 1) := by
  rw [fermat_pderiv_G, eval_mul, eval_C, eval_pow, eval_X]

theorem fermat_eval_pderiv_polar {n : ℕ} (r : ℕ) (w : Fin n → ℂ) (x : Fin n → ℂ) (m : Fin n) :
    eval x (pderiv m (∑ j, C (w j) * pderiv j (∑ j, X j ^ r : MvPolynomial (Fin n) ℂ))) =
      w m * (r : ℂ) * ((r - 1 : ℕ) : ℂ) * x m ^ (r - 1 - 1) := by
  rw [fermat_pderiv_polar, eval_mul, eval_C, eval_pow, eval_X]

theorem fermat_eval_polar {n : ℕ} (r : ℕ) (w : Fin n → ℂ) (x : Fin n → ℂ) :
    eval x (∑ j, C (w j) * pderiv j (∑ j, X j ^ r : MvPolynomial (Fin n) ℂ)) =
      ∑ j, w j * ((r : ℂ) * x j ^ (r - 1)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, fermat_eval_pderiv_G]

/-- A determinant criterion: first column zero below the top, nonzero top entry, and the minor
obtained by deleting the first row and column lower triangular with nonzero diagonal. -/
theorem fermat_det_ne_zero {h : ℕ} (M : Matrix (Fin (h + 2)) (Fin (h + 2)) ℂ)
    (h0 : M 0 0 ≠ 0) (hcol : ∀ i : Fin (h + 1), M i.succ 0 = 0)
    (hlow : ∀ i j : Fin (h + 1), i < j → M i.succ j.succ = 0)
    (hdiag : ∀ i : Fin (h + 1), M i.succ i.succ ≠ 0) : M.det ≠ 0 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun i _ => by rw [hcol i, mul_zero, zero_mul]), add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rw [Matrix.det_of_isLowerTriangular]
  · exact mul_ne_zero h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
  · intro i j hij
    exact hlow i j hij

noncomputable def fBeta (h : ℕ) : ℂ := ((h + 1 : ℕ) : ℂ)⁻¹

noncomputable def fAlpha (h r : ℕ) : ℂ := (fBeta h ^ (r - 1))⁻¹

noncomputable def fA (h : ℕ) : Fin (h + 2) → ℂ := Fin.cons 0 (Fin.cons 1 0)

noncomputable def fV (h r : ℕ) : Fin h → Fin (h + 2) → ℂ :=
  fun k => Fin.cons 0 (Fin.cons 1 (fun m => if m = k then -fAlpha h r else 0))

noncomputable def fC (h r : ℕ) (ζ : Fin h → ℂ) : ℂ := 1 + fBeta h ^ r * ∑ k, ζ k

noncomputable def fY (h r : ℕ) (ζ : Fin h → ℂ) : ℂ :=
  if hr : 0 < r then Classical.choose (IsAlgClosed.exists_pow_nat_eq (-fC h r ζ) hr) else 0

noncomputable def fPt (h r : ℕ) (p : (Fin h → ℂ) × ℂ) : Fin (h + 2) → ℂ :=
  Fin.cons (fY h r p.1 * p.2) (Fin.cons 1 (fun k => p.1 k * fBeta h))

noncomputable def fT (h r : ℕ) : Finset ((Fin h → ℂ) × ℂ) :=
  Fintype.piFinset (fun _ : Fin h => Polynomial.nthRootsFinset (r - 1) (1 : ℂ)) ×ˢ
    Polynomial.nthRootsFinset r (1 : ℂ)

noncomputable def fS (h r : ℕ) : Finset (Fin (h + 2) → ℂ) := (fT h r).image (fPt h r)

theorem fBeta_ne_zero (h : ℕ) : fBeta h ≠ 0 := by
  rw [fBeta]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero h))

theorem fY_pow (h r : ℕ) (hr : 0 < r) (ζ : Fin h → ℂ) : fY h r ζ ^ r = -fC h r ζ := by
  rw [fY, dite_eq_left hr]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-fC h r ζ) hr)

theorem fC_ne_zero (h r : ℕ) (hr : 2 ≤ r) (ζ : Fin h → ℂ) (hζ : ∀ k, ζ k ^ (r - 1) = 1) :
    fC h r ζ ≠ 0 := by
  intro h0
  have hn : ∀ k, ‖ζ k‖ = 1 := fun k => Complex.norm_eq_one_of_pow_eq_one (hζ k) (by omega)
  have hs : ‖∑ k, ζ k‖ ≤ h := by
    refine (norm_sum_le _ _).trans ?_
    simp [hn]
  have hb : ‖fBeta h‖ = ((h : ℝ) + 1)⁻¹ := by
    rw [fBeta, norm_inv, RCLike.norm_natCast (K := ℂ)]
    push_cast
    ring
  have hh : (0 : ℝ) < h + 1 := by positivity
  have hb0 : 0 ≤ ‖fBeta h‖ := norm_nonneg _
  have hb1 : ‖fBeta h‖ ≤ 1 := by
    rw [hb]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg h : (0 : ℝ) ≤ h)])
  have hpow : ‖fBeta h‖ ^ r ≤ ‖fBeta h‖ := pow_le_of_le_one hb0 hb1 (by omega)
  have key : fBeta h ^ r * ∑ k, ζ k = -1 := by
    rw [fC] at h0
    linear_combination h0
  have hle : (1 : ℝ) ≤ ‖fBeta h‖ * h := by
    have := congrArg norm key
    rw [norm_mul, norm_pow, norm_neg, norm_one] at this
    rw [← this]
    exact mul_le_mul hpow hs (norm_nonneg _) hb0
  rw [hb, le_inv_mul_iff₀ hh] at hle
  linarith

theorem fY_ne_zero (h r : ℕ) (hr : 2 ≤ r) (ζ : Fin h → ℂ) (hζ : ∀ k, ζ k ^ (r - 1) = 1) :
    fY h r ζ ≠ 0 := by
  intro h0
  have := fY_pow h r (by omega) ζ
  rw [h0, zero_pow (by omega)] at this
  exact fC_ne_zero h r hr ζ hζ (by linear_combination this)

theorem mem_fT (h r : ℕ) (hr : 2 ≤ r) (p : (Fin h → ℂ) × ℂ) :
    p ∈ fT h r ↔ (∀ k, p.1 k ^ (r - 1) = 1) ∧ p.2 ^ r = 1 := by
  rw [fT, Finset.mem_product, Fintype.mem_piFinset]
  simp only [Polynomial.mem_nthRootsFinset (by omega : 0 < r - 1),
    Polynomial.mem_nthRootsFinset (by omega : 0 < r)]

theorem fPt_injOn (h r : ℕ) (hr : 2 ≤ r) : Set.InjOn (fPt h r) (fT h r) := by
  rintro ⟨ζ, ω⟩ hp ⟨ζ', ω'⟩ _ heq
  have hp' : (ζ, ω) ∈ fT h r := hp
  rw [mem_fT h r hr] at hp'
  have hζ : ζ = ζ' := funext fun k => by
    have := congrFun heq k.succ.succ
    simp only [fPt, Fin.cons_succ] at this
    exact mul_right_cancel₀ (fBeta_ne_zero h) this
  subst hζ
  have := congrFun heq 0
  simp only [fPt, Fin.cons_zero] at this
  rw [Prod.mk.injEq]
  exact ⟨rfl, mul_left_cancel₀ (fY_ne_zero h r hr ζ hp'.1) this⟩

theorem fS_card (h r : ℕ) (hr : 2 ≤ r) : (fS h r).card = r * (r - 1) ^ h := by
  rw [fS, Finset.card_image_of_injOn (fPt_injOn h r hr), fT, Finset.card_product,
    Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    (Complex.isPrimitiveRoot_exp (r - 1) (by omega)).card_nthRootsFinset,
    (Complex.isPrimitiveRoot_exp r (by omega)).card_nthRootsFinset, mul_comm]

/-- Every exhibited point is a simple zero of the polar system. -/
theorem fS_good (h r : ℕ) (hr : 2 ≤ r) (x : Fin (h + 2) → ℂ) (hx : x ∈ fS h r) :
    (∀ i, MvPolynomial.eval x ((Fin.cons (∑ j, MvPolynomial.X j ^ r) (Fin.cons (∑ j, MvPolynomial.C (fA h j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (fV h r k j) * MvPolynomial.pderiv j (∑ j, MvPolynomial.X j ^ r))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons (∑ j, MvPolynomial.X j ^ r) (Fin.cons (∑ j, MvPolynomial.C (fA h j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (fV h r k j) * MvPolynomial.pderiv j (∑ j, MvPolynomial.X j ^ r))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0 := by
  obtain ⟨⟨ζ, ω⟩, hp, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_fT h r hr] at hp
  obtain ⟨hζ, hω⟩ := hp
  simp only at hζ hω
  have hβ := fBeta_ne_zero h
  have hβ' : fBeta h ^ (r - 1) ≠ 0 := pow_ne_zero _ hβ
  have hαβ : fAlpha h r * fBeta h ^ (r - 1) = 1 := inv_mul_cancel₀ hβ'
  have hα : fAlpha h r ≠ 0 := inv_ne_zero hβ'
  have hy := fY_pow h r (by omega) ζ
  have hy0 := fY_ne_zero h r hr ζ hζ
  have hζ0 : ∀ k, ζ k ≠ 0 := fun k h0 => by
    have := hζ k
    rw [h0, zero_pow (by omega)] at this
    exact zero_ne_one this
  have hω0 : ω ≠ 0 := fun h0 => by
    rw [h0, zero_pow (by omega)] at hω
    exact zero_ne_one hω
  have hzr : ∀ k, ζ k ^ r = ζ k := fun k => by
    conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ, hζ k, one_mul]
  refine ⟨fun i => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · simp only [Fin.cons_zero, map_sum, map_pow, eval_X]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [fPt, Fin.cons_zero, Fin.cons_succ]
      rw [mul_pow, hy, hω, one_pow, mul_one]
      have hsum : ∑ k : Fin h, (ζ k * fBeta h) ^ r = fBeta h ^ r * ∑ k, ζ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_pow, hzr k, mul_comm]
      rw [hsum, fC]
      ring
    · simp only [Fin.cons_zero, Fin.cons_succ, map_sub, map_sum, map_mul, eval_C, eval_X,
        map_one]
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp [fA, fPt]
    · simp only [Fin.cons_succ]
      rw [fermat_eval_polar, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [fV, fPt, Fin.cons_zero, Fin.cons_succ, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, one_pow, one_mul, mul_one]
      linear_combination (-(r : ℂ)) * hαβ - fAlpha h r * r * fBeta h ^ (r - 1) * hζ k
  · have hr1 : ((r - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply fermat_det_ne_zero
    · simp only [Matrix.of_apply, Fin.cons_zero]
      rw [fermat_eval_pderiv_G]
      simp only [fPt, Fin.cons_zero]
      exact mul_ne_zero hr0 (pow_ne_zero _ (mul_ne_zero hy0 hω0))
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
        rw [eval_pderiv_affine]
        rfl
      · simp only [Matrix.of_apply, Fin.cons_succ]
        rw [fermat_eval_pderiv_polar]
        simp [fV]
    · intro i j
      refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        intro hij
      · exact absurd hij (lt_irrefl _)
      · simp only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
        rw [eval_pderiv_affine]
        rfl
      · exact absurd hij (Fin.not_lt_zero _)
      · simp only [Matrix.of_apply, Fin.cons_succ]
        rw [fermat_eval_pderiv_polar]
        have hne : j' ≠ k := fun he => by
          subst he
          exact lt_irrefl _ hij
        simp [fV, hne]
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
        rw [eval_pderiv_affine]
        simp [fA]
      · simp only [Matrix.of_apply, Fin.cons_succ]
        rw [fermat_eval_pderiv_polar]
        simp only [fV, fPt, Fin.cons_succ, ↓reduceIte]
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hα) hr0) hr1)
          (pow_ne_zero _ (mul_ne_zero (hζ0 k) hβ))

end PEqualNP.Gct.Helpers
