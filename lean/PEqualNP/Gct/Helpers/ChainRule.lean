import Mathlib

/-! Chain rule for partial derivatives under substitution of variables. Helper for
L-gct-012 and L-gct-014. -/

namespace PEqualNP.Gct.Helpers

open MvPolynomial Finset

variable {σ τ R : Type} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- First-order chain rule: `∂_b (p ∘ φ) = ∑ i, (∂_i p) ∘ φ * ∂_b φ_i`. -/
theorem pderiv_bind₁ (φ : σ → MvPolynomial τ R) (b : τ) (p : MvPolynomial σ R) :
    pderiv b (bind₁ φ p) = ∑ i, bind₁ φ (pderiv i p) * pderiv b (φ i) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, bind₁_X_right, Derivation.leibniz, hp]
    have : ∀ j, bind₁ φ (pderiv j (p * X i)) * pderiv b (φ j) =
        φ i * (bind₁ φ (pderiv j p) * pderiv b (φ j)) +
          (if j = i then bind₁ φ p * pderiv b (φ j) else 0) := by
      intro j
      rw [Derivation.leibniz, pderiv_X]
      by_cases h : j = i
      · subst h; simp; ring
      · simp [h, Pi.single_apply]; ring
    rw [sum_congr rfl fun j _ => this j, sum_add_distrib, ← mul_sum, sum_ite_eq']
    simp [smul_eq_mul]
    ring


/-- The Hessian matrix of `p` at `x`. -/
noncomputable def hess {ι : Type} (p : MvPolynomial ι ℂ) (x : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => eval x (pderiv a (pderiv b p))

/-- Second-order chain rule for a substitution whose partial derivatives are constants. -/
theorem pderiv_pderiv_bind₁ (φ : σ → MvPolynomial τ R) (c : σ → τ → R)
    (hc : ∀ i a, pderiv a (φ i) = C (c i a)) (a b : τ) (p : MvPolynomial σ R) :
    pderiv a (pderiv b (bind₁ φ p)) =
      ∑ i, ∑ j, C (c i b) * C (c j a) * bind₁ φ (pderiv j (pderiv i p)) := by
  rw [pderiv_bind₁, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [hc, Derivation.leibniz, pderiv_C, smul_zero, zero_add, pderiv_bind₁, smul_eq_mul,
    mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [hc]; ring

theorem hess_bind₁ {σ τ : Type} [Fintype σ] [DecidableEq σ] (φ : σ → MvPolynomial τ ℂ)
    (c : σ → τ → ℂ) (hc : ∀ i a, pderiv a (φ i) = C (c i a)) (p : MvPolynomial σ ℂ)
    (y : τ → ℂ) :
    hess (bind₁ φ p) y = (Matrix.of c).transpose * hess p (fun i => eval y (φ i)) * Matrix.of c := by
  ext a b
  simp only [hess, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    pderiv_pderiv_bind₁ φ c hc, map_sum, map_mul, eval_C, sum_mul]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have hev : eval y (bind₁ φ (pderiv j (pderiv i p))) =
      eval (fun i => eval y (φ i)) (pderiv j (pderiv i p)) := by
    show eval₂Hom (RingHom.id ℂ) y _ = _
    rw [eval₂Hom_bind₁]
    rfl
  rw [hev]
  ring

theorem rank_hess_bind₁_le {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ]
    (φ : σ → MvPolynomial τ ℂ) (c : σ → τ → ℂ) (hc : ∀ i a, pderiv a (φ i) = C (c i a))
    (p : MvPolynomial σ ℂ) (y : τ → ℂ) :
    (hess (bind₁ φ p) y).rank ≤ (hess p (fun i => eval y (φ i))).rank := by
  rw [hess_bind₁ φ c hc]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end PEqualNP.Gct.Helpers
