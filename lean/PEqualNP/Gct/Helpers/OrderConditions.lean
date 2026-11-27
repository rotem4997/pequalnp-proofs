import PEqualNP.Defs
import PEqualNP.Gct.Helpers.MRPlusOne

/-! Helper module, proofs only. First and second order conditions for a polynomial vanishing on
a line: if `p` vanishes at `y + s • t` for every scalar `s`, then the gradient of `p` at `y`
kills `t` and the Hessian quadratic form of `p` at `y` vanishes at `t`. -/

namespace PEqualNP.Gct.Helpers.OrderCond

open MvPolynomial Finset PEqualNP.Gct.Helpers

variable {σ : Type} [Fintype σ]

/-- The derivative of `s ↦ p (y + s • t)` is the directional derivative of `p` along `t`. -/
theorem hasDerivAt_eval_line (p : MvPolynomial σ ℂ) (y t : σ → ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => eval (y + s • t) p)
      (∑ a, eval (y + s • t) (pderiv a p) * t a) s := by
  classical
  have h1 := (hasStrictFDerivAt_eval_gen p (y + s • t)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℂ => y + s • t) t s := by
    simpa using ((hasDerivAt_id s).smul_const t).const_add y
  have h3 := h1.comp_hasDerivAt s h2
  rw [gradCLMg_apply] at h3
  have e : ∑ a, eval (y + s • t) (pderiv a p) * t a
      = ∑ a, t a * eval (y + s • t) (pderiv a p) :=
    Finset.sum_congr rfl (fun a _ => mul_comm (eval (y + s • t) (pderiv a p)) (t a))
  rw [e]
  exact h3

/-- If `p` vanishes on the whole line `y + s • t`, the first and second order terms of `p` at
`y` in the direction `t` vanish. -/
theorem order_conditions_of_vanish_on_line (p : MvPolynomial σ ℂ) (y t : σ → ℂ)
    (h : ∀ s : ℂ, eval (y + s • t) p = 0) :
    (∑ a, eval y (pderiv a p) * t a = 0) ∧
      (∑ a, ∑ b, eval y (pderiv a (pderiv b p)) * t a * t b = 0) := by
  have hg : ∀ s : ℂ, ∑ a, eval (y + s • t) (pderiv a p) * t a = 0 := fun s => by
    have h1 := hasDerivAt_eval_line p y t s
    have h2 : HasDerivAt (fun s : ℂ => eval (y + s • t) p) 0 s := by
      rw [show (fun s : ℂ => eval (y + s • t) p) = fun _ => (0 : ℂ) from funext h]
      exact hasDerivAt_const s 0
    exact h1.unique h2
  refine ⟨by simpa using hg 0, ?_⟩
  have h1 : HasDerivAt (fun s : ℂ => ∑ a, eval (y + s • t) (pderiv a p) * t a)
      (∑ a, (∑ b, eval (y + (0 : ℂ) • t) (pderiv b (pderiv a p)) * t b) * t a) 0 :=
    HasDerivAt.fun_sum (fun a _ => (hasDerivAt_eval_line (pderiv a p) y t 0).mul_const (t a))
  have h2 : HasDerivAt (fun s : ℂ => ∑ a, eval (y + s • t) (pderiv a p) * t a) 0 0 := by
    rw [show (fun s : ℂ => ∑ a, eval (y + s • t) (pderiv a p) * t a) = fun _ => (0 : ℂ)
      from funext hg]
    exact hasDerivAt_const 0 0
  have h3 := h1.unique h2
  rw [zero_smul, add_zero] at h3
  rw [← h3]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [pderiv_comm]
  ring

end PEqualNP.Gct.Helpers.OrderCond
