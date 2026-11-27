import Mathlib
import PEqualNP.Defs

/-!
# Tangent space of a smooth polynomial hypersurface

A polynomial `q` vanishing near `x` on the hypersurface `{p = 0}`, smooth at `x`, has
directional derivative zero along every tangent vector of the hypersurface at `x`.
The proof uses the inverse function theorem.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial Filter Topology

/-- The gradient of `p` at `x`, as a continuous linear functional. -/
noncomputable def gradCLM {k : ℕ} (p : MvPolynomial (Fin k) ℂ) (x : Fin k → ℂ) :
    (Fin k → ℂ) →L[ℂ] ℂ :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

theorem gradCLM_apply {k : ℕ} (p : MvPolynomial (Fin k) ℂ) (x v : Fin k → ℂ) :
    gradCLM p x v = ∑ i, v i * eval x (pderiv i p) := by
  simp [gradCLM, mul_comm]

/-- Evaluation of a multivariate polynomial has strict derivative given by the partials. -/
theorem hasStrictFDerivAt_eval {k : ℕ} (p : MvPolynomial (Fin k) ℂ) (x : Fin k → ℂ) :
    HasStrictFDerivAt (fun y => eval y p) (gradCLM p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : gradCLM (C a) x = 0 := by ext v; simp [gradCLM_apply]
    rw [this]; simpa using hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have : gradCLM (p + q) x = gradCLM p x + gradCLM q x := by
      ext v; simp [gradCLM_apply, mul_add, Finset.sum_add_distrib]
    rw [this]; simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    have h1 : HasStrictFDerivAt (fun y : Fin k → ℂ => y i) (ContinuousLinearMap.proj i) x :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).hasStrictFDerivAt
    have : gradCLM (p * X i) x = eval x p • (ContinuousLinearMap.proj i) + x i • gradCLM p x := by
      ext v
      simp only [gradCLM_apply, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, eval_mul,
        add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, eval_X]
      simp only [mul_add, Finset.sum_add_distrib, Pi.single_apply, Finset.mul_sum]
      simp [mul_comm, mul_left_comm]
    rw [this]; convert hp.mul h1 using 1; funext y; simp

theorem pderiv_vanish_of_vanish_on_hypersurface {k : ℕ} (p q : MvPolynomial (Fin k) ℂ)
    (x : Fin k → ℂ)
    (hpx : MvPolynomial.eval x p = 0)
    (hgrad : ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) ≠ 0)
    (hq : ∀ᶠ y in nhds x, MvPolynomial.eval y p = 0 → MvPolynomial.eval y q = 0)
    (t : Fin k → ℂ) (ht : ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0) :
    ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i q) = 0 := by
  obtain ⟨j, hj⟩ := hgrad
  -- the map replacing the `j`-th coordinate by the value of `p`
  set Ψ : (Fin k → ℂ) → (Fin k → ℂ) := fun y i => if i = j then eval y p else y i with hΨ
  set D : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) := ContinuousLinearMap.pi
    (fun i => if i = j then gradCLM p x else ContinuousLinearMap.proj i) with hD
  have hDapply : ∀ v i, D v i = if i = j then gradCLM p x v else v i := by
    intro v i
    by_cases h : i = j <;> simp [hD, h]
  have hΨD : HasStrictFDerivAt Ψ D x := by
    rw [hΨ, hD, hasStrictFDerivAt_pi]
    intro i
    by_cases h : i = j
    · simp only [h, ↓reduceIte]; exact hasStrictFDerivAt_eval p x
    · simp only [h, ↓reduceIte]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i).hasStrictFDerivAt
  have hinj : Function.Injective D.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ i, D v i = 0 := fun i => congrFun hv i
    have hoff : ∀ i, i ≠ j → v i = 0 := by
      intro i hi; have := hv' i; simpa [hDapply, hi] using this
    have hjj := hv' j
    rw [hDapply] at hjj
    simp only [↓reduceIte] at hjj
    rw [gradCLM_apply, Finset.sum_eq_single j] at hjj
    · have hvj : v j = 0 := by
        rcases mul_eq_zero.1 hjj with h | h
        · exact h
        · exact absurd h hj
      funext i
      by_cases hi : i = j
      · subst hi; exact hvj
      · exact hoff i hi
    · intro b _ hb; rw [hoff b hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ j) h
  set E : (Fin k → ℂ) ≃L[ℂ] (Fin k → ℂ) :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv with hE
  have hEcoe : (E : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) = D := by
    ext v i; simp [hE]
  have hΨE : HasStrictFDerivAt Ψ (E : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) x := by
    rw [hEcoe]; exact hΨD
  set g := hΨE.localInverse Ψ E x with hg
  set t' : Fin k → ℂ := fun i => if i = j then 0 else t i with ht'
  have hDt : D t = t' := by
    funext i
    rw [hDapply]
    by_cases h : i = j
    · simp [h, ht', gradCLM_apply, ht]
    · simp [h, ht']
  have hEt : E.symm t' = t := by
    rw [← hDt, ← hEcoe]; simp
  set c : ℂ → (Fin k → ℂ) := fun ε => g (Ψ x + ε • t') with hc
  have hline : HasDerivAt (fun ε : ℂ => Ψ x + ε • t') t' 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const t').const_add (Ψ x)
  have hcd : HasDerivAt c t 0 := by
    have h1 : HasFDerivAt g (E.symm : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ)) (Ψ x + (0 : ℂ) • t') := by
      simpa using hΨE.to_localInverse.hasFDerivAt
    have := h1.comp_hasDerivAt (0 : ℂ) hline
    rw [← hEt]; exact this
  have hlineT : Tendsto (fun ε : ℂ => Ψ x + ε • t') (𝓝 0) (𝓝 (Ψ x)) := by
    simpa using hline.continuousAt.tendsto
  have hc0 : c 0 = x := by simp [hc, hg]
  have hcT : Tendsto c (𝓝 0) (𝓝 x) := by
    have := hcd.continuousAt.tendsto; rwa [hc0] at this
  have hpc : ∀ᶠ ε in 𝓝 (0 : ℂ), eval (c ε) p = 0 := by
    filter_upwards [hlineT.eventually hΨE.eventually_right_inverse] with ε hε
    have h2 : (Ψ x + ε • t') j = 0 := by simp [hΨ, ht', hpx]
    have h3 : Ψ (c ε) j = eval (c ε) p := by simp only [hΨ, ↓reduceIte]
    rw [← h3, ← h2]; exact congrFun hε j
  have hqc : ∀ᶠ ε in 𝓝 (0 : ℂ), eval (c ε) q = 0 := by
    filter_upwards [hpc, hcT.eventually hq] with ε h1 h2 using h2 h1
  have hqd : HasDerivAt (fun ε => eval (c ε) q) (gradCLM q x t) 0 := by
    have h1 : HasFDerivAt (fun y => eval y q) (gradCLM q x) (c 0) := by
      rw [hc0]; exact (hasStrictFDerivAt_eval q x).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) hcd
  have hzero : HasDerivAt (fun ε => eval (c ε) q) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hqc
  have := hqd.unique hzero
  rwa [gradCLM_apply] at this

end PEqualNP.Gct.Helpers
