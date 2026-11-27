import PEqualNP.Defs
import PEqualNP.Gct.L003
import PEqualNP.Gct.Helpers.MignonRessayre
import PEqualNP.Gct.Helpers.MRPlusOne
import PEqualNP.Gct.Helpers.Pointwise
import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Gct.Helpers.HessKernel

/-! The border Mignon-Ressayre bound (helper for L-gct-010). If `perm_m` is a coefficientwise
limit of polynomials `q k` with determinantal expressions of size `n`, the smooth zero `y` of the
permanent with nondegenerate Hessian persists: by the inverse function theorem in the space of
(coefficients, line parameter) there are zeros `x k` of `q k` with `x k → y`. The Hessians of
`q k` at `x k` tend to the Hessian of `perm_m` at `y`, so one of them is invertible, and the rank
bound of L-gct-014 at a zero gives `m² ≤ 2n`. -/

namespace PEqualNP.Gct.Helpers.BorderMR

open MvPolynomial Filter Topology Finset PEqualNP.Gct.Helpers

section Support

variable {σ : Type}

/-- A polynomial supported in `S` is the sum of its monomials over `S`. -/
theorem eq_sum_monomial (S : Finset (σ →₀ ℕ)) (q : MvPolynomial σ ℂ)
    (hS : ∀ s, s ∉ S → q.coeff s = 0) : q = ∑ s ∈ S, q.coeff s • monomial s (1 : ℂ) := by
  have hsub : q.support ⊆ S := fun s hs => by
    by_contra h
    exact (mem_support_iff.mp hs) (hS s h)
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub (fun s _ hs => by rw [notMem_support_iff.mp hs, monomial_zero])]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

/-- Evaluating a linear image of a polynomial supported in `S`. -/
theorem eval_lin_eq_sum (L : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (q : MvPolynomial σ ℂ) (hS : ∀ s, s ∉ S → q.coeff s = 0) (x : σ → ℂ) :
    eval x (L q) = ∑ s ∈ S, q.coeff s * eval x (L (monomial s 1)) := by
  conv_lhs => rw [eq_sum_monomial S q hS]
  simp only [map_sum, map_smul, smul_eval]

/-- Coefficients converging on a fixed finite support and points converging: the evaluations of
any fixed linear image converge. -/
theorem tendsto_eval_lin (L : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (q : ℕ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ)
    (hq : ∀ k s, s ∉ S → (q k).coeff s = 0) (hp : ∀ s, s ∉ S → p.coeff s = 0)
    (hlim : ∀ s, Tendsto (fun k => (q k).coeff s) atTop (𝓝 (p.coeff s)))
    (x : ℕ → σ → ℂ) (y : σ → ℂ) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun k => eval (x k) (L (q k))) atTop (𝓝 (eval y (L p))) := by
  have h1 : (fun k => eval (x k) (L (q k))) =
      fun k => ∑ s ∈ S, (q k).coeff s * eval (x k) (L (monomial s 1)) :=
    funext fun k => eval_lin_eq_sum L S (q k) (hq k) (x k)
  rw [h1, eval_lin_eq_sum L S p hp]
  exact tendsto_finsetSum _ fun s _ =>
    (hlim s).mul (((continuous_eval _).tendsto y).comp hx)

end Support

section Persist

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- The polynomial `(c, t) ↦ ∑_{s ∈ S} c_s (y + t v)^s` in the coefficients and the line
parameter `none`. -/
noncomputable def lineP (S : Finset (σ →₀ ℕ)) (y v : σ → ℂ) : MvPolynomial (Option S) ℂ :=
  ∑ s : S, X (some s) * bind₁ (fun i => C (y i) + C (v i) * X none) (monomial (s : σ →₀ ℕ) 1)

omit [Fintype σ] [DecidableEq σ] in
theorem eval_lineP (S : Finset (σ →₀ ℕ)) (y v : σ → ℂ) (z : Option S → ℂ) :
    eval z (lineP S y v) =
      ∑ s : S, z (some s) * eval (fun i => y i + v i * z none) (monomial (s : σ →₀ ℕ) 1) := by
  simp only [lineP, map_sum, map_mul, eval_X]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  have : eval z (bind₁ (fun i => C (y i) + C (v i) * X none) (monomial (s : σ →₀ ℕ) (1 : ℂ))) =
      eval (fun i => eval z (C (y i) + C (v i) * X none)) (monomial (s : σ →₀ ℕ) 1) := by
    show eval₂Hom (RingHom.id ℂ) z _ = _
    rw [eval₂Hom_bind₁]
    rfl
  rw [this]
  simp

/-- Root persistence: a zero `y` of `p` with a nonzero partial derivative is a limit of zeros of
the `q k`, when the `q k` tend to `p` coefficientwise on a fixed finite support. -/
theorem exists_roots (S : Finset (σ →₀ ℕ)) (q : ℕ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ)
    (hq : ∀ k s, s ∉ S → (q k).coeff s = 0) (hp : ∀ s, s ∉ S → p.coeff s = 0)
    (hlim : ∀ s, Tendsto (fun k => (q k).coeff s) atTop (𝓝 (p.coeff s)))
    (y : σ → ℂ) (hy : eval y p = 0) (i0 : σ) (hi0 : eval y (pderiv i0 p) ≠ 0) :
    ∃ x : ℕ → σ → ℂ, Tendsto x atTop (𝓝 y) ∧ ∀ᶠ k in atTop, eval (x k) (q k) = 0 := by
  classical
  set v : σ → ℂ := Pi.single i0 1 with hv
  set P := lineP S y v with hP
  have hline : ∀ r : MvPolynomial σ ℂ, (∀ s, s ∉ S → r.coeff s = 0) →
      ∀ z : Option S → ℂ, (∀ s : S, z (some s) = r.coeff s) →
        eval z P = eval (fun i => y i + v i * z none) r := by
    intro r hr z hz
    have h0 := eval_lin_eq_sum LinearMap.id S r hr (fun i => y i + v i * z none)
    simp only [LinearMap.id_apply] at h0
    rw [hP, eval_lineP, h0]
    rw [← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun s _ => by rw [hz s]
  set z0 : Option S → ℂ := fun o => o.elim 0 (fun s => p.coeff s) with hz0
  set zk : ℕ → Option S → ℂ := fun k o => o.elim 0 (fun s => (q k).coeff s) with hzk
  have hz0P : eval z0 P = 0 := by
    rw [hline p hp z0 (fun s => rfl)]
    simpa [hz0] using hy
  -- the derivative of `P` in the line parameter is the directional derivative of `p`
  have hj : eval z0 (pderiv none P) ≠ 0 := by
    set e : Option S → ℂ := Pi.single none 1 with he
    have hcurve : HasDerivAt (fun t : ℂ => z0 + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e).const_add z0
    have h1 : HasDerivAt (fun t : ℂ => eval (z0 + t • e) P) (gradCLMg P z0 e) 0 := by
      have hl : HasFDerivAt (fun w => eval w P) (gradCLMg P z0) (z0 + (0 : ℂ) • e) := by
        simpa using (hasStrictFDerivAt_eval_gen P z0).hasFDerivAt
      have h := hl.comp_hasDerivAt (0 : ℂ) hcurve
      exact h
    have hcurve2 : HasDerivAt (fun t : ℂ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
    have h2 : HasDerivAt (fun t : ℂ => eval (y + t • v) p) (gradCLMg p y v) 0 := by
      have hl : HasFDerivAt (fun w => eval w p) (gradCLMg p y) (y + (0 : ℂ) • v) := by
        simpa using (hasStrictFDerivAt_eval_gen p y).hasFDerivAt
      have h := hl.comp_hasDerivAt (0 : ℂ) hcurve2
      exact h
    have heq : (fun t : ℂ => eval (z0 + t • e) P) = fun t => eval (y + t • v) p := by
      funext t
      rw [hline p hp _ (fun s => by simp [hz0, he])]
      have hfun : (fun i => y i + v i * (z0 + t • e) none) = y + t • v := by
        funext i; simp [he, hz0, mul_comm]
      rw [hfun]
    rw [heq] at h1
    have h3 := h1.unique h2
    rw [gradCLMg_apply, gradCLMg_apply] at h3
    have h4 : eval z0 (pderiv none P) = eval y (pderiv i0 p) := by
      simpa [he, hv, Pi.single_apply] using h3
    rw [h4]
    exact hi0
  set Ψ : (Option S → ℂ) → (Option S → ℂ) := fun z o => if o = none then eval z P else z o
    with hΨ
  set D : (Option S → ℂ) →L[ℂ] (Option S → ℂ) := ContinuousLinearMap.pi
    (fun o => if o = none then gradCLMg P z0 else ContinuousLinearMap.proj o) with hD
  have hDapply : ∀ w o, D w o = if o = none then gradCLMg P z0 w else w o := by
    intro w o
    by_cases h : o = none <;> simp [hD, h]
  have hΨD : HasStrictFDerivAt Ψ D z0 := by
    rw [hΨ, hD, hasStrictFDerivAt_pi]
    intro o
    by_cases h : o = none
    · simp only [h, ↓reduceIte]; exact hasStrictFDerivAt_eval_gen P z0
    · simp only [h, ↓reduceIte]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option S => ℂ) o).hasStrictFDerivAt
  have hinj : Function.Injective D.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : ∀ o, D w o = 0 := fun o => congrFun hw o
    have hoff : ∀ o, o ≠ none → w o = 0 := by
      intro o ho; have := hw' o; simpa [hDapply, ho] using this
    have hjj := hw' none
    rw [hDapply] at hjj
    simp only [↓reduceIte] at hjj
    rw [gradCLMg_apply, Finset.sum_eq_single none] at hjj
    · have hwn : w none = 0 := by
        rcases mul_eq_zero.1 hjj with h | h
        · exact h
        · exact absurd h hj
      funext o
      by_cases ho : o = none
      · subst ho; exact hwn
      · exact hoff o ho
    · intro b _ hb; rw [hoff b hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ none) h
  set E : (Option S → ℂ) ≃L[ℂ] (Option S → ℂ) :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv with hE
  have hEcoe : (E : (Option S → ℂ) →L[ℂ] (Option S → ℂ)) = D := by
    ext w o; simp [hE]
  have hΨE : HasStrictFDerivAt Ψ (E : (Option S → ℂ) →L[ℂ] (Option S → ℂ)) z0 := by
    rw [hEcoe]; exact hΨD
  set g := hΨE.localInverse Ψ E z0 with hg
  have hΨz0 : Ψ z0 = z0 := by
    funext o
    by_cases h : o = none
    · subst h; simp only [hΨ, ↓reduceIte]; rw [hz0P]; rfl
    · simp [hΨ, h]
  have hzkT : Tendsto zk atTop (𝓝 z0) := by
    rw [tendsto_pi_nhds]
    intro o
    cases o with
    | none => simp [hzk, hz0]
    | some s => exact hlim s
  have hev : ∀ᶠ k in atTop, Ψ (g (zk k)) = zk k := by
    have := hΨE.eventually_right_inverse
    rw [hΨz0] at this
    exact hzkT.eventually this
  have hu : Tendsto (fun k => g (zk k)) atTop (𝓝 z0) := by
    have h1 := hΨE.localInverse_continuousAt.tendsto
    rw [hΨE.localInverse_apply_image, hΨz0] at h1
    exact h1.comp hzkT
  refine ⟨fun k i => y i + v i * g (zk k) none, ?_, ?_⟩
  · have hn : Tendsto (fun k => g (zk k) none) atTop (𝓝 0) := by
      have := ((continuous_apply none).tendsto z0).comp hu
      simpa [hz0, Function.comp_def] using this
    have : Tendsto (fun k i => y i + v i * g (zk k) none) atTop
        (𝓝 (fun i => y i + v i * 0)) := by
      rw [tendsto_pi_nhds]
      intro i
      exact tendsto_const_nhds.add (tendsto_const_nhds.mul hn)
    simpa using this
  · filter_upwards [hev] with k hk
    have hsome : ∀ s : S, g (zk k) (some s) = (q k).coeff s := fun s => by
      have := congrFun hk (some s)
      simpa [hΨ, hzk] using this
    have hnone : eval (g (zk k)) P = 0 := by
      have := congrFun hk none
      simpa [hΨ, hzk] using this
    rw [← hline (q k) (hq k) (g (zk k)) hsome]
    exact hnone

end Persist

section Main

/-- The Hessian of the permanent at the point of Mignon and Ressayre has full rank. -/
theorem rank_hess_mrPoint (n : ℕ) :
    (hess (PEqualNP.Gct.permPoly ℂ (n + 2)) (mrPoint n)).rank =
      Fintype.card (Fin (n + 2) × Fin (n + 2)) := by
  have hH : hess (PEqualNP.Gct.permPoly ℂ (n + 2)) (mrPoint n) = Matrix.of (hessEntry n) := by
    ext a b
    simp only [hess, Matrix.of_apply, hess_perm_entry]
  rw [hH]
  have hker : ∀ v, (Matrix.of (hessEntry n)).mulVec v = 0 → v = 0 := by
    intro v hv
    have key := hess_kernel n (n.factorial : ℂ) (((n + 2 : ℕ) : ℂ) * ((n - 1).factorial : ℂ))
      (by exact_mod_cast Nat.factorial_ne_zero n) ?_ (fun k l => v (k, l)) ?_
    · funext p
      exact key p.1 p.2
    · intro e
      have hlt : n.factorial < (n + 2) * (n - 1).factorial := by
        rcases n with _ | n
        · simp
        · rw [Nat.factorial_succ]
          simp only [Nat.add_sub_cancel]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos n)
      have : ((n.factorial : ℕ) : ℂ) = (((n + 2) * (n - 1).factorial : ℕ) : ℂ) := by
        rw [e]; push_cast; ring
      exact absurd (Nat.cast_injective this) (ne_of_lt hlt)
    · intro i j
      have := congrFun hv (i, j)
      rw [hess_mulVec] at this
      simpa using this
  have hinj : Function.Injective (Matrix.of (hessEntry n)).mulVec := by
    intro v w hvw
    have := hker (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    exact sub_eq_zero.mp this
  exact Matrix.rank_of_isUnit _ (Matrix.mulVec_injective_iff_isUnit.mp hinj)

/-- Border Mignon-Ressayre: a border determinantal expression of `perm_m` of size `n`, `m ≥ 2`,
forces `m² ≤ 2n`. -/
theorem border_mr (m n : ℕ) (hm : 2 ≤ m)
    (h : PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n) :
    m ^ 2 ≤ 2 * n := by
  classical
  obtain ⟨q, hq, hlim⟩ := h
  obtain ⟨k', rfl⟩ : ∃ k', m = k' + 2 := ⟨m - 2, by omega⟩
  set p := PEqualNP.Gct.permPoly ℂ (k' + 2) with hpdef
  have hfin : {s : Fin (k' + 2) × Fin (k' + 2) →₀ ℕ |
      s ≤ Finsupp.equivFunOnFinite.symm (fun _ => n)}.Finite := Set.finite_Iic _
  have hqS : ∀ k s, s ∉ hfin.toFinset → (q k).coeff s = 0 := by
    intro k s hs
    by_contra hne
    apply hs
    have hmem : s ∈ (q k).support := mem_support_iff.mpr hne
    have hdeg := (le_totalDegree hmem).trans (PEqualNP.Gct.L003 _ ℂ (q k) n (hq k))
    rw [Set.Finite.mem_toFinset]
    intro i
    by_cases hi : i ∈ s.support
    · exact (Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) hi).trans hdeg
    · simp [Finsupp.notMem_support_iff.mp hi]
  have hpS : ∀ s, s ∉ hfin.toFinset → p.coeff s = 0 := fun s hs =>
    tendsto_nhds_unique (hlim s) (by simp [hqS _ s hs])
  set y := mrPoint k' with hydef
  have hy0 : eval y p = 0 := perm_mrPoint k'
  have hrank := rank_hess_mrPoint k'
  have hdet : (hess p y).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_rank_eq_card _ hrank)).ne_zero
  have hgrad : ∃ i0, eval y (pderiv i0 p) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmul : Matrix.mulVec (hess p y) y = 0 := by
      funext a
      simp only [Matrix.mulVec, dotProduct, hess, Matrix.of_apply, Pi.zero_apply]
      rw [euler_hess (by omega) y a, hcon a, mul_zero]
    have hy := eq_zero_of_rank_eq_card _ hrank y hmul
    have h11 := congrFun hy (0, 1)
    simp [hydef, mrPoint] at h11
  obtain ⟨i0, hi0⟩ := hgrad
  obtain ⟨x, hx, hxz⟩ := exists_roots _ q p hqS hpS hlim y hy0 i0 hi0
  have hH : Tendsto (fun k => hess (q k) (x k)) atTop (𝓝 (hess p y)) := by
    refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
    exact tendsto_eval_lin ((pderiv a).toLinearMap ∘ₗ (pderiv b).toLinearMap) _ q p hqS hpS
      hlim x y hx
  have hD : Tendsto (fun k => (hess (q k) (x k)).det) atTop (𝓝 (hess p y).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hH
  obtain ⟨k, hk1, hk2⟩ := (hxz.and (hD.eventually_ne hdet)).exists
  have hr : (hess (q k) (x k)).rank = Fintype.card (Fin (k' + 2) × Fin (k' + 2)) :=
    Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hk2))
  have hle := rank_hess_detExpr_gen (q k) (x k) (hq k) hk1
  rw [hr] at hle
  simpa [Fintype.card_prod, sq] using hle

end Main

end PEqualNP.Gct.Helpers.BorderMR
