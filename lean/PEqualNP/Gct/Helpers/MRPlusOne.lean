import PEqualNP.Defs
import PEqualNP.Gct.L009
import PEqualNP.Gct.L013
import PEqualNP.Gct.L019
import PEqualNP.Gct.Helpers.OrbitClosure

/-! The `m² + 2 ≤ 2n` bound for determinantal expressions of the permanent, assuming the
pointwise step `adj(A(y)) A₀ = 0 = A₀ adj(A(y))` at smooth zeros `y` of the permanent with
Hessian of full rank. -/

namespace PEqualNP.Gct.Helpers

open MvPolynomial Filter Topology Finset

section TangentGen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The gradient of `p` at `x`, as a continuous linear functional (general index type). -/
noncomputable def gradCLMg (p : MvPolynomial ι ℂ) (x : ι → ℂ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj i

omit [DecidableEq ι] in
theorem gradCLMg_apply (p : MvPolynomial ι ℂ) (x v : ι → ℂ) :
    gradCLMg p x v = ∑ i, v i * eval x (pderiv i p) := by
  simp [gradCLMg, mul_comm]

theorem hasStrictFDerivAt_eval_gen (p : MvPolynomial ι ℂ) (x : ι → ℂ) :
    HasStrictFDerivAt (fun y => eval y p) (gradCLMg p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : gradCLMg (C a) x = 0 := by ext v; simp [gradCLMg_apply]
    rw [this]; simpa using hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have : gradCLMg (p + q) x = gradCLMg p x + gradCLMg q x := by
      ext v; simp [gradCLMg_apply, mul_add, Finset.sum_add_distrib]
    rw [this]; simp only [map_add]; exact hp.add hq
  | mul_X p i hp =>
    have h1 : HasStrictFDerivAt (fun y : ι → ℂ => y i) (ContinuousLinearMap.proj i) x :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).hasStrictFDerivAt
    have : gradCLMg (p * X i) x = eval x p • (ContinuousLinearMap.proj i) + x i • gradCLMg p x := by
      ext v
      simp only [gradCLMg_apply, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, eval_mul,
        add_apply, smul_apply,
        ContinuousLinearMap.proj_apply, eval_X]
      simp only [mul_add, Finset.sum_add_distrib, Pi.single_apply, Finset.mul_sum]
      simp [mul_comm, mul_left_comm]
    rw [this]; convert hp.mul h1 using 1; funext y; simp

theorem pderiv_vanish_gen (p q : MvPolynomial ι ℂ) (x : ι → ℂ)
    (hpx : MvPolynomial.eval x p = 0)
    (hgrad : ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) ≠ 0)
    (hq : ∀ᶠ y in nhds x, MvPolynomial.eval y p = 0 → MvPolynomial.eval y q = 0)
    (t : ι → ℂ) (ht : ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0) :
    ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i q) = 0 := by
  obtain ⟨j, hj⟩ := hgrad
  set Ψ : (ι → ℂ) → (ι → ℂ) := fun y i => if i = j then eval y p else y i with hΨ
  set D : (ι → ℂ) →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi
    (fun i => if i = j then gradCLMg p x else ContinuousLinearMap.proj i) with hD
  have hDapply : ∀ v i, D v i = if i = j then gradCLMg p x v else v i := by
    intro v i
    by_cases h : i = j <;> simp [hD, h]
  have hΨD : HasStrictFDerivAt Ψ D x := by
    rw [hΨ, hD, hasStrictFDerivAt_pi]
    intro i
    by_cases h : i = j
    · simp only [h, ↓reduceIte]; exact hasStrictFDerivAt_eval_gen p x
    · simp only [h, ↓reduceIte]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).hasStrictFDerivAt
  have hinj : Function.Injective D.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : ∀ i, D v i = 0 := fun i => congrFun hv i
    have hoff : ∀ i, i ≠ j → v i = 0 := by
      intro i hi; have := hv' i; simpa [hDapply, hi] using this
    have hjj := hv' j
    rw [hDapply] at hjj
    simp only [↓reduceIte] at hjj
    rw [gradCLMg_apply, Finset.sum_eq_single j] at hjj
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
  set E : (ι → ℂ) ≃L[ℂ] (ι → ℂ) :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv with hE
  have hEcoe : (E : (ι → ℂ) →L[ℂ] (ι → ℂ)) = D := by
    ext v i; simp [hE]
  have hΨE : HasStrictFDerivAt Ψ (E : (ι → ℂ) →L[ℂ] (ι → ℂ)) x := by
    rw [hEcoe]; exact hΨD
  set g := hΨE.localInverse Ψ E x with hg
  set t' : ι → ℂ := fun i => if i = j then 0 else t i with ht'
  have hDt : D t = t' := by
    funext i
    rw [hDapply]
    by_cases h : i = j
    · simp [h, ht', gradCLMg_apply, ht]
    · simp [h, ht']
  have hEt : E.symm t' = t := by
    rw [← hDt, ← hEcoe]; simp
  set c : ℂ → (ι → ℂ) := fun ε => g (Ψ x + ε • t') with hc
  have hline : HasDerivAt (fun ε : ℂ => Ψ x + ε • t') t' 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const t').const_add (Ψ x)
  have hcd : HasDerivAt c t 0 := by
    have h1 : HasFDerivAt g (E.symm : (ι → ℂ) →L[ℂ] (ι → ℂ)) (Ψ x + (0 : ℂ) • t') := by
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
  have hqd : HasDerivAt (fun ε => eval (c ε) q) (gradCLMg q x t) 0 := by
    have h1 : HasFDerivAt (fun y => eval y q) (gradCLMg q x) (c 0) := by
      rw [hc0]; exact (hasStrictFDerivAt_eval_gen q x).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) hcd
  have hzero : HasDerivAt (fun ε => eval (c ε) q) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hqc
  have := hqd.unique hzero
  rwa [gradCLMg_apply] at this

end TangentGen

section Deriv

variable {ι : Type} [Fintype ι]

/-- Directional derivative of a polynomial at `x` along `t`. -/
noncomputable def dd (x t : ι → ℂ) (q : MvPolynomial ι ℂ) : ℂ :=
  ∑ i, t i * eval x (pderiv i q)

theorem dd_add (x t : ι → ℂ) (p q : MvPolynomial ι ℂ) : dd x t (p + q) = dd x t p + dd x t q := by
  simp [dd, mul_add, Finset.sum_add_distrib]

theorem dd_C (x t : ι → ℂ) (c : ℂ) : dd x t (C c) = 0 := by simp [dd]

theorem dd_mul (x t : ι → ℂ) (p q : MvPolynomial ι ℂ) :
    dd x t (p * q) = dd x t p * eval x q + eval x p * dd x t q := by
  simp only [dd, Derivation.leibniz, smul_eq_mul, map_add, eval_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]; congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring

theorem dd_sum {κ : Type} (x t : ι → ℂ) (s : Finset κ) (f : κ → MvPolynomial ι ℂ) :
    dd x t (∑ k ∈ s, f k) = ∑ k ∈ s, dd x t (f k) := by
  simp only [dd, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem dd_add_left (x t s : ι → ℂ) (q : MvPolynomial ι ℂ) : dd x (t + s) q = dd x t q + dd x s q := by
  simp [dd, add_mul, Finset.sum_add_distrib]

theorem dd_smul_left (x t : ι → ℂ) (c : ℂ) (q : MvPolynomial ι ℂ) : dd x (c • t) q = c * dd x t q := by
  simp [dd, mul_assoc, Finset.mul_sum]

/-- Product rule for the entrywise directional derivative of a matrix product. -/
theorem dd_matrix_mul {n : ℕ} (x t : ι → ℂ) (B C' : Matrix (Fin n) (Fin n) (MvPolynomial ι ℂ)) :
    (B * C').map (dd x t) = B.map (dd x t) * C'.map (eval x) + B.map (eval x) * C'.map (dd x t) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_sum, dd_mul,
    Finset.sum_add_distrib]

/-- Derivation of a product. -/
theorem derivation_prod {R S κ : Type} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq κ]
    (D : Derivation R S S) (s : Finset κ) (f : κ → S) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ k ∈ s.erase i, f k) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, smul_eq_mul, smul_eq_mul, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hai, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
    ring

/-- Jacobi's formula for a derivation. -/
theorem derivation_det {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (D : Derivation R S S) (B : Matrix (Fin n) (Fin n) S) :
    D B.det = ∑ i, ∑ j, B.adjugate j i * D (B i j) := by
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, B.adjugate j i * D (B i j) =
      (B.updateCol j (fun i => D (B i j))).det := by
    intro j; rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]; rfl
  simp_rw [key, Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Units.smul_def]
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)]
  · rw [Matrix.updateCol_self]

end Deriv

section Main

theorem isUnit_of_rank_eq_card {κ : Type} [Fintype κ] [DecidableEq κ] (H : Matrix κ κ ℂ)
    (h : H.rank = Fintype.card κ) : IsUnit H := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  have h2 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  rw [show Module.finrank ℂ (LinearMap.range H.mulVecLin) = H.rank from rfl, h,
    Module.finrank_fintype_fun_eq_card] at h2
  have hk : LinearMap.ker H.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  exact LinearMap.ker_eq_bot.mp hk

theorem isHomogeneous_permPoly (m : ℕ) : (PEqualNP.Gct.permPoly ℂ m).IsHomogeneous m := by
  unfold PEqualNP.Gct.permPoly Matrix.permanent
  apply IsHomogeneous.sum
  intro σ _
  have := IsHomogeneous.prod (s := univ)
    (φ := fun i => (Matrix.mvPolynomialX (Fin m) (Fin m) ℂ) (σ i) i) (n := fun _ => 1)
    (fun i _ => by simpa using isHomogeneous_X ℂ (σ i, i))
  simpa using this

theorem isHomogeneous_det_of_linear {κ : Type} {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (MvPolynomial κ ℂ)) (h : ∀ i j, (B i j).IsHomogeneous 1) :
    B.det.IsHomogeneous n := by
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have := IsHomogeneous.prod (s := univ) (φ := fun i => B (σ i) i) (n := fun _ => 1)
    (fun i _ => h _ _)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  rw [Units.smul_def, zsmul_eq_mul]
  have hc : (((Equiv.Perm.sign σ : ℤ)) : MvPolynomial κ ℂ) =
      C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
  rw [hc]
  simpa using (isHomogeneous_C κ ((Equiv.Perm.sign σ : ℤ) : ℂ)).mul this

theorem mr_plus_one_of_pointwise
    (hpt : ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ)), 3 ≤ m → 2 * n ≤ m ^ 2 + 1 → (∀ i j, (A i j).totalDegree ≤ 1) → A.det = PEqualNP.Gct.permPoly ℂ m → ∀ y : Fin m × Fin m → ℂ, MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 → (Matrix.of fun a b : Fin m × Fin m => MvPolynomial.eval y (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ m)))).rank = m ^ 2 → (A.map (MvPolynomial.eval y)).adjugate * A.map (fun q => q.coeff 0) = 0 ∧ A.map (fun q => q.coeff 0) * (A.map (MvPolynomial.eval y)).adjugate = 0) :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 + 2 ≤ 2 * n := by
  intro m n hm hexpr
  by_contra hlt
  have hle : 2 * n ≤ m ^ 2 + 1 := by omega
  have h009 := PEqualNP.Gct.L009 m n hexpr
  obtain ⟨A, hA, hdet⟩ := hexpr
  obtain ⟨x, hx0, hrank⟩ := PEqualNP.Gct.L013 m (by omega)
  set perm := PEqualNP.Gct.permPoly ℂ m with hperm
  set H : (Fin m × Fin m → ℂ) → Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
    fun y => Matrix.of fun a b => eval y (pderiv a (pderiv b perm)) with hH
  have hcard : Fintype.card (Fin m × Fin m) = m ^ 2 := by simp [sq]
  have hHx : IsUnit (H x) := isUnit_of_rank_eq_card _ (by rw [hcard]; exact hrank)
  -- the Hessian keeps full rank near `x`
  have hnear : ∀ᶠ y in 𝓝 x, (H y).rank = m ^ 2 := by
    have hcont : Continuous fun y => (H y).det := by
      refine Continuous.matrix_det ?_
      refine continuous_matrix fun a b => ?_
      exact MvPolynomial.continuous_eval _
    have hne : (H x).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hHx).ne_zero
    filter_upwards [hcont.continuousAt.eventually_ne hne] with y hy
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hy)), hcard]
  -- the gradient at `x` is nonzero (Euler's identity)
  have hhom : perm.IsHomogeneous m := isHomogeneous_permPoly m
  have hx_ne : x ≠ 0 := by
    rintro rfl
    have hz : H 0 = 0 := by
      ext a b
      have h2 := (hhom.pderiv (i := b)).pderiv (i := a)
      have hc : (pderiv a (pderiv b perm)).coeff 0 = 0 := h2.coeff_eq_zero (by simp; omega)
      simpa [hH, eval_zero, constantCoeff_eq] using hc
    change (H 0).rank = _ at hrank
    rw [hz, Matrix.rank_zero] at hrank
    have : 0 < m ^ 2 := by positivity
    omega
  have hgrad : ∃ a, eval x (pderiv a perm) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hx_ne
    have hv : Matrix.vecMul x (H x) = 0 := by
      funext a
      have e := congrArg (eval x) (hhom.pderiv (i := a)).sum_X_mul_pderiv
      simp only [map_sum, eval_mul, eval_X, map_nsmul, hcon a, smul_zero] at e
      simpa [Matrix.vecMul, dotProduct, hH] using e
    exact (Matrix.vecMul_injective_iff_isUnit.mpr hHx)
      (show Matrix.vecMul _ (H x) = Matrix.vecMul 0 (H x) by rw [hv, Matrix.zero_vecMul])
  -- the matrices
  set A0 : Matrix (Fin n) (Fin n) ℂ := A.map (fun q => q.coeff 0) with hA0
  set M := A.map (eval x) with hM
  have hadjev : ∀ y, (A.map (eval y)).adjugate = A.adjugate.map (eval y) :=
    fun y => ((eval y).map_adjugate A).symm
  have hC0 : ∀ y : Fin m × Fin m → ℂ, (A0.map (C (σ := Fin m × Fin m))).map (eval y) = A0 := by intro y; ext i j; simp
  have hPev : ∀ y, (A.adjugate * A0.map (C (σ := Fin m × Fin m))).map (eval y) = (A.map (eval y)).adjugate * A0 := by
    intro y; rw [Matrix.map_mul, hC0, hadjev]
  have hQev : ∀ y, (A0.map (C (σ := Fin m × Fin m)) * A.adjugate).map (eval y) = A0 * (A.map (eval y)).adjugate := by
    intro y; rw [Matrix.map_mul, hC0, hadjev]
  have hzeroP : ∀ i j, ∀ᶠ y in 𝓝 x, eval y perm = 0 →
      eval y ((A.adjugate * A0.map (C (σ := Fin m × Fin m))) i j) = 0 := by
    intro i j
    filter_upwards [hnear] with y hy hy0
    have h1 := (hpt m n A hm hle hA hdet y hy0 hy).1
    have h2 := congrFun (congrFun (hPev y) i) j
    rw [Matrix.map_apply] at h2
    rw [h2, h1]; rfl
  have hzeroQ : ∀ i j, ∀ᶠ y in 𝓝 x, eval y perm = 0 →
      eval y ((A0.map (C (σ := Fin m × Fin m)) * A.adjugate) i j) = 0 := by
    intro i j
    filter_upwards [hnear] with y hy hy0
    have h1 := (hpt m n A hm hle hA hdet y hy0 hy).2
    have h2 := congrFun (congrFun (hQev y) i) j
    rw [Matrix.map_apply] at h2
    rw [h2, h1]; rfl
  have hdC : ∀ t, (A0.map (C (σ := Fin m × Fin m))).map (dd x t) = 0 := by intro t; ext; simp [dd_C]
  set Dmat : (Fin m × Fin m → ℂ) → Matrix (Fin n) (Fin n) ℂ := fun t => A.adjugate.map (dd x t)
    with hDmat
  have hDA0 : ∀ t, dd x t perm = 0 → Dmat t * A0 = 0 := by
    intro t ht
    have e := dd_matrix_mul x t A.adjugate (A0.map (C (σ := Fin m × Fin m)))
    rw [hdC, Matrix.mul_zero, add_zero, hC0] at e
    rw [← e]; ext i j
    exact pderiv_vanish_gen perm _ x hx0 hgrad (hzeroP i j) t ht
  have hA0D : ∀ t, dd x t perm = 0 → A0 * Dmat t = 0 := by
    intro t ht
    have e := dd_matrix_mul x t (A0.map (C (σ := Fin m × Fin m))) A.adjugate
    rw [hdC, Matrix.zero_mul, zero_add, hC0] at e
    rw [← e]; ext i j
    exact pderiv_vanish_gen perm _ x hx0 hgrad (hzeroQ i j) t ht
  have hDM : ∀ t, dd x t perm = 0 → Dmat t * M = M.adjugate * (-(A.map (dd x t))) := by
    intro t ht
    have e := dd_matrix_mul x t A.adjugate A
    rw [Matrix.adjugate_mul, hdet] at e
    have hl : (perm • (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))).map
        (dd x t) = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, dd_mul, ht, zero_mul,
        zero_add, Matrix.zero_apply]
      by_cases h : i = j <;> simp [Matrix.one_apply, h, dd]
    rw [hl, ← hadjev x] at e
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left e.symm
  -- Jacobi's formula
  have hc : ∀ i j a, pderiv a (A i j) = C ((A i j).coeff (Finsupp.single a 1)) :=
    fun i j a => pderiv_of_totalDegree_le_one _ (hA i j) a
  have hJ : ∀ a, pderiv a perm =
      ∑ i, ∑ j, A.adjugate j i * C ((A i j).coeff (Finsupp.single a 1)) := by
    intro a
    rw [← hdet]
    refine (derivation_det (pderiv a) A).trans ?_
    simp_rw [hc]
  have hgJ : ∀ a, eval x (pderiv a perm) =
      ∑ i, ∑ j, M.adjugate j i * (A i j).coeff (Finsupp.single a 1) := by
    intro a; rw [hJ a, hadjev x]; simp [map_sum]
  have hdJ : ∀ t a, dd x t (pderiv a perm) =
      ∑ i, ∑ j, Dmat t j i * (A i j).coeff (Finsupp.single a 1) := by
    intro t a
    rw [hJ a]
    simp only [dd_sum, dd_mul, dd_C, mul_zero, add_zero, eval_C, hDmat, Matrix.map_apply]
  have hdH : ∀ t a, dd x t (pderiv a perm) = Matrix.vecMul t (H x) a := by
    intro t a; simp [dd, Matrix.vecMul, dotProduct, hH]
  have hinj : ∀ t, Dmat t = 0 → t = 0 := by
    intro t h0
    have hv : Matrix.vecMul t (H x) = 0 := by
      funext a; rw [← hdH, hdJ, h0]; simp
    exact (Matrix.vecMul_injective_iff_isUnit.mpr hHx)
      (show Matrix.vecMul _ (H x) = Matrix.vecMul 0 (H x) by rw [hv, Matrix.zero_vecMul])
  -- the linear maps
  let G : (Fin m × Fin m → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun t => dd x t perm
      map_add' := fun t s => dd_add_left x t s perm
      map_smul' := fun c t => by simp [dd_smul_left] }
  let Dl : (Fin m × Fin m → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := Dmat
      map_add' := by intro t s; ext i j; simp [hDmat, dd_add_left]
      map_smul' := by intro c t; ext i j; simp [hDmat, dd_smul_left] }
  let T := LinearMap.ker G
  let s := LinearMap.range (Dl.domRestrict T)
  have hsinj : Function.Injective (Dl.domRestrict T) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    exact Subtype.ext (hinj t ht)
  have hfs : Module.finrank ℂ s = Module.finrank ℂ (LinearMap.ker G) := LinearMap.finrank_range_of_inj hsinj
  have hT : m ^ 2 ≤ Module.finrank ℂ (LinearMap.ker G) + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker G
    have h2 : Module.finrank ℂ (LinearMap.range G) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    rw [Module.finrank_fintype_fun_eq_card, hcard] at h1
    omega
  -- hypotheses of L-gct-019
  have hadj : M.adjugate ≠ 0 := by
    intro h0; obtain ⟨a, ha⟩ := hgrad; apply ha; rw [hgJ, h0]; simp
  have hdetM : M.det = 0 := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, hx0]
  have hpx := hpt m n A hm hle hA hdet x hx0 hrank
  have hA0ne : A0 ≠ 0 := by
    intro h0
    have hlin : ∀ i j, (A i j).IsHomogeneous 1 := by
      intro i j
      have hc0 : (A i j).coeff 0 = 0 := by
        have := congrFun (congrFun h0 i) j
        simpa [hA0] using this
      rw [affine_decomp (A i j) (hA i j), hc0, map_zero, zero_add]
      apply IsHomogeneous.sum
      intro v _
      simpa using (isHomogeneous_C _ _).mul (isHomogeneous_X ℂ v)
    have hdh := isHomogeneous_det_of_linear A hlin
    rw [hdet] at hdh
    have hne : perm ≠ 0 := by
      intro h; obtain ⟨a, ha⟩ := hgrad; apply ha; rw [h]; simp
    have hmn := hhom.inj_right hdh hne
    subst hmn
    nlinarith
  have h19 := PEqualNP.Gct.L019 n M A0 hdetM hadj hpx.1 hpx.2 hA0ne s (by
    rintro D ⟨t, rfl⟩
    have ht : dd x t.1 perm = 0 := t.2
    exact ⟨hDA0 t.1 ht, hA0D t.1 ht, _, hDM t.1 ht⟩)
  omega

end Main

end PEqualNP.Gct.Helpers
