import Mathlib
import PEqualNP.Defs

/-!
# Persistence of nondegenerate zeros under coefficientwise convergence

A polynomial map `F : ℂ^d → ℂ^d` has a nondegenerate zero at `x` when every component vanishes
at `x` and the Jacobian determinant at `x` is nonzero. If `Fk k → F` coefficientwise, with all
`Fk k i` of total degree at most `D`, then every nondegenerate zero of `F` is a limit of
nondegenerate zeros of `Fk k`, and so `Fk k` has, for all large `k`, at least as many
nondegenerate zeros as `F`.

The proof is soft. Polynomials of degree at most `D` are parametrized by their coefficient
vectors on a finite box of monomials; evaluation is a continuously differentiable function of
the pair (coefficients, point); the implicit function theorem at (coefficients of `F`, zero)
gives a zero depending continuously on the coefficients; and the Jacobian determinant is a
continuous function of the pair, so it stays nonzero.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial Filter Topology

noncomputable section

/-- The monomials in `d` variables all of whose exponents are at most `D`. -/
def boxMonomials (d D : ℕ) : Finset (Fin d →₀ ℕ) :=
  Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun _ => D)

/-- A polynomial of total degree at most `D` is supported in the box. -/
theorem mem_boxMonomials_of_mem_support {d D : ℕ} {p : MvPolynomial (Fin d) ℂ}
    (hp : p.totalDegree ≤ D) {s : Fin d →₀ ℕ} (hs : s ∈ p.support) :
    s ∈ boxMonomials d D := by
  rw [boxMonomials, Finset.mem_Icc]
  refine ⟨zero_le, fun i => ?_⟩
  have h1 := le_totalDegree hs
  have h2 : s i ≤ s.sum fun _ e => e := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact Finset.single_le_sum (f := fun i => s i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h3 : s i ≤ D := le_trans h2 (le_trans h1 hp)
  simpa using h3

/-- The polynomial with prescribed coefficients on a finite set of monomials. -/
def polyOf {d : ℕ} (M : Finset (Fin d →₀ ℕ)) (c : ↥M → ℂ) : MvPolynomial (Fin d) ℂ :=
  ∑ s : ↥M, monomial s.1 (c s)

/-- A polynomial supported in `M` is recovered from its coefficients on `M`. -/
theorem polyOf_coeff {d : ℕ} (M : Finset (Fin d →₀ ℕ)) (p : MvPolynomial (Fin d) ℂ)
    (h : p.support ⊆ M) : polyOf M (fun s => p.coeff s.1) = p := by
  unfold polyOf
  rw [Finset.sum_coe_sort M (fun s => monomial s (p.coeff s))]
  conv_rhs => rw [← support_sum_monomial_coeff p]
  symm
  apply Finset.sum_subset h
  intro s _ hs
  simp [notMem_support_iff.1 hs]

theorem eval_polyOf {d : ℕ} (M : Finset (Fin d →₀ ℕ)) (c : ↥M → ℂ) (x : Fin d → ℂ) :
    eval x (polyOf M c) = ∑ s : ↥M, c s * eval x (monomial s.1 (1 : ℂ)) := by
  simp only [polyOf, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show monomial s.1 (c s) = C (c s) * monomial s.1 (1 : ℂ) by rw [C_mul_monomial, mul_one],
    map_mul, eval_C]

theorem eval_pderiv_polyOf {d : ℕ} (M : Finset (Fin d →₀ ℕ)) (c : ↥M → ℂ) (x : Fin d → ℂ)
    (j : Fin d) :
    eval x (pderiv j (polyOf M c)) =
      ∑ s : ↥M, c s * eval x (pderiv j (monomial s.1 (1 : ℂ))) := by
  simp only [polyOf, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show monomial s.1 (c s) = C (c s) * monomial s.1 (1 : ℂ) by rw [C_mul_monomial, mul_one],
    pderiv_C_mul, map_mul, eval_C]

/-- Evaluation of a fixed polynomial is continuously differentiable in the point. -/
theorem contDiff_eval {d : ℕ} (p : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun y : Fin d → ℂ => eval y p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p n hp => simpa using hp.mul (by fun_prop : ContDiff ℂ 1 fun y : Fin d → ℂ => y n)

/-- The derivative of evaluation of a polynomial is given by its formal partial derivatives. -/
theorem hasFDerivAt_eval {d : ℕ} (p : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    HasFDerivAt (fun y : Fin d → ℂ => eval y p)
      (∑ j, eval x (pderiv j p) • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ)) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : HasFDerivAt (fun _ : Fin d → ℂ => a) (0 : (Fin d → ℂ) →L[ℂ] ℂ) x :=
      hasFDerivAt_const a x
    simp only [eval_C, pderiv_C, map_zero]
    convert h using 1
    ext v
    simp
  | add p q hp hq =>
    have h : HasFDerivAt (fun y : Fin d → ℂ => eval y p + eval y q) _ x := hp.add hq
    simp only [map_add]
    convert h using 1
    ext v
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have h := hp.mul (hasFDerivAt_apply n x)
    simp only [map_mul, eval_X]
    convert h using 1
    ext v
    simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.sum_add_distrib, mul_add,
      Finset.mul_sum, mul_comm, mul_left_comm]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

/-- Evaluation as a function of the pair (coefficient vectors, point). -/
def evalPair {d : ℕ} (M : Finset (Fin d →₀ ℕ)) :
    (Fin d → ↥M → ℂ) × (Fin d → ℂ) → (Fin d → ℂ) :=
  fun z i => eval z.2 (polyOf M (z.1 i))

theorem contDiff_evalPair {d : ℕ} (M : Finset (Fin d →₀ ℕ)) : ContDiff ℂ 1 (evalPair M) := by
  rw [contDiff_pi]
  intro i
  simp only [evalPair, eval_polyOf]
  apply ContDiff.sum
  intro s _
  apply ContDiff.mul
  · fun_prop
  · exact (contDiff_eval _).comp contDiff_snd

/-- The Jacobian determinant as a function of the pair (coefficient vectors, point). -/
def jacPair {d : ℕ} (M : Finset (Fin d →₀ ℕ)) :
    (Fin d → ↥M → ℂ) × (Fin d → ℂ) → ℂ :=
  fun z => (Matrix.of fun i j => eval z.2 (pderiv j (polyOf M (z.1 i)))).det

theorem continuous_jacPair {d : ℕ} (M : Finset (Fin d →₀ ℕ)) : Continuous (jacPair M) := by
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  simp only [Matrix.of_apply, eval_pderiv_polyOf]
  refine continuous_finsetSum _ fun s _ => ?_
  apply Continuous.mul
  · fun_prop
  · exact (contDiff_eval _).continuous.comp continuous_snd

/-- **Single zero.** A nondegenerate zero `x0` of `F` is the limit of a sequence `xk k`, where
`xk k` is, for all large `k`, a nondegenerate zero of `Fk k`. -/
theorem nondeg_zero_persist (d : ℕ) (D : ℕ) (F : Fin d → MvPolynomial (Fin d) ℂ)
    (Fk : ℕ → Fin d → MvPolynomial (Fin d) ℂ)
    (hdeg : ∀ k i, (Fk k i).totalDegree ≤ D)
    (hconv : ∀ i s, Tendsto (fun k => (Fk k i).coeff s) atTop (𝓝 ((F i).coeff s)))
    (x0 : Fin d → ℂ) (h0 : ∀ i, eval x0 (F i) = 0)
    (hJ : (Matrix.of fun i j => eval x0 (pderiv j (F i))).det ≠ 0) :
    ∃ xk : ℕ → (Fin d → ℂ), Tendsto xk atTop (𝓝 x0) ∧
      ∀ᶠ k in atTop, (∀ i, eval (xk k) (Fk k i) = 0) ∧
        (Matrix.of fun i j => eval (xk k) (pderiv j (Fk k i))).det ≠ 0 := by
  classical
  set M := boxMonomials d D with hM
  let c0 : Fin d → ↥M → ℂ := fun i s => (F i).coeff s.1
  let ck : ℕ → Fin d → ↥M → ℂ := fun k i s => (Fk k i).coeff s.1
  have hFk : ∀ k i, polyOf M (ck k i) = Fk k i := fun k i =>
    polyOf_coeff M (Fk k i) fun s hs => mem_boxMonomials_of_mem_support (hdeg k i) hs
  have hF : ∀ i, polyOf M (c0 i) = F i := by
    intro i
    refine polyOf_coeff M (F i) fun s hs => ?_
    by_contra hsM
    have hz : (fun k => (Fk k i).coeff s) = fun _ => (0 : ℂ) := by
      funext k
      by_contra h
      exact hsM (mem_boxMonomials_of_mem_support (hdeg k i) (mem_support_iff.2 h))
    have h1 := hconv i s
    rw [hz] at h1
    exact (mem_support_iff.1 hs) (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hck : Tendsto ck atTop (𝓝 c0) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun s => hconv i s.1
  have dG : HasStrictFDerivAt (evalPair M) (fderiv ℂ (evalPair M) (c0, x0)) (c0, x0) :=
    (contDiff_evalPair M).contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero
  -- the partial derivative in the point is the Jacobian
  let J : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun i j => eval x0 (pderiv j (F i))
  let A : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      ∑ j, eval x0 (pderiv j (F i)) • (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ)
  have hA : HasFDerivAt (fun x => evalPair M (c0, x)) A x0 := by
    have : (fun x => evalPair M (c0, x)) = fun x i => eval x (F i) := by
      funext x i
      simp [evalPair, hF]
    rw [this]
    exact hasFDerivAt_pi.2 fun i => hasFDerivAt_eval (F i) x0
  have hcomp : HasFDerivAt (fun x => evalPair M (c0, x))
      (fderiv ℂ (evalPair M) (c0, x0) ∘L ContinuousLinearMap.inr ℂ _ _) x0 :=
    dG.hasFDerivAt.comp x0 (hasFDerivAt_prodMk_right c0 x0)
  have hinv : (fderiv ℂ (evalPair M) (c0, x0) ∘L
      ContinuousLinearMap.inr ℂ (Fin d → ↥M → ℂ) (Fin d → ℂ)).IsInvertible := by
    rw [hcomp.unique hA]
    have : Invertible J := Matrix.invertibleOfIsUnitDet J (isUnit_iff_ne_zero.2 hJ)
    refine ⟨(Matrix.toLinearEquiv' J inferInstance).toContinuousLinearEquiv, ?_⟩
    ext v i
    simp [A, J, Matrix.toLinearEquiv', Matrix.mulVec, dotProduct]
  let ψ := dG.implicitFunctionOfProdDomain hinv
  have hψ : Tendsto ψ (𝓝 c0) (𝓝 x0) := dG.tendsto_implicitFunctionOfProdDomain hinv
  have hx : Tendsto (fun k => ψ (ck k)) atTop (𝓝 x0) := hψ.comp hck
  have hz : ∀ᶠ k in atTop, evalPair M (ck k, ψ (ck k)) = evalPair M (c0, x0) :=
    hck.eventually (dG.eventually_apply_implicitFunctionOfProdDomain hinv)
  have hG0 : evalPair M (c0, x0) = 0 := by
    funext i
    simp [evalPair, hF, h0]
  have hJ0 : jacPair M (c0, x0) ≠ 0 := by
    simpa [jacPair, hF] using hJ
  have hJk : ∀ᶠ k in atTop, jacPair M (ck k, ψ (ck k)) ≠ 0 :=
    (hck.prodMk_nhds hx).eventually ((continuous_jacPair M).continuousAt.eventually_ne hJ0)
  refine ⟨fun k => ψ (ck k), hx, ?_⟩
  filter_upwards [hz, hJk] with k h1 h2
  refine ⟨fun i => ?_, ?_⟩
  · have := congrFun (h1.trans hG0) i
    simpa [evalPair, hFk] using this
  · simpa [jacPair, hFk] using h2

/-- **Single zero, ball form.** For every `ε > 0`, for all large `k` the map `Fk k` has a
nondegenerate zero within distance `ε` of the nondegenerate zero `x0` of `F`. -/
theorem nondeg_zero_persist_ball (d : ℕ) (D : ℕ) (F : Fin d → MvPolynomial (Fin d) ℂ)
    (Fk : ℕ → Fin d → MvPolynomial (Fin d) ℂ)
    (hdeg : ∀ k i, (Fk k i).totalDegree ≤ D)
    (hconv : ∀ i s, Tendsto (fun k => (Fk k i).coeff s) atTop (𝓝 ((F i).coeff s)))
    (x0 : Fin d → ℂ) (h0 : ∀ i, eval x0 (F i) = 0)
    (hJ : (Matrix.of fun i j => eval x0 (pderiv j (F i))).det ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ k ≥ K, ∃ x : Fin d → ℂ, dist x x0 < ε ∧ (∀ i, eval x (Fk k i) = 0) ∧
      (Matrix.of fun i j => eval x (pderiv j (Fk k i))).det ≠ 0 := by
  obtain ⟨xk, hx, hgood⟩ := nondeg_zero_persist d D F Fk hdeg hconv x0 h0 hJ
  have hball : ∀ᶠ k in atTop, dist (xk k) x0 < ε := hx.eventually (Metric.ball_mem_nhds x0 hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hball.and hgood)
  exact ⟨K, fun k hk => ⟨xk k, (hK k hk).1, (hK k hk).2⟩⟩

/-- **Persistence of nondegenerate zeros.** If `Fk k → F` coefficientwise with total degrees
bounded by `D`, and `S` is a finite set of nondegenerate zeros of `F`, then for all large `k`
the map `Fk k` has a set of nondegenerate zeros of the same cardinality. -/
theorem nondeg_zeros_persist (d : ℕ) (D : ℕ) (F : Fin d → MvPolynomial (Fin d) ℂ)
    (Fk : ℕ → Fin d → MvPolynomial (Fin d) ℂ)
    (hdeg : ∀ k i, (Fk k i).totalDegree ≤ D)
    (hconv : ∀ i s, Filter.Tendsto (fun k => (Fk k i).coeff s) Filter.atTop
      (nhds ((F i).coeff s)))
    (S : Finset (Fin d → ℂ))
    (hS : ∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) :
    ∃ K, ∀ k ≥ K, ∃ T : Finset (Fin d → ℂ), T.card = S.card ∧
      ∀ x ∈ T, (∀ i, MvPolynomial.eval x (Fk k i) = 0) ∧
        (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (Fk k i))).det ≠ 0 := by
  classical
  have hex : ∀ x : Fin d → ℂ, ∃ xk : ℕ → (Fin d → ℂ), x ∈ S → (Tendsto xk atTop (𝓝 x) ∧
      ∀ᶠ k in atTop, (∀ i, eval (xk k) (Fk k i) = 0) ∧
        (Matrix.of fun i j => eval (xk k) (pderiv j (Fk k i))).det ≠ 0) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨xk, h1, h2⟩ :=
        nondeg_zero_persist d D F Fk hdeg hconv x (hS x hx).1 (hS x hx).2
      exact ⟨xk, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => x, fun h => absurd h hx⟩
  choose g hg using hex
  have hgood : ∀ᶠ k in atTop, ∀ x ∈ S, (∀ i, eval (g x k) (Fk k i) = 0) ∧
      (Matrix.of fun i j => eval (g x k) (pderiv j (Fk k i))).det ≠ 0 :=
    (eventually_all_finset S).2 fun x hx => (hg x hx).2
  have hinj : ∀ᶠ k in atTop, ∀ x ∈ S, ∀ y ∈ S, x ≠ y → g x k ≠ g y k := by
    refine (eventually_all_finset S).2 fun x hx => (eventually_all_finset S).2 fun y hy => ?_
    by_cases hxy : x = y
    · exact Eventually.of_forall fun k h => absurd hxy h
    · have ht : Tendsto (fun k => (g x k, g y k)) atTop (𝓝 (x, y)) :=
        (hg x hx).1.prodMk_nhds (hg y hy).1
      have hopen : {p : (Fin d → ℂ) × (Fin d → ℂ) | p.1 ≠ p.2} ∈ 𝓝 (x, y) :=
        isClosed_diagonal.isOpen_compl.mem_nhds hxy
      filter_upwards [ht.eventually hopen] with k hk _ using hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hgood.and hinj)
  refine ⟨K, fun k hk => ⟨S.image fun x => g x k, ?_, ?_⟩⟩
  · apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    by_contra hne
    exact (hK k hk).2 x hx y hy hne hxy
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact (hK k hk).1 x hx

end

end PEqualNP.Gct.Helpers
