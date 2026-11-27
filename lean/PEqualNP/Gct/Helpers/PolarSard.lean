import PEqualNP.Gct.Helpers.PolarGeneric
import PEqualNP.Gct.Helpers.Persist

/-!
# Generic polar directions of a smooth form give independent gradients (H4)

For a smooth form `G` of degree `r` in `h + 2` variables there are directions `v_1, .., v_h`
such that at every nonzero common zero `x` of `G, D_{v_1} G, .., D_{v_h} G` the gradients of
these `h + 1` forms at `x` are linearly independent.

The proof takes parametric transversality as a hypothesis (`h4_of`). In the chart `x_{j1} = 1`
the map `(y, V) ↦ (G(x(y)), (D_{V_k} G (x(y)))_k)` has a surjective derivative at each zero:
the `V` directions cover the last `h` components because the gradient of `G` does not vanish,
and the `y` directions cover the first because of Euler's identity. Parametric transversality
then says that for almost every `V` the partial derivative in `y` is injective at every zero,
which is the independence of the gradients truncated to the chart, hence of the gradients.
Finitely many charts cover the nonzero points up to scaling, and both the zero set and the
independence are invariant under scaling.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

noncomputable section

/-- The chart `x_{j1} = 1`: the point whose coordinate `j1` is `1` and whose other coordinates
are given by `y`. -/
def polarChart {h : ℕ} (j1 : Fin (h + 2)) (y : Fin (h + 1) → ℂ) : Fin (h + 2) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) j1 (1 : ℂ) y

theorem polarChart_self {h : ℕ} (j1 : Fin (h + 2)) (y : Fin (h + 1) → ℂ) :
    polarChart j1 y j1 = 1 := by
  simp [polarChart]

theorem polarChart_succAbove {h : ℕ} (j1 : Fin (h + 2)) (y : Fin (h + 1) → ℂ)
    (i : Fin (h + 1)) : polarChart j1 y (j1.succAbove i) = y i := by
  simp [polarChart]

theorem hasFDerivAt_polarChart {h : ℕ} (j1 : Fin (h + 2)) (y : Fin (h + 1) → ℂ) :
    HasFDerivAt (polarChart j1)
      (ContinuousLinearMap.pi (Fin.insertNth (α := fun _ => (Fin (h + 1) → ℂ) →L[ℂ] ℂ) j1 0
        (fun i => ContinuousLinearMap.proj i))) y := by
  have key : ∀ l : Fin (h + 2), HasFDerivAt (fun y : Fin (h + 1) → ℂ => polarChart j1 y l)
      (Fin.insertNth (α := fun _ => (Fin (h + 1) → ℂ) →L[ℂ] ℂ) j1 0
        (fun i => ContinuousLinearMap.proj i) l) y := by
    intro l
    rcases Fin.eq_self_or_eq_succAbove j1 l with rfl | ⟨i, rfl⟩
    · simp only [polarChart_self, Fin.insertNth_apply_same]
      exact hasFDerivAt_const _ _
    · simp only [polarChart_succAbove, Fin.insertNth_apply_succAbove]
      exact hasFDerivAt_apply i y
  exact hasFDerivAt_pi.2 key

theorem contDiff_polarChart {h : ℕ} (j1 : Fin (h + 2)) : ContDiff ℂ 1 (polarChart (h := h) j1) := by
  refine contDiff_pi.2 fun l => ?_
  rcases Fin.eq_self_or_eq_succAbove j1 l with rfl | ⟨i, rfl⟩
  · simp only [polarChart_self]
    exact contDiff_const
  · simp only [polarChart_succAbove]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (h + 1) => ℂ) i).contDiff

/-- The derivative of a polynomial along the chart. -/
theorem hasFDerivAt_eval_polarChart {h : ℕ} (j1 : Fin (h + 2)) (p : MvPolynomial (Fin (h + 2)) ℂ)
    (y : Fin (h + 1) → ℂ) :
    HasFDerivAt (fun y : Fin (h + 1) → ℂ => eval (polarChart j1 y) p)
      (∑ i, eval (polarChart j1 y) (pderiv (j1.succAbove i) p) •
        (ContinuousLinearMap.proj i : (Fin (h + 1) → ℂ) →L[ℂ] ℂ)) y := by
  have hEq : (∑ i, eval (polarChart j1 y) (pderiv (j1.succAbove i) p) •
      (ContinuousLinearMap.proj i : (Fin (h + 1) → ℂ) →L[ℂ] ℂ)) =
      (∑ j, eval (polarChart j1 y) (pderiv j p) •
        (ContinuousLinearMap.proj j : (Fin (h + 2) → ℂ) →L[ℂ] ℂ)).comp
      (ContinuousLinearMap.pi (Fin.insertNth (α := fun _ => (Fin (h + 1) → ℂ) →L[ℂ] ℂ) j1 0
        (fun i => ContinuousLinearMap.proj i))) := by
    refine ContinuousLinearMap.ext fun dy => ?_
    simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply,
      Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.coe_pi']
    rw [Fin.sum_univ_succAbove _ j1]
    simp
  rw [hEq]
  exact (hasFDerivAt_eval p (polarChart j1 y)).comp y (hasFDerivAt_polarChart j1 y)

theorem eval_polarD {n h : ℕ} (G : MvPolynomial (Fin n) ℂ) (v : Fin h → Fin n → ℂ) (k : Fin h)
    (x : Fin n → ℂ) : eval x (polarD G v k) = ∑ j, v k j * eval x (pderiv j G) := by
  simp [polarD, map_sum]

/-- The gradients of `G, D_{v_1} G, .., D_{v_h} G` at `x`. -/
def polarRows {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (v : Fin h → Fin (h + 2) → ℂ)
    (x : Fin (h + 2) → ℂ) : Fin (h + 1) → Fin (h + 2) → ℂ :=
  Fin.cons (fun j => eval x (pderiv j G)) (fun k j => eval x (pderiv j (polarD G v k)))

/-- The polar system in the chart, as a function of the chart point and the directions. -/
def polarMap {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2))
    (z : (Fin (h + 1) → ℂ) × (Fin h → Fin (h + 2) → ℂ)) : Fin (h + 1) → ℂ :=
  Fin.cons (eval (polarChart j1 z.1) G) (fun k => eval (polarChart j1 z.1) (polarD G z.2 k))

/-- The partial derivative of the polar system in the chart point. -/
def polarA {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2))
    (v : Fin h → Fin (h + 2) → ℂ) (y : Fin (h + 1) → ℂ) :
    (Fin (h + 1) → ℂ) →L[ℂ] (Fin (h + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ i', polarRows G v (polarChart j1 y) i (j1.succAbove i') •
    (ContinuousLinearMap.proj i' : (Fin (h + 1) → ℂ) →L[ℂ] ℂ)

theorem polarA_apply {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2))
    (v : Fin h → Fin (h + 2) → ℂ) (y dy : Fin (h + 1) → ℂ) (i : Fin (h + 1)) :
    polarA G j1 v y dy i = ∑ i', polarRows G v (polarChart j1 y) i (j1.succAbove i') * dy i' := by
  simp [polarA]

/-- The partial derivative of the polar system in the directions. -/
def polarB {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (x : Fin (h + 2) → ℂ) :
    (Fin h → Fin (h + 2) → ℂ) →L[ℂ] (Fin (h + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons 0 fun k => ∑ j, eval x (pderiv j G) •
    ((ContinuousLinearMap.proj j : (Fin (h + 2) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj k : (Fin h → Fin (h + 2) → ℂ) →L[ℂ] (Fin (h + 2) → ℂ))))

theorem polarB_apply_zero {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (x : Fin (h + 2) → ℂ)
    (dv : Fin h → Fin (h + 2) → ℂ) : polarB G x dv 0 = 0 := by
  simp [polarB]

theorem polarB_apply_succ {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (x : Fin (h + 2) → ℂ)
    (dv : Fin h → Fin (h + 2) → ℂ) (k : Fin h) :
    polarB G x dv k.succ = ∑ j, eval x (pderiv j G) * dv k j := by
  simp [polarB]

theorem hasFDerivAt_polarMap_left {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2))
    (v : Fin h → Fin (h + 2) → ℂ) (y : Fin (h + 1) → ℂ) :
    HasFDerivAt (fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v)) (polarA G j1 v y) y := by
  have key : ∀ i : Fin (h + 1), HasFDerivAt (fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v) i)
      (∑ i', polarRows G v (polarChart j1 y) i (j1.succAbove i') •
        (ContinuousLinearMap.proj i' : (Fin (h + 1) → ℂ) →L[ℂ] ℂ)) y := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hasFDerivAt_eval_polarChart j1 G y
    · exact hasFDerivAt_eval_polarChart j1 (polarD G v k) y
  exact hasFDerivAt_pi.2 key

theorem hasFDerivAt_polarMap_right {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2))
    (v : Fin h → Fin (h + 2) → ℂ) (y : Fin (h + 1) → ℂ) :
    HasFDerivAt (fun v' : Fin h → Fin (h + 2) → ℂ => polarMap G j1 (y, v'))
      (polarB G (polarChart j1 y)) v := by
  have key : ∀ i : Fin (h + 1),
      HasFDerivAt (fun v' : Fin h → Fin (h + 2) → ℂ => polarMap G j1 (y, v') i)
      ((Fin.cons 0 fun k => ∑ j, eval (polarChart j1 y) (pderiv j G) •
        ((ContinuousLinearMap.proj j : (Fin (h + 2) → ℂ) →L[ℂ] ℂ).comp
          (ContinuousLinearMap.proj k : (Fin h → Fin (h + 2) → ℂ) →L[ℂ] (Fin (h + 2) → ℂ))) :
        Fin (h + 1) → ((Fin h → Fin (h + 2) → ℂ) →L[ℂ] ℂ)) i) v := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hasFDerivAt_const (eval (polarChart j1 y) G) v
    · have hfun : (fun v' : Fin h → Fin (h + 2) → ℂ => polarMap G j1 (y, v') k.succ) =
          ⇑(∑ j, eval (polarChart j1 y) (pderiv j G) •
            ((ContinuousLinearMap.proj j : (Fin (h + 2) → ℂ) →L[ℂ] ℂ).comp
              (ContinuousLinearMap.proj k :
                (Fin h → Fin (h + 2) → ℂ) →L[ℂ] (Fin (h + 2) → ℂ)))) := by
        funext v'
        simp [polarMap, eval_polarD, mul_comm]
      rw [hfun]
      exact ContinuousLinearMap.hasFDerivAt _
  exact hasFDerivAt_pi.2 key

theorem contDiff_polarMap {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ) (j1 : Fin (h + 2)) :
    ContDiff ℂ 1 (polarMap G j1) := by
  have hc : ContDiff ℂ 1
      (fun z : (Fin (h + 1) → ℂ) × (Fin h → Fin (h + 2) → ℂ) => polarChart j1 z.1) :=
    (contDiff_polarChart j1).comp contDiff_fst
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (contDiff_eval G).comp hc
  · have hfun : (fun z : (Fin (h + 1) → ℂ) × (Fin h → Fin (h + 2) → ℂ) =>
        polarMap G j1 z k.succ) =
        fun z => ∑ j, z.2 k j * eval (polarChart j1 z.1) (pderiv j G) := by
      funext z
      simp [polarMap, eval_polarD]
    rw [hfun]
    refine ContDiff.sum fun j _ => ContDiff.mul ?_ ((contDiff_eval _).comp hc)
    fun_prop

/-- **Surjectivity of the total derivative at a zero.** -/
theorem polarMap_fderiv_surjective {h r : ℕ} {G : MvPolynomial (Fin (h + 2)) ℂ}
    (hG : G.IsHomogeneous r) (hsm : ∀ x, (∀ i, eval x (pderiv i G) = 0) → x = 0)
    (j1 : Fin (h + 2)) (z : (Fin (h + 1) → ℂ) × (Fin h → Fin (h + 2) → ℂ))
    (hz : polarMap G j1 z = 0) : Function.Surjective (fderiv ℝ (polarMap G j1) z) := by
  obtain ⟨y, v⟩ := z
  have hGx : eval (polarChart j1 y) G = 0 := congrFun hz 0
  have hx1 : polarChart j1 y j1 = 1 := polarChart_self j1 y
  -- the gradient truncated to the chart is not zero, by Euler's identity
  have h0 : ∃ i0, eval (polarChart j1 y) (pderiv (j1.succAbove i0) G) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hE := eval_euler hG (polarChart j1 y)
    rw [hGx, mul_zero, Fin.sum_univ_succAbove _ j1] at hE
    simp only [hcon, mul_zero, Finset.sum_const_zero, add_zero, hx1, one_mul] at hE
    have hx0 : polarChart j1 y = 0 := hsm _ fun l => by
      rcases Fin.eq_self_or_eq_succAbove j1 l with rfl | ⟨i, rfl⟩
      · exact hE
      · exact hcon i
    rw [hx0] at hx1
    simp at hx1
  obtain ⟨i0, hi0⟩ := h0
  have hD : HasFDerivAt (polarMap G j1) (fderiv ℂ (polarMap G j1) (y, v)) (y, v) :=
    (((contDiff_polarMap G j1).differentiable one_ne_zero) (y, v)).hasFDerivAt
  have hR : fderiv ℝ (polarMap G j1) (y, v) =
      (fderiv ℂ (polarMap G j1) (y, v)).restrictScalars ℝ := (hD.restrictScalars ℝ).fderiv
  have hl : (fderiv ℂ (polarMap G j1) (y, v)).comp
      (ContinuousLinearMap.inl ℂ (Fin (h + 1) → ℂ) (Fin h → Fin (h + 2) → ℂ)) =
      polarA G j1 v y :=
    HasFDerivAt.unique (f := fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v))
      (HasFDerivAt.comp (g := polarMap G j1)
        (f := fun e : Fin (h + 1) → ℂ => (e, v)) y hD (hasFDerivAt_prodMk_left y v))
      (hasFDerivAt_polarMap_left G j1 v y)
  have hr : (fderiv ℂ (polarMap G j1) (y, v)).comp
      (ContinuousLinearMap.inr ℂ (Fin (h + 1) → ℂ) (Fin h → Fin (h + 2) → ℂ)) =
      polarB G (polarChart j1 y) :=
    HasFDerivAt.unique (f := fun v' : Fin h → Fin (h + 2) → ℂ => polarMap G j1 (y, v'))
      (HasFDerivAt.comp (g := polarMap G j1)
        (f := fun e : Fin h → Fin (h + 2) → ℂ => (y, e)) v hD (hasFDerivAt_prodMk_right y v))
      (hasFDerivAt_polarMap_right G j1 v y)
  intro w
  obtain ⟨dy, hdy⟩ : ∃ dy : Fin (h + 1) → ℂ, dy = Pi.single i0
      (w 0 / eval (polarChart j1 y) (pderiv (j1.succAbove i0) G)) := ⟨_, rfl⟩
  obtain ⟨dv, hdv⟩ : ∃ dv : Fin h → Fin (h + 2) → ℂ, dv = fun k => Pi.single (j1.succAbove i0)
      ((w k.succ - polarA G j1 v y dy k.succ) /
        eval (polarChart j1 y) (pderiv (j1.succAbove i0) G)) := ⟨_, rfl⟩
  refine ⟨(dy, dv), ?_⟩
  rw [hR]
  show fderiv ℂ (polarMap G j1) (y, v) (dy, dv) = w
  have hsplit : ((dy, dv) : (Fin (h + 1) → ℂ) × (Fin h → Fin (h + 2) → ℂ)) =
      (dy, 0) + (0, dv) := by simp
  have e1 : fderiv ℂ (polarMap G j1) (y, v) (dy, 0) = polarA G j1 v y dy := by
    rw [← hl]; rfl
  have e2 : fderiv ℂ (polarMap G j1) (y, v) (0, dv) = polarB G (polarChart j1 y) dv := by
    rw [← hr]; rfl
  rw [hsplit, map_add, e1, e2]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [Pi.add_apply, polarB_apply_zero, add_zero, polarA_apply,
      Finset.sum_eq_single i0 (fun b _ hb => by simp [hdy, hb]) (by simp)]
    simp only [polarRows, Fin.cons_zero, hdy, Pi.single_eq_same]
    field_simp
  · rw [Pi.add_apply, polarB_apply_succ,
      Finset.sum_eq_single (j1.succAbove i0) (fun b _ hb => by simp [hdv, hb]) (by simp)]
    simp only [hdv, Pi.single_eq_same]
    field_simp
    ring

/-- **From the chart to the gradients.** If the partial derivative of the polar system in the
chart point is injective, the gradients at that point are linearly independent. -/
theorem polarRows_linearIndependent_of_injective {h : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (j1 : Fin (h + 2)) (v : Fin h → Fin (h + 2) → ℂ) (y : Fin (h + 1) → ℂ)
    (hinj : Function.Injective
      (fderiv ℝ (fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v)) y)) :
    LinearIndependent ℂ (polarRows G v (polarChart j1 y)) := by
  have hA : fderiv ℝ (fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v)) y =
      (polarA G j1 v y).restrictScalars ℝ :=
    ((hasFDerivAt_polarMap_left G j1 v y).restrictScalars ℝ).fderiv
  rw [hA] at hinj
  have hinjA : Function.Injective (polarA G j1 v y) := hinj
  have hM : Function.Injective (Matrix.of fun i i' : Fin (h + 1) =>
      polarRows G v (polarChart j1 y) i (j1.succAbove i')).mulVec := by
    intro a b hab
    apply hinjA
    funext i
    simpa [polarA_apply, Matrix.mulVec, dotProduct] using congrFun hab i
  have hv := Matrix.vecMul_injective_iff_isUnit.2 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hvec : Matrix.vecMul g (Matrix.of fun i i' : Fin (h + 1) =>
      polarRows G v (polarChart j1 y) i (j1.succAbove i')) =
      Matrix.vecMul 0 (Matrix.of fun i i' : Fin (h + 1) =>
        polarRows G v (polarChart j1 y) i (j1.succAbove i')) := by
    funext i'
    have := congrFun hg (j1.succAbove i')
    simpa [Matrix.vecMul, dotProduct] using this
  exact fun i => congrFun (hv hvec) i

/-- The gradients scale row by row under scaling of the point. -/
theorem polarRows_smul {h r : ℕ} {G : MvPolynomial (Fin (h + 2)) ℂ} (hG : G.IsHomogeneous r)
    (v : Fin h → Fin (h + 2) → ℂ) (c : ℂ) (x : Fin (h + 2) → ℂ) (i : Fin (h + 1)) :
    polarRows G v (c • x) i =
      (Fin.cons (c ^ (r - 1)) (fun _ => c ^ (r - 1 - 1)) : Fin (h + 1) → ℂ) i •
        polarRows G v x i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · funext j
    simp only [polarRows, Fin.cons_zero, Pi.smul_apply, smul_eq_mul]
    exact (hG.pderiv (i := j)).eval_smul c x
  · funext j
    simp only [polarRows, Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
    exact ((polarD_isHomogeneous hG v k).pderiv (i := j)).eval_smul c x

set_option synthInstance.maxHeartbeats 400000 in
/-- The space of directions carries an additive Haar measure. -/
theorem exists_isAddHaarMeasure_polar (h : ℕ) :
    ∃ μ : MeasureTheory.Measure (Fin h → Fin (h + 2) → ℂ), μ.IsAddHaarMeasure :=
  ⟨MeasureTheory.Measure.addHaar, inferInstance⟩

/-- **H4 from parametric transversality.** -/
theorem h4_of
    (hPT : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      [MeasurableSpace P] [BorelSpace P] (μ : MeasureTheory.Measure P) [μ.IsAddHaarMeasure]
      (f : E × P → E), ContDiff ℝ 1 f →
      (∀ z : E × P, f z = 0 → Function.Surjective (fderiv ℝ f z)) →
      ∀ᵐ c ∂μ, ∀ y : E, f (y, c) = 0 →
        Function.Injective (fderiv ℝ (fun y' : E => f (y', c)) y)) :
    ∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ v : Fin h → Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, x ≠ 0 → MvPolynomial.eval x G = 0 → (∀ k, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → LinearIndependent ℂ (Fin.cons (fun j => MvPolynomial.eval x (MvPolynomial.pderiv j G)) (fun k j => MvPolynomial.eval x (MvPolynomial.pderiv j (∑ l, MvPolynomial.C (v k l) * MvPolynomial.pderiv l G))) : Fin (h + 1) → Fin (h + 2) → ℂ) := by
  intro h r G _ hG hsm
  obtain ⟨μ, hμ⟩ := exists_isAddHaarMeasure_polar h
  have key : ∀ j1 : Fin (h + 2), ∀ᵐ v ∂μ,
      ∀ y : Fin (h + 1) → ℂ, polarMap G j1 (y, v) = 0 →
        Function.Injective (fderiv ℝ (fun y' : Fin (h + 1) → ℂ => polarMap G j1 (y', v)) y) :=
    fun j1 => hPT (Fin (h + 1) → ℂ) (Fin h → Fin (h + 2) → ℂ) μ
      (polarMap G j1) ((contDiff_polarMap G j1).restrict_scalars ℝ)
      (fun z hz => polarMap_fderiv_surjective hG hsm j1 z hz)
  obtain ⟨v, hv⟩ := (MeasureTheory.ae_all_iff.2 key).exists
  refine ⟨v, fun x hx hGx hDx => ?_⟩
  obtain ⟨j1, hj1⟩ : ∃ j1, x j1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hc0 : (x j1)⁻¹ ≠ 0 := inv_ne_zero hj1
  have hx1 : ((x j1)⁻¹ • x) j1 = 1 := by
    simp [hj1]
  have hch : polarChart j1 (j1.removeNth ((x j1)⁻¹ • x)) = (x j1)⁻¹ • x := by
    have := Fin.insertNth_self_removeNth j1 ((x j1)⁻¹ • x)
    rw [hx1] at this
    exact this
  have hzero : polarMap G j1 (j1.removeNth ((x j1)⁻¹ • x), v) = 0 := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · show eval (polarChart j1 (j1.removeNth ((x j1)⁻¹ • x))) G = 0
      rw [hch, hG.eval_smul, hGx, mul_zero]
    · show eval (polarChart j1 (j1.removeNth ((x j1)⁻¹ • x))) (polarD G v k) = 0
      rw [hch, (polarD_isHomogeneous hG v k).eval_smul]
      have : eval x (polarD G v k) = 0 := hDx k
      rw [this, mul_zero]
  have hind := polarRows_linearIndependent_of_injective G j1 v _ (hv j1 _ hzero)
  rw [hch] at hind
  have hu : ∀ i : Fin (h + 1),
      (Fin.cons ((x j1)⁻¹ ^ (r - 1)) (fun _ => (x j1)⁻¹ ^ (r - 1 - 1)) : Fin (h + 1) → ℂ) i ≠ 0 := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact pow_ne_zero _ hc0
    · exact pow_ne_zero _ hc0
  have hfin : LinearIndependent ℂ (polarRows G v x) := by
    have := hind.units_smul fun i => (Units.mk0 _ (hu i))⁻¹
    convert this using 1
    funext i
    rw [Pi.smul_apply', polarRows_smul hG, Units.smul_def, smul_smul,
      Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ (hu i), one_smul]
  exact hfin

end

end PEqualNP.Gct.Helpers
