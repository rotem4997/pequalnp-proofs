import PEqualNP.Gct.Helpers.ParamTrans
import PEqualNP.Gct.Helpers.PolarSard
import PEqualNP.Gct.Helpers.ChainRule

/-!
# A smooth linear section from a transversal subspace

Let `G` be a form of degree `r` in `N` variables and `L` a linear map from `d` variables such
that the full gradient of `G` vanishes on the image of `L` only at `L 0`. Then for some linear
map `M` the form `G ∘ M` in `d` variables is smooth.

The proof works with the map `F (y, M) = M^T g (M y)`, the gradient of `G ∘ M` at `y`, where `g`
is the gradient of `G`. No charts are used.

* The parameters `M` with `g (M y) ≠ 0` for all `y ≠ 0` contain a neighbourhood of `L`
  (compactness of the unit sphere).
* At a zero `(y, M)` of `F` with `y ≠ 0` and `g (M y) ≠ 0` the total derivative of `F` is onto.
  Pick `w` with `w . g (M y) = 1` and move `M` in the directions `w ⊗ c`. If `c . y = 0` the
  point `M y` does not move and the derivative is `c`. If `c . y = 1` then, by Euler's identity
  `y . F (y, M) = r G (M y)`, the derivative `τ` has `y . τ = r ≠ 0`.
* Parametric transversality on the set of such pairs: for almost every `M`, at each such zero
  the derivative of `F (., M)` is injective. But `F (., M)` is homogeneous, so it vanishes on
  the whole line through a zero `y` and its derivative kills `y`. So there is no such zero.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial MeasureTheory Set Topology

noncomputable section

/-- Parametric transversality on a set: only the zeros in `S` are assumed transversal, and only
those are concluded nondegenerate. -/
theorem param_transversality_on
    (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P] (μ : MeasureTheory.Measure P) [μ.IsAddHaarMeasure]
    (f : E × P → E) (hf : ContDiff ℝ 1 f) (S : Set (E × P))
    (hsurj : ∀ z : E × P, z ∈ S → f z = 0 → Function.Surjective (fderiv ℝ f z)) :
    ∀ᵐ c ∂μ, ∀ y : E, (y, c) ∈ S → f (y, c) = 0 →
      Function.Injective (fderiv ℝ (fun y' : E => f (y', c)) y) := by
  have hslice : ∀ y c, fderiv ℝ (fun y' : E => f (y', c)) y =
      (fderiv ℝ f (y, c)).comp (ContinuousLinearMap.inl ℝ E P) := fun y c =>
    ((hf.differentiable one_ne_zero (y, c)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y c)).fderiv
  choose W hWo hWm hWn using fun z : {z : E × P // z ∈ S ∧ f z = 0} =>
    pt_local E P μ f hf z.1 (hsurj z.1 z.2.1 z.2.2)
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  rw [ae_iff]
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hT).2 fun i _ => hWn i)
  intro c hc
  simp only [mem_ofPred_eq, not_forall] at hc
  obtain ⟨y, hyS, hy, hni⟩ := hc
  have hmem : (y, c) ∈ ⋃ i ∈ T, W i := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨(y, c), hyS, hy⟩, hWm _⟩
  obtain ⟨i, hi, hiW⟩ := mem_iUnion₂.1 hmem
  refine mem_iUnion₂.2 ⟨i, hi, y, hiW, hy, ?_⟩
  rwa [← hslice]

/-- The linear map with matrix `M`. -/
def tsApply {N d : ℕ} (M : Fin N → Fin d → ℂ) (y : Fin d → ℂ) : Fin N → ℂ :=
  fun n => ∑ s, M n s * y s

/-- The gradient of `G ∘ M` at `y`, as a function of the pair `(y, M)`. -/
def tsMap {N d : ℕ} (G : MvPolynomial (Fin N) ℂ)
    (z : (Fin d → ℂ) × (Fin N → Fin d → ℂ)) : Fin d → ℂ :=
  fun s => ∑ n, z.2 n s * eval (tsApply z.2 z.1) (pderiv n G)

theorem tsApply_smul {N d : ℕ} (M : Fin N → Fin d → ℂ) (c : ℂ) (y : Fin d → ℂ) :
    tsApply M (c • y) = c • tsApply M y := by
  funext n
  simp only [tsApply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem tsApply_add_rank_one {N d : ℕ} (M : Fin N → Fin d → ℂ) (w : Fin N → ℂ)
    (c y : Fin d → ℂ) (t : ℂ) :
    tsApply (M + t • fun n s => w n * c s) y = tsApply M y + (t * ∑ s, c s * y s) • w := by
  funext n
  simp only [tsApply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

theorem continuous_tsApply {N d : ℕ} :
    Continuous (fun z : (Fin N → Fin d → ℂ) × (Fin d → ℂ) => tsApply z.1 z.2) := by
  unfold tsApply
  fun_prop

theorem contDiff_tsMap {N d : ℕ} (G : MvPolynomial (Fin N) ℂ) :
    ContDiff ℂ 1 (tsMap (d := d) G) := by
  have hc : ContDiff ℂ 1
      (fun z : (Fin d → ℂ) × (Fin N → Fin d → ℂ) => tsApply z.2 z.1) := by
    unfold tsApply
    fun_prop
  refine contDiff_pi.2 fun s => ?_
  unfold tsMap
  refine ContDiff.sum fun n _ => ContDiff.mul ?_ ((contDiff_eval _).comp hc)
  fun_prop

theorem tsMap_smul {N d r : ℕ} {G : MvPolynomial (Fin N) ℂ} (hG : G.IsHomogeneous r)
    (c : ℂ) (y : Fin d → ℂ) (M : Fin N → Fin d → ℂ) :
    tsMap G (c • y, M) = c ^ (r - 1) • tsMap G (y, M) := by
  funext s
  simp only [tsMap, Pi.smul_apply, smul_eq_mul, tsApply_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [(hG.pderiv (i := n)).eval_smul]
  ring

/-- Euler's identity for the section: `y . F (y, M) = r G (M y)`. -/
theorem tsMap_dot {N d r : ℕ} {G : MvPolynomial (Fin N) ℂ} (hG : G.IsHomogeneous r)
    (y : Fin d → ℂ) (M : Fin N → Fin d → ℂ) :
    ∑ s, y s * tsMap G (y, M) s = (r : ℂ) * eval (tsApply M y) G := by
  rw [← eval_euler hG]
  simp only [tsMap, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [tsApply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The gradient of `G ∘ M` in the `bind₁` form is the map `tsMap`. -/
theorem eval_pderiv_bind₁_lin {N d : ℕ} (G : MvPolynomial (Fin N) ℂ)
    (M : Fin N → Fin d → ℂ) (y : Fin d → ℂ) (s : Fin d) :
    eval y (pderiv s (bind₁ (fun n => ∑ t, C (M n t) * X t) G)) = tsMap G (y, M) s := by
  rw [pderiv_bind₁, map_sum]
  show _ = ∑ n, M n s * eval (tsApply M y) (pderiv n G)
  refine Finset.sum_congr rfl fun n _ => ?_
  have hev : eval y (bind₁ (fun n => ∑ t, C (M n t) * X t) (pderiv n G)) =
      eval (tsApply M y) (pderiv n G) := by
    show eval₂Hom (RingHom.id ℂ) y _ = _
    rw [eval₂Hom_bind₁]
    have : (fun i => eval₂Hom (RingHom.id ℂ) y (∑ t, C (M i t) * X t)) = tsApply M y := by
      funext i
      simp [tsApply]
    rw [this]
    rfl
  have hd : eval y (pderiv s (∑ t, C (M n t) * X t : MvPolynomial (Fin d) ℂ)) = M n s := by
    simp [pderiv_X, Pi.single_apply, apply_ite, Finset.sum_ite_eq]
  rw [map_mul, hev, hd]
  ring

/-- The good parameters contain a neighbourhood of `L`. -/
theorem ts_eventually {N d : ℕ} (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ)
    (hL : ∀ y : Fin d → ℂ, (∀ i, eval (tsApply L y) (pderiv i G) = 0) → y = 0) :
    ∀ᶠ M in 𝓝 L, ∀ y ∈ Metric.sphere (0 : Fin d → ℂ) 1,
      ∃ i, eval (tsApply M y) (pderiv i G) ≠ 0 := by
  apply (isCompact_sphere (0 : Fin d → ℂ) 1).eventually_forall_of_forall_eventually
  intro y hy
  have hopen : IsOpen {z : (Fin N → Fin d → ℂ) × (Fin d → ℂ) |
      ∃ i, eval (tsApply z.1 z.2) (pderiv i G) ≠ 0} := by
    simp only [Set.setOf_exists]
    exact isOpen_iUnion fun i => isOpen_ne_fun
      ((contDiff_eval (pderiv i G)).continuous.comp continuous_tsApply) continuous_const
  refine hopen.mem_nhds ?_
  show ∃ i, eval (tsApply L y) (pderiv i G) ≠ 0
  by_contra hcon
  push Not at hcon
  have hy0 := hL y hcon
  rw [hy0] at hy
  simp at hy

/-- From the unit sphere to all nonzero points. -/
theorem ts_ne_of_sphere {N d r : ℕ} {G : MvPolynomial (Fin N) ℂ} (hG : G.IsHomogeneous r)
    {M : Fin N → Fin d → ℂ}
    (hM : ∀ y ∈ Metric.sphere (0 : Fin d → ℂ) 1, ∃ i, eval (tsApply M y) (pderiv i G) ≠ 0)
    {y : Fin d → ℂ} (hy : y ≠ 0) : ∃ i, eval (tsApply M y) (pderiv i G) ≠ 0 := by
  obtain ⟨i, hi⟩ := hM (((‖y‖ : ℂ)⁻¹) • y) (by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (𝕜 := ℂ) hy)
  refine ⟨i, fun h0 => hi ?_⟩
  rw [tsApply_smul, (hG.pderiv (i := i)).eval_smul, h0, mul_zero]

/-- **Surjectivity of the total derivative** at a zero `(y, M)` with `y ≠ 0` and
`g (M y) ≠ 0`. -/
theorem tsMap_fderiv_surjective {N d r : ℕ} {G : MvPolynomial (Fin N) ℂ}
    (hG : G.IsHomogeneous r) (hr : r ≠ 0) (y : Fin d → ℂ) (M : Fin N → Fin d → ℂ)
    (hy : y ≠ 0) (hg : ∃ i, eval (tsApply M y) (pderiv i G) ≠ 0)
    (hz : tsMap G (y, M) = 0) : Function.Surjective (fderiv ℝ (tsMap G) (y, M)) := by
  obtain ⟨i0, hi0⟩ := hg
  obtain ⟨s0, hs0⟩ : ∃ s0, y s0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (funext hc)
  obtain ⟨w, hwdef⟩ : ∃ w : Fin N → ℂ,
      w = Pi.single i0 (eval (tsApply M y) (pderiv i0 G))⁻¹ := ⟨_, rfl⟩
  have hw : ∑ n, w n * eval (tsApply M y) (pderiv n G) = 1 := by
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hwdef, hb]) (by simp)]
    simp [hwdef, hi0]
  obtain ⟨A, hAdef⟩ : ∃ A, A = fderiv ℂ (tsMap (d := d) G) (y, M) := ⟨_, rfl⟩
  have hD : HasFDerivAt (tsMap G) A (y, M) := by
    rw [hAdef]
    exact (((contDiff_tsMap G).differentiable one_ne_zero) (y, M)).hasFDerivAt
  have hR : fderiv ℝ (tsMap G) (y, M) = A.restrictScalars ℝ := (hD.restrictScalars ℝ).fderiv
  -- the derivative along the line `M + t (w ⊗ c)`
  have hline : ∀ c : Fin d → ℂ,
      HasDerivAt (fun t : ℂ => tsMap G (y, M + t • fun n s => w n * c s))
        (A ((0 : Fin d → ℂ), fun n s => w n * c s)) 0 := by
    intro c
    have hγ : HasDerivAt (fun t : ℂ => ((y, M) : (Fin d → ℂ) × (Fin N → Fin d → ℂ)) +
        t • ((0 : Fin d → ℂ), fun n s => w n * c s))
        ((0 : Fin d → ℂ), fun n s => w n * c s) 0 := by
      have := ((hasDerivAt_id (0 : ℂ)).smul_const
        (((0 : Fin d → ℂ), fun n s => w n * c s) :
          (Fin d → ℂ) × (Fin N → Fin d → ℂ))).const_add
        ((y, M) : (Fin d → ℂ) × (Fin N → Fin d → ℂ))
      simpa using this
    have hD' : HasFDerivAt (tsMap G) A (((y, M) : (Fin d → ℂ) × (Fin N → Fin d → ℂ)) +
        (0 : ℂ) • ((0 : Fin d → ℂ), fun n s => w n * c s)) := by
      rw [zero_smul, add_zero]
      exact hD
    have := HasFDerivAt.comp_hasDerivAt (0 : ℂ) hD' hγ
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show tsMap G (y, M + t • fun n s => w n * c s) = tsMap G ((y, M) + t • (0, _))
    simp
  -- directions `c` with `c . y = 0` are reproduced
  have h1 : ∀ c : Fin d → ℂ, ∑ s, c s * y s = 0 →
      A ((0 : Fin d → ℂ), fun n s => w n * c s) = c := by
    intro c hc
    have hfun : (fun t : ℂ => tsMap G (y, M + t • fun n s => w n * c s)) = fun t => t • c := by
      funext t s
      have hzs : ∑ n, M n s * eval (tsApply M y) (pderiv n G) = 0 := congrFun hz s
      simp only [tsMap, tsApply_add_rank_one, hc, mul_zero, zero_smul, add_zero, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, hzs, zero_add]
      calc ∑ n, t * (w n * c s) * eval (tsApply M y) (pderiv n G)
          = t * c s * ∑ n, w n * eval (tsApply M y) (pderiv n G) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun n _ => by ring
        _ = t * c s := by rw [hw, mul_one]
    have h := hline c
    rw [hfun] at h
    have h' : HasDerivAt (fun t : ℂ => t • c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const c
    exact h.unique h'
  -- one direction leaves the hyperplane `y . τ = 0`
  obtain ⟨c0, hc0def⟩ : ∃ c0 : Fin d → ℂ, c0 = Pi.single s0 (y s0)⁻¹ := ⟨_, rfl⟩
  have hc0 : ∑ s, c0 s * y s = 1 := by
    rw [Finset.sum_eq_single s0 (fun b _ hb => by simp [hc0def, hb]) (by simp)]
    simp [hc0def, hs0]
  obtain ⟨τ0, hτ0def⟩ : ∃ τ0, τ0 = A ((0 : Fin d → ℂ), fun n s => w n * c0 s) := ⟨_, rfl⟩
  have h2 : ∑ s, y s * τ0 s = (r : ℂ) := by
    have ha : HasDerivAt
        (fun t : ℂ => ∑ s, y s * tsMap G (y, M + t • fun n s => w n * c0 s) s)
        (∑ s, y s * τ0 s) 0 := by
      refine HasDerivAt.fun_sum fun s _ => HasDerivAt.const_mul (y s) ?_
      rw [hτ0def]
      exact hasDerivAt_pi.1 (hline c0) s
    have hfun : (fun t : ℂ => ∑ s, y s * tsMap G (y, M + t • fun n s => w n * c0 s) s) =
        fun t => (r : ℂ) * eval (tsApply M y + t • w) G := by
      funext t
      rw [tsMap_dot hG, tsApply_add_rank_one, hc0, mul_one]
    rw [hfun] at ha
    have hl : HasDerivAt (fun t : ℂ => tsApply M y + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const w).const_add (tsApply M y)
    have hE : HasFDerivAt (fun x : Fin N → ℂ => eval x G)
        (∑ j, eval (tsApply M y) (pderiv j G) •
          (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ)) (tsApply M y + (0 : ℂ) • w) := by
      rw [zero_smul, add_zero]
      exact hasFDerivAt_eval G (tsApply M y)
    have hb := (HasFDerivAt.comp_hasDerivAt (0 : ℂ) hE hl).const_mul (r : ℂ)
    have hval : (∑ j, eval (tsApply M y) (pderiv j G) •
        (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ)) w = 1 := by
      rw [← hw]
      simp [mul_comm]
    rw [hval, mul_one] at hb
    exact ha.unique hb
  intro τ
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = (∑ s, y s * τ s) / (r : ℂ) := ⟨_, rfl⟩
  have hc : ∑ s, (τ - a • τ0) s * y s = 0 := by
    have : ∑ s, (τ - a • τ0) s * y s = ∑ s, y s * τ s - a * ∑ s, y s * τ0 s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
    rw [this, h2, hadef]
    field_simp
    ring
  refine ⟨((0 : Fin d → ℂ), fun n s => w n * (τ - a • τ0) s) +
    a • ((0 : Fin d → ℂ), fun n s => w n * c0 s), ?_⟩
  rw [hR]
  show A (((0 : Fin d → ℂ), fun n s => w n * (τ - a • τ0) s) +
    a • ((0 : Fin d → ℂ), fun n s => w n * c0 s)) = τ
  rw [map_add, map_smul, h1 _ hc, ← hτ0def]
  simp

/-- **No nondegenerate zeros.** At a zero `y ≠ 0` the derivative of `F (., M)` kills `y`. -/
theorem tsMap_not_injective {N d r : ℕ} {G : MvPolynomial (Fin N) ℂ}
    (hG : G.IsHomogeneous r) (y : Fin d → ℂ) (M : Fin N → Fin d → ℂ) (hy : y ≠ 0)
    (hz : tsMap G (y, M) = 0) :
    ¬ Function.Injective (fderiv ℝ (fun y' : Fin d → ℂ => tsMap G (y', M)) y) := by
  intro hinj
  have hc : ContDiff ℝ 1 (fun y' : Fin d → ℂ => tsMap G (y', M)) :=
    ((contDiff_tsMap G).restrict_scalars ℝ).comp (contDiff_id.prodMk contDiff_const)
  have hfd : HasFDerivAt (fun y' : Fin d → ℂ => tsMap G (y', M))
      (fderiv ℝ (fun y' : Fin d → ℂ => tsMap G (y', M)) y) ((1 : ℝ) • y) := by
    rw [one_smul]
    exact (hc.differentiable one_ne_zero y).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have h := HasFDerivAt.comp_hasDerivAt (1 : ℝ) hfd hγ
  have hfun : ((fun y' : Fin d → ℂ => tsMap G (y', M)) ∘ fun t : ℝ => t • y) = fun _ => 0 := by
    funext t
    show tsMap G (t • y, M) = 0
    have : (t • y : Fin d → ℂ) = (t : ℂ) • y := by
      funext s
      simp
    rw [this, tsMap_smul hG, hz, smul_zero]
  rw [hfun] at h
  have h0 := h.unique (hasDerivAt_const (1 : ℝ) (0 : Fin d → ℂ))
  exact hy (hinj (h0.trans (map_zero _).symm))

set_option synthInstance.maxHeartbeats 400000 in
/-- The space of matrices carries an additive Haar measure. -/
theorem exists_isAddHaarMeasure_ts (N d : ℕ) :
    ∃ μ : MeasureTheory.Measure (Fin N → Fin d → ℂ), μ.IsAddHaarMeasure :=
  ⟨MeasureTheory.Measure.addHaar, inferInstance⟩

/-- **Smooth linear section from a transversal subspace.** -/
theorem transSection :
    ∀ (N d r : ℕ) (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ), G.IsHomogeneous r → (∀ y : Fin d → ℂ, (∀ i, MvPolynomial.eval (fun n => ∑ s, L n s * y s) (MvPolynomial.pderiv i G) = 0) → y = 0) → ∃ M : Fin N → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun n => ∑ t, MvPolynomial.C (M n t) * MvPolynomial.X t) G)) = 0) → y = 0 := by
  intro N d r G L hG hL
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- a constant has zero gradient, so the hypothesis already says every `y` is zero
    refine ⟨0, fun y _ => hL y fun i => ?_⟩
    have hC : G = C (G.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hG.totalDegree_le)
    rw [hC, pderiv_C, map_zero]
  · obtain ⟨μ, hμ⟩ := exists_isAddHaarMeasure_ts N d
    have key := param_transversality_on (Fin d → ℂ) (Fin N → Fin d → ℂ) μ (tsMap G)
      ((contDiff_tsMap G).restrict_scalars ℝ)
      {z | z.1 ≠ 0 ∧ ∃ i, eval (tsApply z.2 z.1) (pderiv i G) ≠ 0}
      (fun z hz hz0 => tsMap_fderiv_surjective hG hr.ne' z.1 z.2 hz.1 hz.2 hz0)
    obtain ⟨U, hUsub, hUo, hLU⟩ := mem_nhds_iff.1 (ts_eventually G L hL)
    have hpos : 0 < μ U := hUo.measure_pos μ ⟨L, hLU⟩
    obtain ⟨M, hMU, hM⟩ := ((frequently_ae_mem_iff.2 hpos.ne').and_eventually key).exists
    refine ⟨M, fun y hy => ?_⟩
    by_contra hy0
    have hz : tsMap G (y, M) = 0 := funext fun s => by
      rw [← eval_pderiv_bind₁_lin]
      exact hy s
    exact tsMap_not_injective hG y M hy0 hz
      (hM y ⟨hy0, ts_ne_of_sphere hG (hUsub hMU) hy0⟩ hz)

end

end PEqualNP.Gct.Helpers
