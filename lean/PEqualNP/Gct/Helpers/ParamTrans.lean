import Mathlib

/-!
# Parametric transversality

If the zero set of a `C^1` map `f : E × P → E` is cut out transversally in the total space,
then for almost every parameter `c` every zero of `f (., c)` is nondegenerate.

The proof is local: near a zero `z0` the map `z ↦ (f z, L z)` is a local diffeomorphism for a
suitable linear `L : E × P → P`, its inverse parametrises the zeros by `t ↦ Ψ (0, t)`, and the
bad parameters are the image of critical points of `t ↦ (Ψ (0, t)).2 : P → P`, which is null by
the equidimensional Sard lemma. A countable subcover finishes.
-/

open MeasureTheory Function Set

namespace PEqualNP.Gct.Helpers

/-- A surjective linear map `A : E × P → E` can be completed by a linear `L : E × P → P` to a
linear isomorphism `(A, L)` of `E × P`. -/
theorem pt_exists_completion (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (A : E × P →L[ℝ] E) (hA : Surjective A) :
    ∃ (L : E × P →L[ℝ] P) (Φ : (E × P) ≃L[ℝ] (E × P)),
      (Φ : E × P →L[ℝ] E × P) = A.prod L := by
  set K := LinearMap.ker (A : E × P →ₗ[ℝ] E) with hK
  have hrank : Module.finrank ℝ K = Module.finrank ℝ P := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : E × P →ₗ[ℝ] E)
    have h2 : LinearMap.range (A : E × P →ₗ[ℝ] E) = ⊤ := LinearMap.range_eq_top.2 hA
    rw [h2, finrank_top, Module.finrank_prod] at h1
    linarith
  let φ : K ≃ₗ[ℝ] P := LinearEquiv.ofFinrankEq K P hrank
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective K.subtype (Submodule.ker_subtype K)
  let L : E × P →L[ℝ] P := LinearMap.toContinuousLinearMap (φ.toLinearMap ∘ₗ p)
  have hinj : Injective ((A.prod L : E × P →L[ℝ] E × P) : E × P →ₗ[ℝ] E × P) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz1 : A z = 0 := congrArg Prod.fst hz
    have hz2 : φ (p z) = 0 := congrArg Prod.snd hz
    have hzK : z ∈ K := hz1
    have hpz : p (K.subtype ⟨z, hzK⟩) = ⟨z, hzK⟩ := by
      have := LinearMap.congr_fun hp ⟨z, hzK⟩
      simpa using this
    have hpz0 : p z = 0 := φ.map_eq_zero_iff.1 hz2
    have : (⟨z, hzK⟩ : K) = 0 := by rw [← hpz]; simpa using hpz0
    exact congrArg Subtype.val this
  refine ⟨L, (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv, ?_⟩
  ext z <;> rfl

/-- A continuous linear endomorphism with a nonzero kernel vector has determinant zero. -/
theorem pt_det_eq_zero (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (T : P →L[ℝ] P) (s : P) (hs : s ≠ 0) (hT : T s = 0) :
    T.det = 0 := by
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro h
  exact hs ((LinearMap.ker_eq_bot'.1 h) s hT)

/-- The local step: near a transversal zero, the bad parameters are null. -/
theorem pt_local (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P] (μ : MeasureTheory.Measure P) [μ.IsAddHaarMeasure]
    (f : E × P → E) (hf : ContDiff ℝ 1 f) (z0 : E × P)
    (hz0 : Surjective (fderiv ℝ f z0)) :
    ∃ W : Set (E × P), IsOpen W ∧ z0 ∈ W ∧
      μ {c | ∃ y, (y, c) ∈ W ∧ f (y, c) = 0 ∧
        ¬ Injective ((fderiv ℝ f (y, c)).comp (ContinuousLinearMap.inl ℝ E P))} = 0 := by
  obtain ⟨L, Φ, hΦ⟩ := pt_exists_completion E P (fderiv ℝ f z0) hz0
  set Θ : E × P → E × P := fun z => (f z, L z) with hΘdef
  have hΘ : ContDiff ℝ 1 Θ := hf.prodMk L.contDiff
  have hΘd : ∀ z, HasFDerivAt Θ ((fderiv ℝ f z).prod L) z := fun z =>
    ((hf.differentiable one_ne_zero z).hasFDerivAt.prodMk L.hasFDerivAt)
  have hs0 : HasStrictFDerivAt Θ (Φ : E × P →L[ℝ] E × P) z0 := by
    have := hΘ.contDiffAt.hasStrictFDerivAt (hΘd z0) one_ne_zero
    rwa [← hΦ] at this
  set e := hs0.toOpenPartialHomeomorph Θ with he
  have hecoe : (e : E × P → E × P) = Θ := hs0.toOpenPartialHomeomorph_coe
  set U : Set (E × P) := {z | ∃ A : (E × P) ≃L[ℝ] (E × P),
    (A : E × P →L[ℝ] E × P) = fderiv ℝ Θ z} with hUdef
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage (hΘ.continuous_fderiv one_ne_zero)
  refine ⟨e.source ∩ U, e.open_source.inter hU,
    ⟨hs0.mem_toOpenPartialHomeomorph_source, Φ, by rw [(hΘd z0).fderiv, hΦ]⟩, ?_⟩
  set σ : P → P := fun t => (e.symm (0, t)).2 with hσdef
  set S : Set P := {t | ∃ z ∈ e.source ∩ U, f z = 0 ∧ L z = t ∧
    ¬ Injective ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E P))} with hSdef
  have key : ∀ t ∈ S, HasFDerivAt σ (fderiv ℝ σ t) t ∧ (fderiv ℝ σ t).det = 0 := by
    rintro t ⟨z, ⟨hzs, A, hA⟩, hfz, hLz, hni⟩
    have hΘz : e z = (0, t) := by rw [hecoe]; simp [Θ, hfz, hLz]
    have hsymm : e.symm (0, t) = z := by rw [← hΘz]; exact e.left_inv hzs
    have htgt : (0, t) ∈ e.target := by rw [← hΘz]; exact e.map_source hzs
    have hA' : (A : E × P →L[ℝ] E × P) = (fderiv ℝ f z).prod L := by
      rw [hA]; exact (hΘd z).fderiv
    have hd : HasFDerivAt e (A : E × P →L[ℝ] E × P) (e.symm (0, t)) := by
      rw [hsymm, hecoe, hA']; exact hΘd z
    have hinv := e.hasFDerivAt_symm htgt hd
    have hσ : HasFDerivAt σ ((ContinuousLinearMap.snd ℝ E P).comp
        ((A.symm : E × P →L[ℝ] E × P).comp (ContinuousLinearMap.inr ℝ E P))) t :=
      (ContinuousLinearMap.snd ℝ E P).hasFDerivAt.comp t
        (hinv.comp t (hasFDerivAt_prodMk_right 0 t))
    refine ⟨hσ.differentiableAt.hasFDerivAt, ?_⟩
    rw [hσ.fderiv]
    obtain ⟨v, hv, hv0⟩ : ∃ v : E, fderiv ℝ f z (v, 0) = 0 ∧ v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hni
      rw [injective_iff_map_eq_zero]
      intro v hv
      exact hcon v (by simpa using hv)
    have hAv : A (v, 0) = (0, L (v, 0)) := by
      have : A (v, 0) = ((fderiv ℝ f z).prod L) (v, 0) := by rw [← hA']; rfl
      rw [this]; simp [hv]
    apply pt_det_eq_zero P _ (L (v, 0))
    · intro h0
      rw [h0] at hAv
      have : (v, (0 : P)) = 0 := A.map_eq_zero_iff.1 (by rw [hAv]; rfl)
      exact hv0 (congrArg Prod.fst this)
    · have : A.symm (0, L (v, 0)) = (v, 0) := by rw [← hAv]; exact A.symm_apply_apply _
      simp [this]
  have hnull := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun t ht => (key t ht).1.hasFDerivWithinAt) (fun t ht => (key t ht).2)
  refine measure_mono_null ?_ hnull
  rintro c ⟨y, hW, hfz, hni⟩
  refine ⟨L (y, c), ⟨(y, c), hW, hfz, rfl, hni⟩, ?_⟩
  have h1 : e (y, c) = (0, L (y, c)) := by rw [hecoe]; simp [Θ, hfz]
  show (e.symm (0, L (y, c))).2 = c
  rw [← h1, e.left_inv hW.1]

/-- Parametric transversality: if the zero set of `f` is cut out transversally in the total
space, then for almost every parameter `c` every zero of `f (., c)` is nondegenerate. -/
theorem param_transversality
    (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P] (μ : MeasureTheory.Measure P) [μ.IsAddHaarMeasure]
    (f : E × P → E) (hf : ContDiff ℝ 1 f)
    (hsurj : ∀ z : E × P, f z = 0 → Function.Surjective (fderiv ℝ f z)) :
    ∀ᵐ c ∂μ, ∀ y : E, f (y, c) = 0 →
      Function.Injective (fderiv ℝ (fun y' : E => f (y', c)) y) := by
  have hslice : ∀ y c, fderiv ℝ (fun y' : E => f (y', c)) y =
      (fderiv ℝ f (y, c)).comp (ContinuousLinearMap.inl ℝ E P) := fun y c =>
    ((hf.differentiable one_ne_zero (y, c)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y c)).fderiv
  choose W hWo hWm hWn using fun z : {z : E × P // f z = 0} =>
    pt_local E P μ f hf z.1 (hsurj z.1 z.2)
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  rw [ae_iff]
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hT).2 fun i _ => hWn i)
  intro c hc
  simp only [mem_ofPred_eq, not_forall] at hc
  obtain ⟨y, hy, hni⟩ := hc
  have hmem : (y, c) ∈ ⋃ i ∈ T, W i := by
    rw [hTU]; exact mem_iUnion.2 ⟨⟨(y, c), hy⟩, hWm _⟩
  obtain ⟨i, hi, hiW⟩ := mem_iUnion₂.1 hmem
  refine mem_iUnion₂.2 ⟨i, hi, y, hiW, hy, ?_⟩
  rwa [← hslice]

end PEqualNP.Gct.Helpers
