import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Tangent
import PEqualNP.Gct.Helpers.PolarGeneric

/-!
Helper module for L-gct-048 (chart choice), proofs only.

The cone of common zeros of `G, D_{v_1} G, .., D_{v_h} G` in `h + 2` variables, with independent
gradients at each nonzero point, is a finite union of lines: near a nonzero zero `x` the map
`y ↦ (y j₀, G y, D_{v_k} G y)` is injective by the inverse function theorem, and it takes the same
value at a zero `y` and at the point `(y j₀ / x j₀) • x` of the line through `x`. Compactness of
the unit sphere gives finitely many lines, and a covector avoiding finitely many hyperplanes
exists over an infinite field.
-/

namespace PEqualNP.Gct.Helpers.ChartA

open MvPolynomial Filter Topology PEqualNP.Gct.Helpers

/-- A square polynomial system with independent gradients at `x` is injective near `x`. -/
theorem injOn_nhds_of_linearIndependent {m : ℕ} (P : Fin m → MvPolynomial (Fin m) ℂ)
    (x : Fin m → ℂ)
    (hli : LinearIndependent ℂ (fun i j => eval x (pderiv j (P i)) : Fin m → Fin m → ℂ)) :
    ∃ S : Set (Fin m → ℂ), IsOpen S ∧ x ∈ S ∧
      Set.InjOn (fun (y : Fin m → ℂ) (i : Fin m) => eval y (P i)) S := by
  classical
  set Ψ : (Fin m → ℂ) → (Fin m → ℂ) := fun y i => eval y (P i) with hΨ
  set D : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi (fun i => gradCLM (P i) x) with hD
  have hΨD : HasStrictFDerivAt Ψ D x := by
    rw [hΨ, hD, hasStrictFDerivAt_pi]
    intro i
    exact hasStrictFDerivAt_eval (P i) x
  set M : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => eval x (pderiv j (P i)) with hM
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    funext i
    refine Fintype.linearIndependent_iff.1 hli c ?_ i
    funext j
    have := congrFun hc j
    simpa [Matrix.vecMul, dotProduct, hM] using this
  have hinj : Function.Injective D.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    by_contra hu0
    apply hdet
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu0, ?_⟩
    funext i
    have h1 : D u i = 0 := congrFun hu i
    have h2 : D u i = gradCLM (P i) x u := by simp [hD]
    rw [h2, gradCLM_apply] at h1
    simpa [Matrix.mulVec, dotProduct, hM, mul_comm] using h1
  set E : (Fin m → ℂ) ≃L[ℂ] (Fin m → ℂ) :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv with hE
  have hEcoe : (E : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) = D := by
    ext v i; simp [hE]
  have hΨE : HasStrictFDerivAt Ψ (E : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) x := by
    rw [hEcoe]; exact hΨD
  refine ⟨(hΨE.toOpenPartialHomeomorph Ψ).source, (hΨE.toOpenPartialHomeomorph Ψ).open_source,
    hΨE.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hΨE.toOpenPartialHomeomorph Ψ).injOn
  rwa [hΨE.toOpenPartialHomeomorph_coe] at this

/-- Near a nonzero point `x` of the cone, every point of the cone lies on the line of `x`. -/
theorem eventually_mem_line {h r : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (hG : G.IsHomogeneous r) (v : Fin h → Fin (h + 2) → ℂ)
    (x : Fin (h + 2) → ℂ) (hx : x ≠ 0) (hGx : eval x G = 0)
    (hDx : ∀ k, eval x (polarD G v k) = 0)
    (hind : LinearIndependent ℂ
      (Fin.cons (fun j => eval x (pderiv j G))
        (fun k j => eval x (pderiv j (polarD G v k))) : Fin (h + 1) → Fin (h + 2) → ℂ)) :
    ∀ᶠ y in 𝓝 x, eval y G = 0 → (∀ k, eval y (polarD G v k) = 0) → ∃ t : ℂ, y = t • x := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  set P : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ :=
    Fin.cons (X j₀) (Fin.cons G (fun k => polarD G v k)) with hP
  set fam : Fin (h + 1) → Fin (h + 2) → ℂ :=
    Fin.cons (fun j => eval x (pderiv j G)) (fun k j => eval x (pderiv j (polarD G v k)))
    with hfam
  have hrows : (fun i j => eval x (pderiv j (P i)) : Fin (h + 2) → Fin (h + 2) → ℂ) =
      Fin.cons (fun j => eval x (pderiv j (X j₀ : MvPolynomial (Fin (h + 2)) ℂ))) fam := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hP]
    · refine Fin.cases ?_ (fun k => ?_) i
      · simp [hP, hfam]
      · simp [hP, hfam]
  -- pairing with `x` kills the homogeneous rows (Euler)
  set φ : (Fin (h + 2) → ℂ) →ₗ[ℂ] ℂ :=
    ∑ j, x j • (LinearMap.proj j : (Fin (h + 2) → ℂ) →ₗ[ℂ] ℂ) with hφ
  have hφa : ∀ w, φ w = ∑ j, x j * w j := by
    intro w; simp [hφ, LinearMap.sum_apply]
  have hfamker : ∀ i, φ (fam i) = 0 := by
    intro i
    rw [hφa]
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [hfam, Fin.cons_zero]
      rw [eval_euler hG x, hGx, mul_zero]
    · simp only [hfam, Fin.cons_succ]
      rw [eval_euler (polarD_isHomogeneous hG v k) x, hDx k, mul_zero]
  have hli : LinearIndependent ℂ
      (fun i j => eval x (pderiv j (P i)) : Fin (h + 2) → Fin (h + 2) → ℂ) := by
    rw [hrows, linearIndependent_finCons]
    refine ⟨hind, fun hmem => ?_⟩
    have hle : Submodule.span ℂ (Set.range fam) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hfamker i
    have h0 := hle hmem
    rw [LinearMap.mem_ker, hφa] at h0
    apply hj₀
    simpa [pderiv_X, Pi.single_apply] using h0
  obtain ⟨S, hSo, hxS, hSinj⟩ := injOn_nhds_of_linearIndependent P x hli
  have hcont : Continuous (fun y : Fin (h + 2) → ℂ => (y j₀ / x j₀) • x) :=
    ((continuous_apply j₀).div_const _).smul continuous_const
  have hfx : (x j₀ / x j₀) • x = x := by rw [div_self hj₀, one_smul]
  have hpre : (fun y : Fin (h + 2) → ℂ => (y j₀ / x j₀) • x) ⁻¹' S ∈ 𝓝 x :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hfx]; exact hSo.mem_nhds hxS)
  filter_upwards [hSo.mem_nhds hxS, hpre] with y hyS hfy hyG hyD
  refine ⟨y j₀ / x j₀, hSinj hyS hfy ?_⟩
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [hP, Fin.cons_zero, eval_X, Pi.smul_apply, smul_eq_mul]
    field_simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp only [hP, Fin.cons_succ, Fin.cons_zero]
      rw [hG.eval_smul, hGx, mul_zero, hyG]
    · simp only [hP, Fin.cons_succ]
      rw [(polarD_isHomogeneous hG v k).eval_smul, hDx k, mul_zero, hyD k]

/-- The cone is contained in finitely many lines. -/
theorem exists_finset_lines {h r : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (hG : G.IsHomogeneous r) (v : Fin h → Fin (h + 2) → ℂ)
    (hind : ∀ x : Fin (h + 2) → ℂ, x ≠ 0 → eval x G = 0 →
      (∀ k, eval x (polarD G v k) = 0) →
      LinearIndependent ℂ
        (Fin.cons (fun j => eval x (pderiv j G))
          (fun k j => eval x (pderiv j (polarD G v k))) : Fin (h + 1) → Fin (h + 2) → ℂ)) :
    ∃ T : Finset (Fin (h + 2) → ℂ), (∀ x ∈ T, x ≠ 0) ∧
      ∀ z : Fin (h + 2) → ℂ, z ≠ 0 → eval z G = 0 → (∀ k, eval z (polarD G v k) = 0) →
        ∃ x ∈ T, ∃ t : ℂ, z = t • x := by
  classical
  have hce : ∀ p : MvPolynomial (Fin (h + 2)) ℂ,
      Continuous (fun y : Fin (h + 2) → ℂ => eval y p) := fun p =>
    continuous_iff_continuousAt.2 fun y => (hasStrictFDerivAt_eval p y).continuousAt
  set Z : Set (Fin (h + 2) → ℂ) :=
    {y | eval y G = 0} ∩ ⋂ k, {y | eval y (polarD G v k) = 0} with hZ
  have hZc : IsClosed Z :=
    (isClosed_eq (hce G) continuous_const).inter
      (isClosed_iInter fun k => isClosed_eq (hce _) continuous_const)
  have hK : IsCompact (Z ∩ Metric.sphere (0 : Fin (h + 2) → ℂ) 1) :=
    (isCompact_sphere _ _).inter_left hZc
  set U : (Fin (h + 2) → ℂ) → Set (Fin (h + 2) → ℂ) := fun x =>
    {y | eval y G = 0 → (∀ k, eval y (polarD G v k) = 0) → ∃ t : ℂ, y = t • x} with hU
  have hsph : ∀ x ∈ Z ∩ Metric.sphere (0 : Fin (h + 2) → ℂ) 1, x ≠ 0 := by
    rintro x ⟨-, hx⟩ rfl
    simp at hx
  have hUn : ∀ x ∈ Z ∩ Metric.sphere (0 : Fin (h + 2) → ℂ) 1, U x ∈ 𝓝 x := by
    intro x hxK
    have hxZ := hxK.1
    rw [hZ] at hxZ
    have hxG : eval x G = 0 := hxZ.1
    have hxD : ∀ k, eval x (polarD G v k) = 0 := fun k => Set.mem_iInter.1 hxZ.2 k
    exact eventually_mem_line G hG v x (hsph x hxK) hxG hxD (hind x (hsph x hxK) hxG hxD)
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover U hUn
  refine ⟨T, fun x hx => hsph x (hTK x hx), ?_⟩
  intro z hz hzG hzD
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  set c : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast inv_ne_zero hnz
  have hcG : eval (c • z) G = 0 := by rw [hG.eval_smul, hzG, mul_zero]
  have hcD : ∀ k, eval (c • z) (polarD G v k) = 0 := fun k => by
    rw [(polarD_isHomogeneous hG v k).eval_smul, hzD k, mul_zero]
  have hmem : c • z ∈ Z ∩ Metric.sphere (0 : Fin (h + 2) → ℂ) 1 := by
    refine ⟨⟨hcG, Set.mem_iInter.2 hcD⟩, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hnz]
  obtain ⟨x, hxT, hxU⟩ := Set.mem_iUnion₂.1 (hcov hmem)
  obtain ⟨t, ht⟩ := hxU hcG hcD
  refine ⟨x, hxT, c⁻¹ * t, ?_⟩
  rw [mul_smul, ← ht, smul_smul, inv_mul_cancel₀ hc0, one_smul]

/-- A covector that vanishes on none of finitely many nonzero vectors. -/
theorem exists_covector {n : ℕ} (T : Finset (Fin n → ℂ)) (hT : ∀ x ∈ T, x ≠ 0) :
    ∃ a : Fin n → ℂ, ∀ x ∈ T, ∑ j, a j * x j ≠ 0 := by
  classical
  set φ : (Fin n → ℂ) → ((Fin n → ℂ) →ₗ[ℂ] ℂ) := fun x =>
    ∑ j, x j • (LinearMap.proj j : (Fin n → ℂ) →ₗ[ℂ] ℂ) with hφ
  have hφa : ∀ x a, φ x a = ∑ j, a j * x j := by
    intro x a; simp [hφ, LinearMap.sum_apply, mul_comm]
  set s : Finset (Subspace ℂ (Fin n → ℂ)) := T.image (fun x => LinearMap.ker (φ x)) with hs
  have htop : ⊤ ∉ s := by
    intro hmem
    obtain ⟨x, hxT, hx⟩ := Finset.mem_image.1 hmem
    apply hT x hxT
    funext j
    have h1 : (Pi.single j 1 : Fin n → ℂ) ∈ LinearMap.ker (φ x) := by rw [hx]; trivial
    rw [LinearMap.mem_ker, hφa] at h1
    simpa [Pi.single_apply] using h1
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem htop)
  refine ⟨a, fun x hxT h0 => ha ?_⟩
  refine Set.mem_iUnion₂.2 ⟨LinearMap.ker (φ x), Finset.mem_image.2 ⟨x, hxT, rfl⟩, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, hφa]
  exact h0

/-- Chart choice, in terms of `polarD`. -/
theorem chart_choice {h r : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (hG : G.IsHomogeneous r) (v : Fin h → Fin (h + 2) → ℂ)
    (hind : ∀ x : Fin (h + 2) → ℂ, x ≠ 0 → eval x G = 0 →
      (∀ k, eval x (polarD G v k) = 0) →
      LinearIndependent ℂ
        (Fin.cons (fun j => eval x (pderiv j G))
          (fun k j => eval x (pderiv j (polarD G v k))) : Fin (h + 1) → Fin (h + 2) → ℂ)) :
    ∃ a : Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, eval x G = 0 → ∑ j, a j * x j = 0 →
      (∀ k : Fin h, eval x (polarD G v k) = 0) → x = 0 := by
  obtain ⟨T, hT0, hT⟩ := exists_finset_lines G hG v hind
  obtain ⟨a, ha⟩ := exists_covector T hT0
  refine ⟨a, fun z hzG haz hzD => ?_⟩
  by_contra hz
  obtain ⟨x, hxT, t, rfl⟩ := hT z hz hzG hzD
  have h1 : ∑ j, a j * (t • x) j = t * ∑ j, a j * x j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h1] at haz
  rcases mul_eq_zero.1 haz with h | h
  · exact hz (by rw [h, zero_smul])
  · exact ha x hxT h

end PEqualNP.Gct.Helpers.ChartA
