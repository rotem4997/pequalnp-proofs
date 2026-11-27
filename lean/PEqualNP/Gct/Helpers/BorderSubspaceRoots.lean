import Mathlib

/-! Helpers for L-gct-069 (border subspace reduction): root persistence for univariate complex
polynomials of bounded degree. If `f k → g` coefficientwise, `g ≠ 0` and `g 0 = 0`, then the
`f k` have roots tending to `0`. The reason: a polynomial with no root in the disc of radius `ε`
is its constant term times `∏ (1 - X / r)` over its roots, whose coefficients are bounded by
`(1 + ε⁻¹) ^ deg`, so every coefficient is bounded by the constant term times that factor. -/

namespace PEqualNP.Gct.Helpers.BorderSubspace

open Polynomial Filter Topology

/-- The coefficients of `∏ (1 - c X)` over a multiset of `c` of norm at most `M` are bounded by
`(1 + M) ^ card`. -/
theorem norm_coeff_prod_le (M : ℝ) (hM : 0 ≤ M) (s : Multiset ℂ) (hs : ∀ c ∈ s, ‖c‖ ≤ M) :
    ∀ j, ‖((s.map fun c => (1 - C c * X : ℂ[X])).prod).coeff j‖ ≤ (1 + M) ^ s.card := by
  induction s using Multiset.induction_on with
  | empty =>
    intro j
    rcases j with _ | j <;> simp [coeff_one]
  | cons a s ih =>
    intro j
    have ih' := ih (fun c hc => hs c (Multiset.mem_cons_of_mem hc))
    have ha : ‖a‖ ≤ M := hs a (Multiset.mem_cons_self a s)
    set P := (s.map fun c => (1 - C c * X : ℂ[X])).prod with hP
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have hB : 0 ≤ (1 + M) ^ s.card := pow_nonneg (by linarith) _
    have heq : (1 - C a * X) * P = P - C a * (X * P) := by ring
    rw [heq, coeff_sub, coeff_C_mul]
    rcases j with _ | j
    · rw [coeff_X_mul_zero, mul_zero, sub_zero]
      nlinarith [ih' 0]
    · rw [coeff_X_mul]
      calc ‖P.coeff (j + 1) - a * P.coeff j‖ ≤ ‖P.coeff (j + 1)‖ + ‖a‖ * ‖P.coeff j‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ (1 + M) ^ s.card + M * (1 + M) ^ s.card := by
            gcongr
            · exact ih' _
            · exact ih' _
        _ = (1 + M) ^ s.card * (1 + M) := by ring

/-- A complex polynomial with no root of norm less than `ε` has every coefficient bounded by its
constant coefficient times `(1 + ε⁻¹) ^ natDegree`. -/
theorem norm_coeff_le_of_roots (p : ℂ[X]) (ε : ℝ) (hε : 0 < ε)
    (hr : ∀ r ∈ p.roots, ε ≤ ‖r‖) (j : ℕ) :
    ‖p.coeff j‖ ≤ ‖p.coeff 0‖ * (1 + ε⁻¹) ^ p.natDegree := by
  have hne : ∀ r ∈ p.roots, r ≠ 0 := fun r hr' h => by
    have := hr r hr'
    rw [h, norm_zero] at this
    linarith
  set g := (p.roots.map fun r => (1 - C r⁻¹ * X : ℂ[X])).prod with hg
  set κ := p.leadingCoeff * (p.roots.map fun r => -r).prod with hκ
  have hfac : p = C κ * g := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := p))]
    have hmap : (p.roots.map fun a => X - C a) =
        p.roots.map fun r => C (-r) * (1 - C r⁻¹ * X) := by
      refine Multiset.map_congr rfl fun r hr' => ?_
      have h0 := hne r hr'
      rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, neg_mul, mul_inv_cancel₀ h0]
      simp only [map_neg, map_one]
      ring
    rw [hmap, Multiset.prod_map_mul, hκ, hg, C_mul, mul_assoc]
    congr 2
    rw [← Multiset.prod_hom _ (C : ℂ →+* ℂ[X]), Multiset.map_map]
    simp
  have hg0 : g.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hg, eval_multiset_prod]
    simp
  have hc0 : p.coeff 0 = κ := by
    rw [hfac, coeff_C_mul, hg0, mul_one]
  have hbound := norm_coeff_prod_le ε⁻¹ (inv_nonneg.mpr hε.le) (p.roots.map fun r => r⁻¹)
    (fun c hc => by
      obtain ⟨r, hr', rfl⟩ := Multiset.mem_map.mp hc
      rw [norm_inv]
      exact inv_anti₀ hε (hr r hr')) j
  rw [Multiset.map_map] at hbound
  rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree] at hbound
  have hgj : ‖g.coeff j‖ ≤ (1 + ε⁻¹) ^ p.natDegree := by
    simpa [hg, Function.comp_def] using hbound
  conv_lhs => rw [hfac]
  rw [coeff_C_mul, norm_mul, hc0]
  exact mul_le_mul_of_nonneg_left hgj (norm_nonneg _)

/-- Root persistence for univariate polynomials of bounded degree. -/
theorem exists_roots_tendsto_zero (f : ℕ → ℂ[X]) (g : ℂ[X]) (N : ℕ)
    (hdeg : ∀ k, (f k).natDegree ≤ N)
    (hlim : ∀ i, Tendsto (fun k => (f k).coeff i) atTop (𝓝 (g.coeff i)))
    (hg0 : g.coeff 0 = 0) (hg : g ≠ 0) :
    ∃ s : ℕ → ℂ, Tendsto s atTop (𝓝 0) ∧ ∀ᶠ k in atTop, (f k).eval (s k) = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, g.coeff j ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext i
    simpa using h i
  have hsmall : ∀ ε > 0, ∀ᶠ k in atTop, ∃ r ∈ (f k).roots, ‖r‖ < ε := by
    intro ε hε
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hcon' : ∃ᶠ k in atTop, ∀ r ∈ (f k).roots, ε ≤ ‖r‖ :=
      hcon.mono fun k hk r hr => by
        by_contra hlt
        exact hk ⟨r, hr, lt_of_not_ge hlt⟩
    set B := (1 + ε⁻¹) ^ N with hB
    have hB0 : 0 ≤ B := pow_nonneg (by positivity) _
    have hjpos : 0 < ‖g.coeff j‖ := norm_pos_iff.mpr hj
    have h0 : Tendsto (fun k => ‖(f k).coeff 0‖ * B) atTop (𝓝 0) := by
      have := ((hlim 0).norm).mul_const B
      simpa [hg0] using this
    have hJ : Tendsto (fun k => ‖(f k).coeff j‖) atTop (𝓝 ‖g.coeff j‖) := (hlim j).norm
    have e1 := h0.eventually (gt_mem_nhds (half_pos hjpos))
    have e2 := hJ.eventually (lt_mem_nhds (half_lt_self hjpos))
    obtain ⟨k, hk, hk1, hk2⟩ := (hcon'.and_eventually (e1.and e2)).exists
    have hb := norm_coeff_le_of_roots (f k) ε hε hk j
    have hpow : (1 + ε⁻¹) ^ (f k).natDegree ≤ B :=
      pow_le_pow_right₀ (by have : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le; linarith) (hdeg k)
    have : ‖(f k).coeff j‖ ≤ ‖(f k).coeff 0‖ * B :=
      hb.trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg _))
    linarith
  let s : ℕ → ℂ := fun k =>
    if h : ((f k).roots.toFinset).Nonempty then
      (Finset.exists_min_image _ (fun r => ‖r‖) h).choose else 0
  have hs : ∀ k, ∀ r ∈ (f k).roots, s k ∈ (f k).roots ∧ ‖s k‖ ≤ ‖r‖ := by
    intro k r hr
    have h : ((f k).roots.toFinset).Nonempty := ⟨r, Multiset.mem_toFinset.mpr hr⟩
    have hspec := (Finset.exists_min_image _ (fun r => ‖r‖) h).choose_spec
    simp only [s, h, ↓reduceDIte]
    exact ⟨Multiset.mem_toFinset.mp hspec.1, hspec.2 r (Multiset.mem_toFinset.mpr hr)⟩
  refine ⟨s, ?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsmall ε hε] with k ⟨r, hr, hrε⟩
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hs k r hr).2 hrε
  · filter_upwards [hsmall 1 one_pos] with k ⟨r, hr, _⟩
    exact isRoot_of_mem_roots (hs k r hr).1

end PEqualNP.Gct.Helpers.BorderSubspace
