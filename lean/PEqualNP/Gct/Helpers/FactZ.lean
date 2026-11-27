import Mathlib
import PEqualNP.Gct.Helpers.BezFinite
import PEqualNP.Gct.Helpers.BezoutBox

/-!
Helpers for L-gct-059 (Fact Z) and `PEqualNP.Gct.Rung.BoundedZeros`: the zeros of a system of
`k` polynomials in `l` variables whose top forms `g` (all of degree `e`) have only the trivial
common zero are bounded uniformly in the lower order terms.

* `fz_exists_pow_mem`, `fz_monomial_mem`, `fz_homog_decomp`: the Nullstellensatz step of
  `BezFinite`, for `k` forms in `l` variables.
* `factz_reduce`: there is `D0`, depending on `g` alone, such that for every `f` with
  `totalDegree (f i - g i) < e`, every polynomial is congruent mod `(f)` to one of degree `< D0`.
* `factz_card_le`: a finite set of common zeros of such an `f` has at most `D0 ^ l` points
  (evaluation on the set is onto, kills `(f)`, so factors through the box monomials).
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- Nullstellensatz step for `k` forms in `l` variables. -/
theorem fz_exists_pow_mem {k l : ℕ} (g : Fin k → MvPolynomial (Fin l) ℂ)
    (hg : ∀ x : Fin l → ℂ, (∀ i, eval x (g i) = 0) → x = 0) (j : Fin l) :
    ∃ N : ℕ, X j ^ N ∈ Ideal.span (Set.range g) := by
  have hmem : (X j : MvPolynomial (Fin l) ℂ) ∈
      vanishingIdeal ℂ (zeroLocus ℂ (Ideal.span (Set.range g)) : Set (Fin l → ℂ)) := by
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have h0 : x = 0 := hg x fun i => by
      have := hx (g i) (Ideal.subset_span ⟨i, rfl⟩)
      simpa [aeval_eq_eval] using this
    simp [h0]
  rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
  exact hmem

/-- Every monomial of large degree lies in `(g)`. -/
theorem fz_monomial_mem {k l : ℕ} (g : Fin k → MvPolynomial (Fin l) ℂ)
    (hg : ∀ x : Fin l → ℂ, (∀ i, eval x (g i) = 0) → x = 0) (E : ℕ) :
    ∃ D0 : ℕ, E < D0 ∧ ∀ (s : Fin l →₀ ℕ) (c : ℂ), D0 ≤ s.degree →
      monomial s c ∈ Ideal.span (Set.range g) := by
  choose N hN using fz_exists_pow_mem g hg
  refine ⟨∑ j, N j + E + 1, by omega, fun s c hs => ?_⟩
  have : ∃ j, N j ≤ s j := by
    by_contra hcon
    push Not at hcon
    have h1 : s.degree ≤ ∑ j, N j := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.sum_le_sum fun j _ => (hcon j).le
    omega
  obtain ⟨j, hj⟩ := this
  have hle : Finsupp.single j (N j) ≤ s := by
    rw [Finsupp.single_le_iff]; exact hj
  have hs' : s = (s - Finsupp.single j (N j)) + Finsupp.single j (N j) :=
    (tsub_add_cancel_of_le hle).symm
  rw [hs', ← mul_one c, ← monomial_mul_monomial, ← X_pow_eq_monomial]
  exact Ideal.mul_mem_left _ _ (hN j)

/-- Forms of large degree decompose along the `g i` (all of degree `e`). -/
theorem fz_homog_decomp {k l e : ℕ} (g : Fin k → MvPolynomial (Fin l) ℂ)
    (hgh : ∀ i, (g i).IsHomogeneous e) (D0 : ℕ) (heD0 : e ≤ D0)
    (hD0 : ∀ (s : Fin l →₀ ℕ) (c : ℂ), D0 ≤ s.degree → monomial s c ∈ Ideal.span (Set.range g))
    {D : ℕ} (hD : D0 ≤ D) (p : MvPolynomial (Fin l) ℂ) (hp : p.IsHomogeneous D) :
    ∃ a : Fin k → MvPolynomial (Fin l) ℂ, (∀ i, (a i).IsHomogeneous (D - e)) ∧
      p = ∑ i, g i * a i := by
  have hpI : p ∈ Ideal.span (Set.range g) := by
    rw [p.as_sum]
    refine Ideal.sum_mem _ fun s hs => hD0 s _ ?_
    have h := hp (mem_support_iff.mp hs)
    rw [Finsupp.degree_eq_weight_one]
    exact h.symm ▸ hD
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hpI
  refine ⟨fun i => homogeneousComponent (D - e) (c i),
    fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hpD : homogeneousComponent D p = p := homogeneousComponent_of_mem hp |>.trans (by simp)
  rw [← hpD, ← hc, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (g i)]
  exact weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right (hgh i) (heD0.trans hD)

/-- The uniform reduction: `D0` comes from `g` alone. -/
theorem factz_reduce {k n e : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (hgh : ∀ i, (g i).IsHomogeneous e)
    (hg : ∀ x : Fin n → ℂ, (∀ i, eval x (g i) = 0) → x = 0) :
    ∃ D0 : ℕ, e < D0 ∧ ∀ f : Fin k → MvPolynomial (Fin n) ℂ,
      (∀ i, (f i - g i).totalDegree < e) → ∀ p : MvPolynomial (Fin n) ℂ,
      ∃ q : MvPolynomial (Fin n) ℂ, q.totalDegree < D0 ∧ p - q ∈ Ideal.span (Set.range f) := by
  obtain ⟨D0, hED0, hD0⟩ := fz_monomial_mem g hg e
  refine ⟨D0, hED0, fun f hf p => ?_⟩
  induction hdeg : p.totalDegree using Nat.strong_induction_on generalizing p with
  | _ D ih =>
  by_cases hlt : D < D0
  · exact ⟨p, hdeg ▸ hlt, by simp⟩
  push Not at hlt
  have hD : 0 < D := by omega
  obtain ⟨a, ha, hpa⟩ := fz_homog_decomp g hgh D0 hED0.le hD0 hlt
    (homogeneousComponent D p) (homogeneousComponent_isHomogeneous _ _)
  set p' := p - ∑ i, f i * a i with hp'
  have hp'eq : p' = (p - homogeneousComponent D p) - ∑ i, (f i - g i) * a i := by
    rw [hp', hpa]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hlt' : p'.totalDegree < D := by
    rw [hp'eq]
    refine lt_of_le_of_lt (totalDegree_sub _ _) (max_lt ?_ ?_)
    · exact bez_totalDegree_sub_homogeneousComponent_lt p hdeg.le hD
    · have hsum : (∑ i, (f i - g i) * a i).totalDegree ≤ D - 1 := by
        refine totalDegree_finsetSum_le fun i _ => ?_
        have hai : (a i).totalDegree ≤ D - e := (ha i).totalDegree_le
        refine (totalDegree_mul _ _).trans ?_
        have := hf i
        omega
      omega
  obtain ⟨q, hq, hpq⟩ := ih _ (hdeg ▸ hlt') p' rfl
  refine ⟨q, hq, ?_⟩
  have : p - q = (p' - q) + ∑ i, a i * f i := by
    rw [hp']
    simp only [mul_comm (a _)]
    ring
  rw [this]
  refine Ideal.add_mem _ hpq (Ideal.sum_mem _ fun i _ => ?_)
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Counting: if every polynomial is congruent mod `(f)` to one of degree `< D0`, a finite set of
common zeros of `f` has at most `D0 ^ n` points. -/
theorem factz_card_le {k n : ℕ} (f : Fin k → MvPolynomial (Fin n) ℂ) (D0 : ℕ) (hD0pos : 0 < D0)
    (hred : ∀ p : MvPolynomial (Fin n) ℂ, ∃ q : MvPolynomial (Fin n) ℂ,
      q.totalDegree < D0 ∧ p - q ∈ Ideal.span (Set.range f))
    (T : Finset (Fin n → ℂ)) (hT : ∀ x ∈ T, ∀ i, eval x (f i) = 0) :
    T.card ≤ D0 ^ n := by
  classical
  have hev : ∀ p : MvPolynomial (Fin n) ℂ, evOn T p ∈ boxSpan T (fun _ => D0 - 1) := by
    intro p
    obtain ⟨q, hq, hpq⟩ := hred p
    have heq : evOn T p = evOn T q := by
      ext x
      rw [evOn_apply, evOn_apply]
      have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval x.1) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact RingHom.mem_ker.2 (hT x.1 x.2 i)
      have h0 := RingHom.mem_ker.1 (hle hpq)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [heq]
    refine evOn_mem_of_support T _ q fun t ht => ?_
    refine Submodule.subset_span ?_
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, mem_boxMon fun i => ?_, rfl⟩)
    have h1 : t.degree ≤ q.totalDegree := le_totalDegree ht
    have h2 : t i ≤ t.degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (f := fun j => t j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  have htop : boxSpan T (fun _ => D0 - 1) = ⊤ := by
    refine eq_top_iff.2 fun φ _ => ?_
    have hφ : ∑ y : ↥T, φ y • evOn T ((exists_sep T y.1).choose) = φ := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, evOn_apply]
      rw [Finset.sum_eq_single x]
      · rw [(exists_sep T x.1).choose_spec.1, mul_one]
      · intro y _ hyx
        rw [(exists_sep T y.1).choose_spec.2 x.1 x.2 (fun h => hyx (Subtype.ext h.symm)),
          mul_zero]
      · intro h
        exact absurd (Finset.mem_univ x) h
    rw [← hφ]
    exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (hev _)
  have h1 : Module.finrank ℂ (boxSpan T (fun _ => D0 - 1)) = T.card := by
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℂ (boxSpan T (fun _ => D0 - 1)) ≤ (boxMon fun _ : Fin n => D0 - 1).card :=
    (finrank_span_finset_le_card _).trans Finset.card_image_le
  have h3 := card_boxMon_le (fun _ : Fin n => D0 - 1)
  have h4 : ∏ _i : Fin n, (D0 - 1 + 1) ≤ D0 ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_left (by omega) n
  exact h1.symm.le.trans (h2.trans (h3.trans h4))

/-- Fact Z, for `k` forms in `l` variables. -/
theorem factz (l k e : ℕ) (g : Fin k → MvPolynomial (Fin l) ℂ)
    (hgh : ∀ i, (g i).IsHomogeneous e)
    (hg : ∀ x : Fin l → ℂ, (∀ i, eval x (g i) = 0) → x = 0) :
    ∃ M : ℕ, ∀ (f : Fin k → MvPolynomial (Fin l) ℂ), (∀ i, (f i - g i).totalDegree < e) →
      ∀ S : Finset (Fin l → ℂ), (∀ x ∈ S, ∀ i, eval x (f i) = 0) → S.card ≤ M := by
  obtain ⟨D0, hlt, hD0⟩ := factz_reduce g hgh hg
  exact ⟨D0 ^ l, fun f hf S hS => factz_card_le f D0 (by omega) (hD0 f hf) S hS⟩

end PEqualNP.Gct.Helpers
