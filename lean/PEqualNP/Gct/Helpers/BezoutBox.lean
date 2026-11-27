import Mathlib
import PEqualNP.Gct.Helpers.Persist

/-!
Helpers for L-gct-038: an elementary Bezout bound with `D i + 1`.

A polynomial map with component degrees at most `D i` has at most `∏ (D i + 1)` zeros with
invertible Jacobian. Route: perturb `F i` by `c * X i ^ (D i + 1)`; the nondegenerate zeros
persist (`nondeg_zeros_persist`); on the common zeros of the perturbed system every polynomial
function agrees with a combination of box monomials (exponents `s i ≤ D i`); the polynomial
functions on a finite point set are all functions; so the point count is at most the number of
box monomials.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

noncomputable section

open Classical in
/-- Evaluation of polynomials on a finite point set, as a linear map. -/
def evOn {N : ℕ} (T : Finset (Fin N → ℂ)) : MvPolynomial (Fin N) ℂ →ₗ[ℂ] (↥T → ℂ) where
  toFun p x := eval x.1 p
  map_add' p q := by ext x; simp
  map_smul' a p := by ext x; simp [smul_eval]

theorem evOn_apply {N : ℕ} (T : Finset (Fin N → ℂ)) (p : MvPolynomial (Fin N) ℂ) (x : ↥T) :
    evOn T p x = eval x.1 p := rfl

/-- The box monomials: exponent vectors `s` with `s i ≤ D i` for all `i`. -/
def boxMon {N : ℕ} (D : Fin N → ℕ) : Finset (Fin N →₀ ℕ) :=
  (Fintype.piFinset fun i => Finset.range (D i + 1)).image Finsupp.equivFunOnFinite.symm

theorem card_boxMon_le {N : ℕ} (D : Fin N → ℕ) : (boxMon D).card ≤ ∏ i, (D i + 1) := by
  unfold boxMon
  refine Finset.card_image_le.trans ?_
  simp [Fintype.card_piFinset]

theorem mem_boxMon {N : ℕ} {D : Fin N → ℕ} {s : Fin N →₀ ℕ} (h : ∀ i, s i ≤ D i) :
    s ∈ boxMon D := by
  unfold boxMon
  refine Finset.mem_image.2 ⟨⇑s, Fintype.mem_piFinset.2 fun i =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (h i)), ?_⟩
  ext i
  simp

open Classical in
/-- The span, inside the functions on `T`, of the box monomial functions. -/
def boxSpan {N : ℕ} (T : Finset (Fin N → ℂ)) (D : Fin N → ℕ) : Submodule ℂ (↥T → ℂ) :=
  Submodule.span ℂ
    (((boxMon D).image fun s => evOn T (monomial s 1) : Finset (↥T → ℂ)) : Set (↥T → ℂ))

/-- A polynomial function lies in a submodule as soon as its monomial functions do. -/
theorem evOn_mem_of_support {N : ℕ} (T : Finset (Fin N → ℂ)) (W : Submodule ℂ (↥T → ℂ))
    (p : MvPolynomial (Fin N) ℂ) (h : ∀ t ∈ p.support, evOn T (monomial t 1) ∈ W) :
    evOn T p ∈ W := by
  have hp : ∑ t ∈ p.support, p.coeff t • monomial t (1 : ℂ) = p := by
    conv_rhs => rw [← support_sum_monomial_coeff p]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_monomial, smul_eq_mul, mul_one]
  have key : evOn T (∑ t ∈ p.support, p.coeff t • monomial t (1 : ℂ)) ∈ W := by
    rw [map_sum]
    refine Submodule.sum_mem _ fun t ht => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (h t ht)
  rw [hp] at key
  exact key

/-- Spanning: on the common zeros of `F i + c X_i^(D i + 1)`, every monomial function is a
combination of box monomial functions. Strong induction on the degree of the monomial. -/
theorem evOn_monomial_mem {N : ℕ} (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D i) (c : ℂ) (hc : c ≠ 0) (T : Finset (Fin N → ℂ))
    (hT : ∀ x ∈ T, ∀ i, eval x (F i + C c * X i ^ (D i + 1)) = 0) :
    ∀ (n : ℕ) (s : Fin N →₀ ℕ), (s.sum fun _ e => e) = n →
      evOn T (monomial s 1) ∈ boxSpan T D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs
  by_cases hbox : ∀ i, s i ≤ D i
  · exact Submodule.subset_span
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (mem_boxMon hbox)))
  · push Not at hbox
    obtain ⟨i, hi⟩ := hbox
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single i (D i + 1) := by
      refine ⟨s - Finsupp.single i (D i + 1), ?_⟩
      ext j
      by_cases hj : i = j
      · subst hj
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [hj]
    have hev : evOn T (monomial (s' + Finsupp.single i (D i + 1)) 1)
        = (-c⁻¹) • evOn T (monomial s' 1 * F i) := by
      ext x
      have hx := hT x.1 x.2 i
      simp only [map_add, map_mul, eval_C, map_pow, eval_X] at hx
      have hx1 : c * x.1 i ^ (D i + 1) = -eval x.1 (F i) := by linear_combination hx
      have hx2 : x.1 i ^ (D i + 1) = -c⁻¹ * eval x.1 (F i) := by
        calc x.1 i ^ (D i + 1) = c⁻¹ * (c * x.1 i ^ (D i + 1)) := by field_simp
          _ = -c⁻¹ * eval x.1 (F i) := by rw [hx1]; ring
      simp only [Pi.smul_apply, evOn_apply, smul_eq_mul, monomial_add_single, map_mul, map_pow,
        eval_X]
      rw [hx2]
      ring
    rw [hev]
    refine Submodule.smul_mem _ _ (evOn_mem_of_support T _ _ fun t ht => ?_)
    have hdeg : (t.sum fun _ e => e) < n := by
      have h1 := le_totalDegree ht
      have h2 := totalDegree_mul (monomial s' (1 : ℂ)) (F i)
      have h3 : (monomial s' (1 : ℂ)).totalDegree = s'.sum fun _ e => e :=
        totalDegree_monomial s' one_ne_zero
      have h4 := hF i
      have hsum : ((s' + Finsupp.single i (D i + 1)).sum fun _ e => e)
          = (s'.sum fun _ e => e) + (D i + 1) := by
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
          Finsupp.sum_single_index rfl]
      omega
    exact ih _ hdeg t rfl

/-- Separation: a polynomial that is `1` at `y` and `0` at the other points of `T`. -/
theorem exists_sep {N : ℕ} (T : Finset (Fin N → ℂ)) (y : Fin N → ℂ) :
    ∃ p : MvPolynomial (Fin N) ℂ, eval y p = 1 ∧ ∀ x ∈ T, x ≠ y → eval x p = 0 := by
  classical
  have h : ∀ z : Fin N → ℂ, ∃ q : MvPolynomial (Fin N) ℂ,
      z ≠ y → eval y q = 1 ∧ eval z q = 0 := by
    intro z
    by_cases hz : z = y
    · exact ⟨0, fun h => absurd hz h⟩
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
      refine ⟨C ((y j - z j)⁻¹) * (X j - C (z j)), fun _ => ⟨?_, ?_⟩⟩
      · simp only [map_mul, map_sub, eval_C, eval_X]
        exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hj))
      · simp
  choose q hq using h
  refine ⟨∏ z ∈ T.erase y, q z, ?_, fun x hx hxy => ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z hz => (hq z (Finset.ne_of_mem_erase hz)).1
  · rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hxy, hx⟩) (hq x hxy).2

/-- Count: a finite set of common zeros of the perturbed system `F i + c X_i^(D i + 1)` has at
most `∏ (D i + 1)` points. -/
theorem card_le_of_perturbed {N : ℕ} (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D i) (c : ℂ) (hc : c ≠ 0) (T : Finset (Fin N → ℂ))
    (hT : ∀ x ∈ T, ∀ i, eval x (F i + C c * X i ^ (D i + 1)) = 0) :
    T.card ≤ ∏ i, (D i + 1) := by
  classical
  have htop : boxSpan T D = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    have hf : ∑ y : ↥T, f y • evOn T ((exists_sep T y.1).choose) = f := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, evOn_apply]
      rw [Finset.sum_eq_single x]
      · rw [(exists_sep T x.1).choose_spec.1, mul_one]
      · intro y _ hyx
        rw [(exists_sep T y.1).choose_spec.2 x.1 x.2 (fun h => hyx (Subtype.ext h.symm)),
          mul_zero]
      · intro h
        exact absurd (Finset.mem_univ x) h
    rw [← hf]
    refine Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ ?_
    exact evOn_mem_of_support T _ _ fun t _ => evOn_monomial_mem F D hF c hc T hT _ t rfl
  have h1 : Module.finrank ℂ (boxSpan T D) = T.card := by
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have h2 : Module.finrank ℂ (boxSpan T D) ≤ (boxMon D).card :=
    (finrank_span_finset_le_card _).trans Finset.card_image_le
  calc T.card = Module.finrank ℂ (boxSpan T D) := h1.symm
    _ ≤ (boxMon D).card := h2
    _ ≤ ∏ i, (D i + 1) := card_boxMon_le D

/-- Elementary Bezout with `D i + 1`: at most `∏ (D i + 1)` nondegenerate zeros. -/
theorem bezout_box (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D i) (S : Finset (Fin N → ℂ))
    (hS : ∀ x ∈ S, (∀ i, eval x (F i) = 0) ∧
      (Matrix.of fun i j => eval x (pderiv j (F i))).det ≠ 0) :
    S.card ≤ ∏ i, (D i + 1) := by
  let Fk : ℕ → Fin N → MvPolynomial (Fin N) ℂ :=
    fun k i => F i + C (1 / ((k : ℂ) + 1)) * X i ^ (D i + 1)
  have hdeg : ∀ k i, (Fk k i).totalDegree ≤ (∑ i, D i) + 1 := by
    intro k i
    have hle : D i ≤ ∑ i, D i :=
      Finset.single_le_sum (f := D) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (hF i).trans (hle.trans (Nat.le_succ _))
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add, totalDegree_X_pow]
      exact Nat.succ_le_succ hle
  have hconv : ∀ i s, Filter.Tendsto (fun k => (Fk k i).coeff s) Filter.atTop
      (nhds ((F i).coeff s)) := by
    intro i s
    have h0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℂ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (tendsto_const_nhds (x := (F i).coeff s)).add
      (h0.mul_const ((X i ^ (D i + 1) : MvPolynomial (Fin N) ℂ).coeff s))
    simp only [zero_mul, add_zero] at h1
    refine h1.congr fun k => ?_
    exact congrArg (fun z => (F i).coeff s + z) (coeff_C_mul s _ _).symm
  obtain ⟨K, hK⟩ := nondeg_zeros_persist N _ F Fk hdeg hconv S hS
  obtain ⟨T, hTc, hT⟩ := hK K le_rfl
  rw [← hTc]
  exact card_le_of_perturbed F D hF (1 / ((K : ℂ) + 1))
    (one_div_ne_zero (Nat.cast_add_one_ne_zero K)) T fun x hx i => (hT x hx).1 i

end

end PEqualNP.Gct.Helpers
