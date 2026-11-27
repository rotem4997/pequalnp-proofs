import Mathlib
import PEqualNP.Gct.Helpers.BezCount

/-!
Helpers for L-gct-042 (count lemma B), the point count.

* `bez_points_ge`: if `C[x]/(f)` is finite dimensional and every common zero of `f` has
  invertible Jacobian, then there are at least `dim_C C[x]/(f)` common zeros.
  Route: Taylor at a zero `p` gives `m_p ≤ (f) ⊔ m_p^2`, hence `m_p ≤ (f) ⊔ m_p^N`; the
  ideals `(f) ⊔ m_p^N` are pairwise coprime, so their meet is their product, which lies in
  `(f) ⊔ (prod_p m_p)^N`; the Nullstellensatz puts `(prod_p m_p)^N` in `(f)` for large `N`.
  So the vanishing ideal of the zeros lies in `(f)`, and evaluation at the zeros is injective on
  `C[x]/(f)`.
* `bezCountB_holds`: `BezCountB` (the statement of L-gct-042), from `bez_finrank_ge` and
  `bez_points_ge`.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

variable {n : ℕ}

/-- The maximal ideal of a point. -/
noncomputable def bezMax (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval p)

theorem mem_bezMax {p : Fin n → ℂ} {h : MvPolynomial (Fin n) ℂ} : h ∈ bezMax p ↔ eval p h = 0 :=
  RingHom.mem_ker

theorem bez_X_sub_mem (p : Fin n → ℂ) (j : Fin n) : X j - C (p j) ∈ bezMax p := by
  rw [mem_bezMax]
  simp

theorem bez_sub_eval_mem (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    h - C (eval p h) ∈ bezMax p := by
  rw [mem_bezMax]
  simp

/-- First order Taylor expansion at `p`, with remainder in `m_p^2`. -/
theorem bez_taylor (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    h - C (eval p h) - ∑ j, C (eval p (pderiv j h)) * (X j - C (p j)) ∈ bezMax p ^ 2 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb =>
    have e : a + b - C (eval p (a + b)) - ∑ j, C (eval p (pderiv j (a + b))) * (X j - C (p j)) =
        (a - C (eval p a) - ∑ j, C (eval p (pderiv j a)) * (X j - C (p j))) +
        (b - C (eval p b) - ∑ j, C (eval p (pderiv j b)) * (X j - C (p j))) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [e]
    exact Ideal.add_mem _ ha hb
  | mul_X a k ha =>
    have hs : ∑ j, C (eval p (pderiv j (a * X k))) * (X j - C (p j)) =
        C (p k) * ∑ j, C (eval p (pderiv j a)) * (X j - C (p j)) +
          C (eval p a) * (X k - C (p k)) := by
      have h1 : ∀ j, C (eval p (pderiv j (a * X k))) * (X j - C (p j)) =
          C (p k) * (C (eval p (pderiv j a)) * (X j - C (p j))) +
            (if k = j then C (eval p a) * (X j - C (p j)) else 0) := by
        intro j
        rw [Derivation.leibniz, pderiv_X]
        by_cases hkj : k = j
        · subst hkj
          simp only [Pi.single_eq_same, smul_eq_mul, mul_one, map_add, map_mul, eval_X,
            ite_true]
          ring
        · simp only [Pi.single_apply, ite_false, smul_eq_mul, mul_zero,
            zero_add, map_mul, eval_X, hkj]
          ring
      simp_rw [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        Finset.mul_sum]
    have e : a * X k - C (eval p (a * X k)) -
        ∑ j, C (eval p (pderiv j (a * X k))) * (X j - C (p j)) =
        C (p k) * (a - C (eval p a) - ∑ j, C (eval p (pderiv j a)) * (X j - C (p j))) +
          (a - C (eval p a)) * (X k - C (p k)) := by
      rw [hs]
      simp only [map_mul, eval_X]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (bez_sub_eval_mem p a) (bez_X_sub_mem p k)

/-- At a simple zero `p`, `m_p ≤ (f) ⊔ m_p^2`. -/
theorem bez_max_le_sup_sq (f : Fin n → MvPolynomial (Fin n) ℂ) (p : Fin n → ℂ)
    (hp : ∀ i, eval p (f i) = 0)
    (hdet : (Matrix.of fun i j : Fin n => eval p (pderiv j (f i))).det ≠ 0) :
    bezMax p ≤ Ideal.span (Set.range f) ⊔ bezMax p ^ 2 := by
  classical
  set I := Ideal.span (Set.range f)
  set J : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j : Fin n => eval p (pderiv j (f i)) with hJ
  have hinv : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hdet)
  set L : Fin n → MvPolynomial (Fin n) ℂ := fun k => X k - C (p k) with hL
  have hR : ∀ i, f i - ∑ k, C (J i k) * L k ∈ bezMax p ^ 2 := by
    intro i
    have := bez_taylor p (f i)
    rw [hp i, map_zero, sub_zero] at this
    simpa [hJ, hL] using this
  have hLj : ∀ j, L j ∈ I ⊔ bezMax p ^ 2 := by
    intro j
    have hsum : ∑ i, C (J⁻¹ j i) * (∑ k, C (J i k) * L k) = L j := by
      simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply]
      simp
    have e : L j = ∑ i, C (J⁻¹ j i) * f i - ∑ i, C (J⁻¹ j i) * (f i - ∑ k, C (J i k) * L k) := by
      rw [← hsum]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hR i)
  intro h hh
  have ht := bez_taylor p h
  rw [mem_bezMax.mp hh, map_zero, sub_zero] at ht
  have e : h = (h - ∑ j, C (eval p (pderiv j h)) * L j) + ∑ j, C (eval p (pderiv j h)) * L j := by
    ring
  rw [e]
  refine Ideal.add_mem _ (Ideal.mem_sup_right ht) ?_
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hLj j)

theorem bez_max_le_sup_pow (I M : Ideal (MvPolynomial (Fin n) ℂ)) (h2 : M ≤ I ⊔ M ^ 2) (k : ℕ) :
    M ≤ I ⊔ M ^ (k + 1) := by
  induction k with
  | zero => rw [zero_add, pow_one]; exact le_sup_right
  | succ k ih =>
    calc M ≤ I ⊔ M ^ 2 := h2
      _ = I ⊔ M * M := by rw [pow_two]
      _ ≤ I ⊔ M * (I ⊔ M ^ (k + 1)) := sup_le_sup_left (Ideal.mul_mono_right ih) _
      _ = I ⊔ (M * I ⊔ M * M ^ (k + 1)) := by rw [Ideal.mul_sup]
      _ ≤ I ⊔ M ^ (k + 1 + 1) := by
        refine sup_le le_sup_left (sup_le (le_sup_of_le_left Ideal.mul_le_right) ?_)
        rw [← pow_succ']
        exact le_sup_right

theorem bez_sup_mul_le (I A B : Ideal (MvPolynomial (Fin n) ℂ)) :
    (I ⊔ A) * (I ⊔ B) ≤ I ⊔ A * B := by
  rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
  refine sup_le (sup_le (le_sup_of_le_left Ideal.mul_le_right)
    (le_sup_of_le_left Ideal.mul_le_left)) (sup_le (le_sup_of_le_left Ideal.mul_le_right)
    le_sup_right)

theorem bez_prod_sup_le {ι : Type*} (S : Finset ι) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (J : ι → Ideal (MvPolynomial (Fin n) ℂ)) : ∏ i ∈ S, (I ⊔ J i) ≤ I ⊔ ∏ i ∈ S, J i := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    exact (Ideal.mul_mono_right ih).trans (bez_sup_mul_le I (J a) _)

theorem bez_max_sup_eq_top {p q : Fin n → ℂ} (hpq : p ≠ q) : bezMax p ⊔ bezMax q = ⊤ := by
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
    by_contra hcon
    push Not at hcon
    exact hpq (funext hcon)
  have hmem : C (q j - p j) ∈ bezMax p ⊔ bezMax q := by
    have e : C (q j - p j) = (X j - C (p j)) - (X j - C (q j)) := by
      rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left (bez_X_sub_mem p j))
      (Ideal.mem_sup_right (bez_X_sub_mem q j))
  exact Ideal.eq_top_of_isUnit_mem _ hmem
    ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hj))).map C)

/-- **Point count.** A finite dimensional `C[x]/(f)` whose zeros are all simple has at least
`dim` zeros. -/
theorem bez_points_ge (f : Fin n → MvPolynomial (Fin n) ℂ)
    (hjac : ∀ x : Fin n → ℂ, (∀ i, eval x (f i) = 0) →
      (Matrix.of fun i j : Fin n => eval x (pderiv j (f i))).det ≠ 0) :
    ∃ S : Finset (Fin n → ℂ),
      Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range f)) ≤ S.card ∧
        ∀ x ∈ S, ∀ i, eval x (f i) = 0 := by
  classical
  set I := Ideal.span (Set.range f) with hI
  set Z : Set (Fin n → ℂ) := {x | ∀ i, eval x (f i) = 0} with hZ
  by_cases hZf : Z.Finite
  swap
  · obtain ⟨S, hSZ, hS⟩ := Set.Infinite.exists_subset_card_eq hZf
      (Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ I))
    exact ⟨S, hS.ge, fun x hx => hSZ hx⟩
  set S := hZf.toFinset with hS
  have hSZ : ∀ x, x ∈ S ↔ ∀ i, eval x (f i) = 0 := fun x => by
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  refine ⟨S, ?_, fun x hx => (hSZ x).mp hx⟩
  set K : Ideal (MvPolynomial (Fin n) ℂ) := S.inf bezMax with hK
  have hmemK : ∀ h, h ∈ K ↔ ∀ p ∈ S, eval p h = 0 := fun h => by
    rw [hK, Submodule.mem_finsetInf]
    exact forall₂_congr fun p _ => mem_bezMax
  -- `K ≤ rad (f)`, so a power of `K` lies in `(f)`.
  have hKrad : K ≤ I.radical := by
    intro h hh
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hx' : ∀ i, eval x (f i) = 0 := fun i => by
      have := hx (f i) (Ideal.subset_span ⟨i, rfl⟩)
      simpa [aeval_eq_eval] using this
    have := (hmemK h).mp hh x ((hSZ x).mpr hx')
    simpa [aeval_eq_eval] using this
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hKrad (IsNoetherian.noetherian K)
  -- local step at each zero
  have hloc : ∀ p ∈ S, bezMax p ≤ I ⊔ bezMax p ^ (N + 1) := fun p hp =>
    bez_max_le_sup_pow I (bezMax p)
      (bez_max_le_sup_sq f p ((hSZ p).mp hp) (hjac p ((hSZ p).mp hp))) N
  have hcop : (S : Set (Fin n → ℂ)).Pairwise
      (Function.onFun IsCoprime fun p => I ⊔ bezMax p ^ (N + 1)) := by
    intro p _ q _ hpq
    have h1 : IsCoprime (bezMax p) (bezMax q) :=
      Ideal.isCoprime_iff_sup_eq.mpr (bez_max_sup_eq_top hpq)
    have h2 := Ideal.isCoprime_iff_sup_eq.mp (h1.pow (m := N + 1) (n := N + 1))
    refine Ideal.isCoprime_iff_sup_eq.mpr (eq_top_iff.mpr ?_)
    rw [← h2]
    exact sup_le_sup le_sup_right le_sup_right
  have hKI : K ≤ I := by
    have h1 : K ≤ ⨅ p ∈ S, (I ⊔ bezMax p ^ (N + 1)) := by
      refine le_iInf₂ fun p hp => ?_
      exact (Finset.inf_le hp).trans (hloc p hp)
    rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop] at h1
    refine h1.trans ((bez_prod_sup_le S I _).trans (sup_le le_rfl ?_))
    rw [Finset.prod_pow]
    calc (∏ p ∈ S, bezMax p) ^ (N + 1) ≤ K ^ (N + 1) :=
          Ideal.pow_right_mono Ideal.prod_le_inf _
      _ ≤ K ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
      _ ≤ I := hN
  -- evaluation at the zeros is injective on `C[x]/(f)`
  let φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] (S → ℂ) :=
    AlgHom.pi fun p : S => (aeval p.1 : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ)
  have hφI : ∀ a ∈ I, φ a = 0 := by
    intro a ha
    funext p
    have : a ∈ K := by
      rw [hmemK]
      intro q hq
      have hIK : I ≤ bezMax q := by
        rw [hI, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact mem_bezMax.mpr (((hSZ q).mp hq) i)
      exact mem_bezMax.mp (hIK ha)
    have h := (hmemK a).mp this p.1 p.2
    simpa [φ, aeval_eq_eval] using h
  let Φ := Ideal.Quotient.liftₐ I φ hφI
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hKI
    rw [hmemK]
    intro p hp
    have e : Φ (Ideal.Quotient.mk I a) = φ a := rfl
    have := congrFun (e.symm.trans hy) ⟨p, hp⟩
    simpa [φ, aeval_eq_eval] using this
  have := LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
  simpa using this

/-- **Count lemma B** (the statement of L-gct-042). -/
theorem bezCountB_holds : BezCountB := by
  intro n f hinf hjac
  obtain ⟨S, hS, hS0⟩ := bez_points_ge f hjac
  exact ⟨S, (bez_finrank_ge f hinf).trans hS, hS0⟩

end PEqualNP.Gct.Helpers
