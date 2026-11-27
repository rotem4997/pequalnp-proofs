import Mathlib

/-!
Helpers for `PEqualNP.Gct.L150`: a polynomial with nonzero constant term over a field of
characteristic zero, with `s` distinct roots in an algebraic closure, whose coefficients vanish on
a window `[n, n + s)` with `n ≥ 1`, has all coefficients from `n` on equal to zero.
-/

namespace PEqualNP.Gct.Helpers.GapLemma

open Polynomial

/-- Coefficient recursion: from `A * H' = B * H` with `A.coeff 0 ≠ 0`, `deg A ≤ s`, `deg B < s`,
a window of `s` zero coefficients starting at `n ≥ 1` propagates to all coefficients from `n` on. -/
theorem coeff_gap {F : Type*} [Field F] [CharZero F] (H A B : F[X]) (s n : ℕ)
    (hA0 : A.coeff 0 ≠ 0) (hAdeg : ∀ j, s < j → A.coeff j = 0)
    (hB : ∀ j, s ≤ j → B.coeff j = 0) (heq : A * derivative H = B * H) (hn : 1 ≤ n)
    (hgap : ∀ i, n ≤ i → i < n + s → H.coeff i = 0) : ∀ i, n ≤ i → H.coeff i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hni
  by_cases hi : i < n + s
  · exact hgap i hni hi
  rw [not_lt] at hi
  have key := congrArg (fun p => p.coeff (i - 1)) heq
  simp only [coeff_mul] at key
  have hR : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (i - 1), B.coeff x.1 * H.coeff x.2) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
    by_cases hbs : b.1 < s
    · rw [ih b.2 (by omega) (by omega), mul_zero]
    · rw [hB _ (by omega), zero_mul]
  have hL : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (i - 1),
      A.coeff x.1 * (derivative H).coeff x.2) = A.coeff 0 * (derivative H).coeff (i - 1) := by
    rw [Finset.sum_eq_single (0, i - 1)]
    · intro b hb hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hb
      have hb1 : b.1 ≠ 0 := by
        intro h0
        apply hne
        ext <;> simp <;> omega
      by_cases hbs : s < b.1
      · rw [hAdeg _ hbs, zero_mul]
      · rw [coeff_derivative, ih (b.2 + 1) (by omega) (by omega), zero_mul, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  rw [hR, hL, coeff_derivative] at key
  have hi1 : i - 1 + 1 = i := by omega
  rw [hi1] at key
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hA0
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exfalso
    have : ((i - 1 : ℕ) : F) + 1 = ((i - 1 + 1 : ℕ) : F) := by push_cast; ring
    rw [this, hi1] at h
    exact (Nat.cast_ne_zero.2 (by omega : i ≠ 0)) h

/-- Over an algebraically closed field of characteristic zero, a polynomial `H` with nonzero
constant term satisfies `A * H' = B * H` with `A.coeff 0 ≠ 0`, `deg A ≤ s` and `deg B < s`, where
`s` is the number of distinct roots of `H`. -/
theorem factor {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] [DecidableEq F] (H : F[X])
    (h0 : H.coeff 0 ≠ 0) : ∃ A B : F[X], A.coeff 0 ≠ 0 ∧
      (∀ j, H.roots.dedup.card < j → A.coeff j = 0) ∧
      (∀ j, H.roots.dedup.card ≤ j → B.coeff j = 0) ∧ A * derivative H = B * H := by
  have hH : H ≠ 0 := by
    rintro rfl
    exact h0 (coeff_zero 0)
  set R := H.roots with hRdef
  set D := R.dedup with hDdef
  set E := R - D with hEdef
  set A0 := (D.map fun a => X - C a).prod with hA0def
  set Q := (E.map fun a => X - C a).prod with hQdef
  have hRDE : D + E = R := add_tsub_cancel_of_le (Multiset.dedup_le R)
  have hfac : C H.leadingCoeff * (A0 * Q) = H := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C
      (p := H) (IsAlgClosed.card_roots_eq_natDegree (p := H))
    rw [← hRdef, ← hRDE, Multiset.map_add, Multiset.prod_add] at h
    exact h
  have hQ : Q ∣ derivative H := by
    by_cases hd : derivative H = 0
    · rw [hd]
      exact dvd_zero _
    refine (Multiset.prod_X_sub_C_dvd_iff_le_roots hd E).2 ?_
    rw [Multiset.le_iff_count]
    intro r
    rw [hEdef, Multiset.count_sub, hDdef, Multiset.count_dedup, count_roots]
    by_cases hr : r ∈ R
    · simp only [hr, ↓reduceIte]
      rw [count_roots, derivative_rootMultiplicity_of_root ((mem_roots hH).1 hr)]
    · have h : rootMultiplicity r H = 0 := by
        rw [← count_roots]
        exact Multiset.count_eq_zero.2 hr
      rw [h, Nat.zero_sub]
      exact Nat.zero_le _
  obtain ⟨B0, hB0⟩ := hQ
  have hlc : H.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hH
  have hA0ne : A0 ≠ 0 := by
    intro h
    rw [h, zero_mul, mul_zero] at hfac
    exact hH hfac.symm
  have hQne : Q ≠ 0 := by
    intro h
    rw [h, mul_zero, mul_zero] at hfac
    exact hH hfac.symm
  refine ⟨C H.leadingCoeff * A0, B0, ?_, ?_, ?_, ?_⟩
  · intro h
    apply h0
    rw [← hfac, ← mul_assoc, mul_coeff_zero, h, zero_mul]
  · intro j hj
    apply coeff_eq_zero_of_natDegree_lt
    calc (C H.leadingCoeff * A0).natDegree ≤ A0.natDegree := natDegree_C_mul_le _ _
      _ = D.card := natDegree_multiset_prod_X_sub_C_eq_card D
      _ < j := hj
  · intro j hj
    by_cases hB : B0 = 0
    · rw [hB, coeff_zero]
    apply coeff_eq_zero_of_natDegree_lt
    have hdH : derivative H ≠ 0 := by
      rw [hB0]
      exact mul_ne_zero hQne hB
    have hnd : H.natDegree ≠ 0 := by
      intro h
      exact hdH (derivative_of_natDegree_zero h)
    have h1 := natDegree_derivative_lt hnd
    have h2 : (derivative H).natDegree = Q.natDegree + B0.natDegree := by
      rw [hB0, natDegree_mul hQne hB]
    have h3 : H.natDegree = A0.natDegree + Q.natDegree := by
      conv_lhs => rw [← hfac]
      rw [natDegree_C_mul hlc, natDegree_mul hA0ne hQne]
    have h4 : A0.natDegree = D.card := natDegree_multiset_prod_X_sub_C_eq_card D
    omega
  · rw [hB0]
    conv_rhs => rw [← hfac]
    ring

/-- The statement of `PEqualNP.Gct.L150`. -/
theorem main : ∀ (K : Type) [Field K] [CharZero K] (G : Polynomial K) (n : ℕ), G.coeff 0 ≠ 0 →
    1 ≤ n → (∀ i : ℕ, n ≤ i → i < n + (G.rootSet (AlgebraicClosure K)).ncard → G.coeff i = 0) →
    ∀ i : ℕ, n ≤ i → G.coeff i = 0 := by
  intro K _ _ G n h0 hn hgap
  classical
  let F := AlgebraicClosure K
  let H := G.map (algebraMap K F)
  have hcoeff : ∀ i, H.coeff i = algebraMap K F (G.coeff i) := fun i => coeff_map _ _
  have hs : (G.rootSet F).ncard = H.roots.dedup.card := by
    rw [rootSet_def, Set.ncard_coe_finset]
    rfl
  have hH0 : H.coeff 0 ≠ 0 := by
    rw [hcoeff]
    exact (map_ne_zero_iff _ (algebraMap K F).injective).2 h0
  obtain ⟨A, B, hA0, hAdeg, hB, heq⟩ := factor H hH0
  have hall := coeff_gap H A B _ n hA0 hAdeg hB heq hn (fun i h1 h2 => by
    rw [hcoeff, hgap i h1 (by rw [hs]; exact h2), map_zero])
  intro i hi
  apply (algebraMap K F).injective
  rw [← hcoeff, hall i hi, map_zero]

end PEqualNP.Gct.Helpers.GapLemma
