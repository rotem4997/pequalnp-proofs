import Mathlib

/-!
Helpers H and P for Lemma S2 (route R3, R4, start of R5): the ideal of variables `m0` in
`MvPolynomial (Fin d) k` is prime, has height at least `d`, so it is minimal over no ideal
spanned by fewer than `d` elements; if it is not minimal over `I ≤ m0`, some prime between
misses a variable.
-/

namespace PEqualNP.Gct.Helpers.S2Height

open MvPolynomial

variable (k : Type*) [Field k] (d : ℕ)

/-- The ideal spanned by all the variables. -/
noncomputable abbrev m0 : Ideal (MvPolynomial (Fin d) k) := Ideal.span (Set.range MvPolynomial.X)

theorem m0_isPrime : (m0 k d).IsPrime := MvPolynomial.isPrime_idealOfVars (Fin d) k

theorem mem_m0_iff (p : MvPolynomial (Fin d) k) :
    p ∈ m0 k d ↔ MvPolynomial.constantCoeff p = 0 := by
  rw [m0, ← Set.image_univ, mem_ideal_span_X_image]
  constructor
  · intro h
    rw [constantCoeff_eq]
    by_contra hc
    obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.mpr hc)
    exact hi rfl
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mem_support_iff, ← constantCoeff_eq] at hm
      exact hm h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ _, hi⟩

/-- The chain of primes `P i = (X j : j < i)`. -/
private noncomputable def chainIdeal (i : ℕ) : Ideal (MvPolynomial (Fin d) k) :=
  Ideal.span (MvPolynomial.X '' {j : Fin d | j.val < i})

private theorem chainIdeal_isPrime (i : ℕ) : (chainIdeal k d i).IsPrime :=
  span_X_image_isPrime _

private theorem chainIdeal_lt (i : ℕ) (hi : i < d) :
    chainIdeal k d i < chainIdeal k d (i + 1) := by
  refine lt_of_le_of_ne ?_ ?_
  · refine Ideal.span_mono (Set.image_mono ?_)
    intro j hj
    simp only [Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro h
    have hmem : (X ⟨i, hi⟩ : MvPolynomial (Fin d) k) ∈ chainIdeal k d (i + 1) :=
      Ideal.subset_span ⟨⟨i, hi⟩, by simp, rfl⟩
    rw [← h, chainIdeal, mem_ideal_span_X_image] at hmem
    obtain ⟨j, hj, hne⟩ := hmem (Finsupp.single ⟨i, hi⟩ 1) (by simp [support_X])
    simp only [Set.mem_ofPred_eq] at hj
    rw [Finsupp.single_apply] at hne
    split_ifs at hne with hij
    · subst hij; simp at hj
    · exact hne rfl

private theorem le_height_chainIdeal (i : ℕ) (hi : i ≤ d) :
    (i : ℕ∞) ≤ (chainIdeal k d i).height := by
  induction i with
  | zero => simp
  | succ n ih =>
    have := chainIdeal_isPrime k d n
    have := chainIdeal_isPrime k d (n + 1)
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (chainIdeal k d n).height + 1 := by gcongr; exact ih (by omega)
      _ ≤ (chainIdeal k d (n + 1)).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime (chainIdeal_lt k d n (by omega))

private theorem chainIdeal_d : chainIdeal k d d = m0 k d := by
  rw [chainIdeal, m0, ← Set.image_univ]
  congr 2
  ext j
  simp

theorem le_height_m0 : (d : ℕ∞) ≤ (m0 k d).height := by
  rw [← chainIdeal_d]
  exact le_height_chainIdeal k d d le_rfl

theorem card_ge_of_minimal (s : Finset (MvPolynomial (Fin d) k))
    (h : m0 k d ∈ (Ideal.span (s : Set (MvPolynomial (Fin d) k))).minimalPrimes) :
    d ≤ s.card := by
  have h1 := le_height_m0 k d
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset h
  exact_mod_cast h1.trans h2

theorem exists_prime_lt (I : Ideal (MvPolynomial (Fin d) k)) (hI : I ≤ m0 k d)
    (h : m0 k d ∉ I.minimalPrimes) :
    ∃ P : Ideal (MvPolynomial (Fin d) k), P.IsPrime ∧ I ≤ P ∧ P ≤ m0 k d ∧
      ∃ i : Fin d, MvPolynomial.X i ∉ P := by
  have hp := m0_isPrime k d
  obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le hI
  have hne : P ≠ m0 k d := by
    rintro rfl; exact h hPmin
  refine ⟨P, hPmin.isPrime, hPmin.1.2, hPle, ?_⟩
  by_contra hall
  push Not at hall
  apply hne
  refine le_antisymm hPle (Ideal.span_le.mpr ?_)
  rintro _ ⟨i, rfl⟩
  exact hall i

end PEqualNP.Gct.Helpers.S2Height
