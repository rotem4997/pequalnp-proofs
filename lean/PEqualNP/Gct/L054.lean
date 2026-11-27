import PEqualNP.Defs.Gct
import Mathlib

/-- L-gct-054: the red team restatement of the power sum target (limits of determinants of
affine linear matrices whose coefficients tend to those of `x_1^r + .. + x_d^r`, with the bound
stated over the reals) is equivalent to the statement of L-gct-045. -/
theorem PEqualNP.Gct.L054 :
    (∀ (d r n : ℕ) (A : ℕ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ)), 2 ≤ d → 2 ≤ r → (∀ (k : ℕ) (i j : Fin n), (A k i j).totalDegree ≤ 1) → (∀ s : Fin d →₀ ℕ, Filter.Tendsto (fun k : ℕ => (A k).det.coeff s) Filter.atTop (nhds (if ∃ i : Fin d, s = Finsupp.single i r then (1 : ℂ) else 0))) → ((r : ℝ) - 1) * ((d : ℝ) - 1) / 11 ≤ (n : ℝ)) ↔ (∀ (d r n : ℕ), 2 ≤ d → 2 ≤ r → PEqualNP.Gct.HasBorderDetExpression (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r) n → (r - 1) * (d - 1) ≤ 11 * n) := by
  classical
  have key : ∀ (d r : ℕ), 2 ≤ r → ∀ s : Fin d →₀ ℕ,
      (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r).coeff s
        = if ∃ i : Fin d, s = Finsupp.single i r then (1 : ℂ) else 0 := by
    intro d r hr s
    have hr0 : r ≠ 0 := by omega
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [ite_eq_right_iff]
        intro hEq
        exfalso
        apply hji
        have := congrArg (fun f => f j) hEq
        simp only [Finsupp.single_eq_same] at this
        by_contra hne
        rw [Finsupp.single_eq_of_ne hne] at this
        exact hr0 this
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · apply Finset.sum_eq_zero
      intro j _
      rw [ite_eq_right_iff]
      intro hEq
      exact absurd ⟨j, hEq.symm⟩ h
  have arith : ∀ (d r n : ℕ), 2 ≤ d → 2 ≤ r →
      (((r : ℝ) - 1) * ((d : ℝ) - 1) / 11 ≤ (n : ℝ) ↔ (r - 1) * (d - 1) ≤ 11 * n) := by
    intro d r n hd hr
    have h1 : ((r : ℝ) - 1) = ((r - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    have h2 : ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [h1, h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 11)]
    constructor
    · intro h
      have h' : (((r - 1) * (d - 1) : ℕ) : ℝ) ≤ ((11 * n : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast h'
    · intro h
      have h' : (((r - 1) * (d - 1) : ℕ) : ℝ) ≤ ((11 * n : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at h'
      linarith
  constructor
  · intro H d r n hd hr hb
    obtain ⟨q, hq, hlim⟩ := hb
    choose A hA hdet using hq
    refine (arith d r n hd hr).1 (H d r n A hd hr hA ?_)
    intro s
    have := hlim s
    rw [key d r hr s] at this
    simpa only [hdet] using this
  · intro H d r n A hd hr hA hlim
    refine (arith d r n hd hr).2 (H d r n hd hr ⟨fun k => (A k).det, fun k => ⟨A k, hA k, rfl⟩, ?_⟩)
    intro s
    rw [key d r hr s]
    exact hlim s
