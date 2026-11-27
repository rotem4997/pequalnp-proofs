import PEqualNP.Defs
import PEqualNP.Gct.Helpers.BorderMR

/-! L-gct-010: over `ℂ`, every border determinantal expression of `perm_m` has size at least
`m²/2` (border Mignon-Ressayre, Landsberg, Manivel and Ressayre 2013). For `m ≥ 2`, the zero of
the permanent with Hessian of rank `m²` (L-gct-013) is a limit of zeros of the approximating
polynomials (inverse function theorem), their Hessians there tend to the full-rank one, and the
rank bound at a zero (L-gct-014) applies to one of them. For `m < 2` the bound is immediate or
the size cannot be `0`. -/

theorem PEqualNP.Gct.L010 :
    ∀ m n : ℕ, PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n →
      m ^ 2 ≤ 2 * n := by
  intro m n hp
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        obtain ⟨q, hq, hlim⟩ := hp
        have hq1 : ∀ k, q k = 1 := by
          intro k
          obtain ⟨A, -, hA⟩ := hq k
          rw [← hA, Matrix.det_isEmpty]
        have h0 := hlim 0
        simp only [hq1, MvPolynomial.coeff_one, ↓reduceIte] at h0
        have h1 := tendsto_nhds_unique tendsto_const_nhds h0
        have h2 : (PEqualNP.Gct.permPoly ℂ 1).coeff 0 = 0 := by
          simp [PEqualNP.Gct.permPoly, Matrix.permanent, MvPolynomial.coeff_X]
        rw [h2] at h1
        exact absurd h1 one_ne_zero
      · omega
  · exact PEqualNP.Gct.Helpers.BorderMR.border_mr m n hm hp
