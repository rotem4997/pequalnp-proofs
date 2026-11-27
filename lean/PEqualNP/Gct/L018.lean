import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Tangent

/-! L-gct-018: a polynomial vanishing on a smooth hypersurface `{p = 0}` near a point has zero
derivative along the tangent space there (inverse function theorem). -/

theorem PEqualNP.Gct.L018 :
    ∀ (k : ℕ) (p q : MvPolynomial (Fin k) ℂ) (x : Fin k → ℂ), MvPolynomial.eval x p = 0 →
      (∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i p) ≠ 0) →
      (∀ᶠ y in nhds x, MvPolynomial.eval y p = 0 → MvPolynomial.eval y q = 0) →
      ∀ t : Fin k → ℂ, ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i p) = 0 →
        ∑ i, t i * MvPolynomial.eval x (MvPolynomial.pderiv i q) = 0 :=
  fun _ p q x hpx hgrad hq t ht =>
    PEqualNP.Gct.Helpers.pderiv_vanish_of_vanish_on_hypersurface p q x hpx hgrad hq t ht
