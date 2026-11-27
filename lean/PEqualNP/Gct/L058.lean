import PEqualNP.Gct.L053
import PEqualNP.Gct.Helpers.BertiniLite

/-- Bertini-lite: a form of degree r in n variables whose singular points all lie in finitely
many subspaces of dimension at most q has, for every d with d + q ≤ n, a linear substitution
into d variables whose result has no singular point other than the origin. -/
theorem PEqualNP.Gct.L058 :
    ∀ (n d q r : ℕ) (F : MvPolynomial (Fin n) ℂ) (W : Finset (Submodule ℂ (Fin n → ℂ))), F.IsHomogeneous r → (∀ V ∈ W, Module.finrank ℂ V ≤ q) → (∀ x : Fin n → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → ∃ V ∈ W, x ∈ V) → d + q ≤ n → ∃ M : Fin n → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun k => ∑ t, MvPolynomial.C (M k t) * MvPolynomial.X t) F)) = 0) → y = 0 :=
  PEqualNP.Gct.Helpers.bertini_lite_of PEqualNP.Gct.L053
