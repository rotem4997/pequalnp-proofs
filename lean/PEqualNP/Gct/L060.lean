import PEqualNP.Gct.L053
import PEqualNP.Gct.Helpers.BertiniLite

/-- Bertini-lite relative to a subspace: a form of degree r in n variables whose singular points
inside a subspace V all lie in finitely many subspaces of dimension at most q has, for every d
with d + q at most the dimension of V, a linear substitution into d variables whose result has
no singular point other than the origin. -/
theorem PEqualNP.Gct.L060 :
    ∀ (n d q r : ℕ) (F : MvPolynomial (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)) (W : Finset (Submodule ℂ (Fin n → ℂ))), F.IsHomogeneous r → (∀ U ∈ W, Module.finrank ℂ U ≤ q) → (∀ x ∈ V, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → ∃ U ∈ W, x ∈ U) → d + q ≤ Module.finrank ℂ V → ∃ M : Fin n → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun k => ∑ t, MvPolynomial.C (M k t) * MvPolynomial.X t) F)) = 0) → y = 0 :=
  PEqualNP.Gct.Helpers.bertini_lite_sub_of PEqualNP.Gct.L053
