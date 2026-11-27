import PEqualNP.Gct.Helpers.TransSection

/-- Smooth linear section from a transversal subspace: if the full gradient of the form `G`
vanishes on the image of the linear map `L` only at `L 0`, then for some linear map `M` the form
`G ∘ M` in `d` variables is smooth. -/
theorem PEqualNP.Gct.L053 :
    ∀ (N d r : ℕ) (G : MvPolynomial (Fin N) ℂ) (L : Fin N → Fin d → ℂ), G.IsHomogeneous r → (∀ y : Fin d → ℂ, (∀ i, MvPolynomial.eval (fun n => ∑ s, L n s * y s) (MvPolynomial.pderiv i G) = 0) → y = 0) → ∃ M : Fin N → Fin d → ℂ, ∀ y : Fin d → ℂ, (∀ s, MvPolynomial.eval y (MvPolynomial.pderiv s (MvPolynomial.bind₁ (fun n => ∑ t, MvPolynomial.C (M n t) * MvPolynomial.X t) G)) = 0) → y = 0 :=
  PEqualNP.Gct.Helpers.transSection
