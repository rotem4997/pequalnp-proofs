import PEqualNP.Gct.Helpers.Rung.BoundedZeros

/-- L-gct-059 (Fact Z): if the forms `g` of degree `e ≥ 1` have only the trivial common zero, the
finite sets of common zeros of systems `f` with top parts `g` (`totalDegree (f i - g i) < e`) are
bounded in size by one `M` independent of `f`. The square case of `BoundedZeros`. -/
theorem PEqualNP.Gct.L059 :
    ∀ (l e : ℕ) (g : Fin l → MvPolynomial (Fin l) ℂ), 1 ≤ e → (∀ i, (g i).IsHomogeneous e) → (∀ x : Fin l → ℂ, (∀ i, MvPolynomial.eval x (g i) = 0) → x = 0) → ∃ M : ℕ, ∀ (f : Fin l → MvPolynomial (Fin l) ℂ), (∀ i, (f i - g i).totalDegree < e) → ∀ S : Finset (Fin l → ℂ), (∀ x ∈ S, ∀ i, MvPolynomial.eval x (f i) = 0) → S.card ≤ M :=
  fun l e g _ hgh hg => PEqualNP.Gct.Rung.boundedZeros l l e g hgh hg
