import PEqualNP.Gct.Helpers.PolarFermat

/-- The Fermat form `sum_j x_j ^ r` in `h + 2` variables has at least `r * (r - 1) ^ h` simple
polar points on a chart, exhibited. -/
theorem PEqualNP.Gct.L043 :
    ∀ (h r : ℕ), 2 ≤ r → ∃ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), r * (r - 1) ^ h ≤ S.card ∧ ∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons (∑ j, MvPolynomial.X j ^ r) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (∑ j, MvPolynomial.X j ^ r))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons (∑ j, MvPolynomial.X j ^ r) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (∑ j, MvPolynomial.X j ^ r))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0 :=
  fun h r hr =>
    ⟨PEqualNP.Gct.Helpers.fA h, PEqualNP.Gct.Helpers.fV h r, PEqualNP.Gct.Helpers.fS h r,
      (PEqualNP.Gct.Helpers.fS_card h r hr).ge, PEqualNP.Gct.Helpers.fS_good h r hr⟩
