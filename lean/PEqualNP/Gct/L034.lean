import PEqualNP.Gct.L047
import PEqualNP.Gct.L048
import PEqualNP.Gct.L049

/-- L-gct-034, half (a) of L-gct-024: a smooth complex form of degree `r` in `h + 2` variables has
a chart and polar directions with at least `(r - 1) ^ (h + 1)` simple polar points. The assembly
L-gct-049 applied to H4 (L-gct-047) and the chart choice (L-gct-048). -/
theorem PEqualNP.Gct.L034 :
    ∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (r - 1) ^ (h + 1) ≤ S.card ∧ ∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons G (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0 :=
  PEqualNP.Gct.L049 PEqualNP.Gct.L047 PEqualNP.Gct.L048
