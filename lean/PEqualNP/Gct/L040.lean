import PEqualNP.Gct.L039
import PEqualNP.Gct.Helpers.PolarLift

/-- The determinant side of the smooth-form bound: the simple polar points of a determinant of
affine forms satisfy a weighted count, by the weighted Bezout bound on the lifted system in the
point and the two kernel vectors. -/
theorem PEqualNP.Gct.L040 :
    ∀ (h n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)), (∀ i j, (A i j).totalDegree ≤ 1) → ∀ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) → ∀ p q : ℕ, S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n) :=
  PEqualNP.Gct.Helpers.polar_count_of PEqualNP.Gct.L039
