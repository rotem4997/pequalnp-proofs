import PEqualNP.Gct.Helpers.PsumAsm

/-- L-gct-046: the weighted count of simple polar points of a determinant of affine matrices
(the statement of L-gct-040, half (b)) implies the power sum target L-gct-045: a border
determinantal expression of size `n` of `∑ i < d, X i ^ r` forces `(r - 1) * (d - 1) ≤ 11 * n`. -/
theorem PEqualNP.Gct.L046 :
    (∀ (h n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)), (∀ i j, (A i j).totalDegree ≤ 1) → ∀ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) → ∀ p q : ℕ, S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) → (∀ (d r n : ℕ), 2 ≤ d → 2 ≤ r → PEqualNP.Gct.HasBorderDetExpression (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r) n → (r - 1) * (d - 1) ≤ 11 * n) :=
  PEqualNP.Gct.Helpers.psumAsm_bound_of
