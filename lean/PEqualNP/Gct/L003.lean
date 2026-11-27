import PEqualNP.Defs

/-! L-gct-003: the determinant of an `n × n` matrix of polynomials of total degree at most one
has total degree at most `n`. -/

theorem PEqualNP.Gct.L003 :
    ∀ (σ R : Type) [CommRing R] (p : MvPolynomial σ R) (n : ℕ),
      PEqualNP.Gct.HasDetExpression p n → p.totalDegree ≤ n := by
  intro σ R _ p n ⟨A, hA, hdet⟩
  subst hdet
  rw [Matrix.det_apply']
  refine MvPolynomial.totalDegree_finsetSum_le fun τ _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hc : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R).totalDegree = 0 := by
    rw [← map_intCast (MvPolynomial.C (σ := σ) (R := R))]
    exact MvPolynomial.totalDegree_C _
  rw [hc, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (A (τ i) i).totalDegree ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => hA _ _
    _ = n := by simp
