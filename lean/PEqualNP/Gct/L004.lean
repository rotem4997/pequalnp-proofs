import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.CommRing

/-! L-gct-004: `perm_2 = det [[x₀₀, -x₀₁], [x₁₀, x₁₁]]` (Pólya 1913). -/

theorem PEqualNP.Gct.L004 :
    ∀ (R : Type) [CommRing R], PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly R 2) 2 := by
  intro R _
  have hX : ∀ q : Fin 2 × Fin 2, (MvPolynomial.X q : MvPolynomial (Fin 2 × Fin 2) R).totalDegree ≤ 1 :=
    fun q => by simpa [MvPolynomial.X] using MvPolynomial.totalDegree_monomial_le (Finsupp.single q 1) (1 : R)
  refine ⟨!![MvPolynomial.X (0, 0), -MvPolynomial.X (0, 1); MvPolynomial.X (1, 0), MvPolynomial.X (1, 1)],
    ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [MvPolynomial.totalDegree_neg, hX]
  · rw [Matrix.det_fin_two_of]
    simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Fin.prod_univ_two, Matrix.mvPolynomialX_apply]
    rw [show (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} from by decide,
      Finset.sum_pair (by decide)]
    simp only [Equiv.Perm.one_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
