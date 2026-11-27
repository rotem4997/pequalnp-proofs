import PEqualNP.Gct.L030
import PEqualNP.Gct.L041
import PEqualNP.Gct.L043
import PEqualNP.Gct.Helpers.SmoothAssembly

/-!
# Assembly of the power sum bound

The bound `(r - 1) * (d - 1) ≤ 11 * n` for the power sum `∑ i, X i ^ r` in `d` variables with a
border determinantal expression of size `n`, from the statement of the weighted count for the
polar system of a determinant of affine forms (L-gct-040, half (b)), the checked count of simple
polar points of the Fermat form (L-gct-043), the checked persistence of nondegenerate zeros
(L-gct-030) and the checked arithmetic (L-gct-041).
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- The power sum bound, assembled from the statement of the weighted count. -/
theorem psumAsm_bound_of
    (hC : ∀ (h n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)), (∀ i j, (A i j).totalDegree ≤ 1) → ∀ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) → ∀ p q : ℕ, S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) :
    ∀ (d r n : ℕ), 2 ≤ d → 2 ≤ r → PEqualNP.Gct.HasBorderDetExpression (∑ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r) n → (r - 1) * (d - 1) ≤ 11 * n := by
  intro d r n hd hr hb
  obtain ⟨h, rfl⟩ : ∃ h, d = h + 2 := ⟨d - 2, by omega⟩
  obtain ⟨a, v, S, hcard, hS⟩ := PEqualNP.Gct.L043 h r hr
  obtain ⟨q, hq, hconv⟩ := hb
  choose A hA hdet using hq
  obtain ⟨K, hK⟩ := PEqualNP.Gct.L030 (h + 2) (n + 1)
    (Fin.cons (∑ j, MvPolynomial.X j ^ r) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (∑ j, MvPolynomial.X j ^ r))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ)
    (fun m => (Fin.cons (q m) (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j (q m))) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ))
    (fun m i => polar_totalDegree_le n (q m)
      (by rw [← hdet m]; exact totalDegree_det_le_size _ (hA m)) a v i)
    (fun i s => polar_tendsto _ q hconv a v i s) S hS
  obtain ⟨T, hTcard, hT⟩ := hK K le_rfl
  have hcount := hC h n (A K) (hA K) a v T (by rw [hdet K]; exact hT)
  have hpow : (r - 1) ^ (h + 1) ≤ T.card := by
    rw [hTcard, pow_succ, mul_comm]
    exact le_trans (Nat.mul_le_mul_right _ (Nat.sub_le r 1)) hcard
  have hfin : (r - 1) * (h + 1) ≤ 11 * n :=
    PEqualNP.Gct.L041 h n r T.card hr hpow hcount
  have e : h + 2 - 1 = h + 1 := by omega
  rw [e]
  exact hfin

end PEqualNP.Gct.Helpers
