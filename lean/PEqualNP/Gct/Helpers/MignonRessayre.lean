import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetExprHessian

/-! The Hessian bound of L-gct-014 on any finite type of variables. Helper for L-gct-009. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

/-- At a zero of a polynomial with a determinantal expression of size `n`, its Hessian has rank
at most `2n`. -/
theorem rank_hess_detExpr_gen {τ : Type} [Fintype τ] [DecidableEq τ] {n : ℕ}
    (p : MvPolynomial τ ℂ) (y : τ → ℂ)
    (hp : PEqualNP.Gct.HasDetExpression p n) (h0 : eval y p = 0) :
    (hess p y).rank ≤ 2 * n := by
  obtain ⟨A, hA, rfl⟩ := hp
  let φ : Fin n × Fin n → MvPolynomial τ ℂ := fun q => A q.1 q.2
  have hbind : bind₁ φ (PEqualNP.Gct.detPoly ℂ n) = A.det := by
    simp only [PEqualNP.Gct.detPoly]
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp [φ]
  have hc : ∀ q a, pderiv a (φ q) = C ((A q.1 q.2).coeff (Finsupp.single a 1)) :=
    fun q a => pderiv_of_totalDegree_le_one _ (hA q.1 q.2) a
  have hev : eval (fun q => eval y (φ q)) (PEqualNP.Gct.detPoly ℂ n) = 0 := by
    have : eval y (bind₁ φ (PEqualNP.Gct.detPoly ℂ n)) =
        eval (fun q => eval y (φ q)) (PEqualNP.Gct.detPoly ℂ n) := by
      show eval₂Hom (RingHom.id ℂ) y _ = _
      rw [eval₂Hom_bind₁]
      rfl
    rw [← this, hbind, h0]
  rw [← hbind]
  exact (rank_hess_bind₁_le φ _ hc _ y).trans (rank_hess_det_singular _ hev)

end PEqualNP.Gct.Helpers
