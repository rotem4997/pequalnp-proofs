import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermHessian

/-! L-gct-013: for `m ≥ 2` the permanent has a zero where its Hessian has full rank `m²`
(Mignon and Ressayre 2004). The zero is the all-ones matrix with `1 - m` at `(0, 0)`. -/

open PEqualNP.Gct.Helpers in
theorem PEqualNP.Gct.L013 :
    ∀ m : ℕ, 2 ≤ m → ∃ x : Fin m × Fin m → ℂ,
      MvPolynomial.eval x (PEqualNP.Gct.permPoly ℂ m) = 0 ∧
      (Matrix.of fun a b : Fin m × Fin m => MvPolynomial.eval x (MvPolynomial.pderiv a
        (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ m)))).rank = m ^ 2 := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  refine ⟨mrPoint n, perm_mrPoint n, ?_⟩
  have hH : (Matrix.of fun a b : Fin (n + 2) × Fin (n + 2) => MvPolynomial.eval (mrPoint n)
      (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ (n + 2))))) =
      Matrix.of (hessEntry n) := by
    ext a b
    simp only [Matrix.of_apply, hess_perm_entry]
  rw [hH]
  have hker : ∀ v, (Matrix.of (hessEntry n)).mulVec v = 0 → v = 0 := by
    intro v hv
    have key := hess_kernel n (n.factorial : ℂ) (((n + 2 : ℕ) : ℂ) * ((n - 1).factorial : ℂ))
      (by exact_mod_cast Nat.factorial_ne_zero n) ?_ (fun k l => v (k, l)) ?_
    · funext p
      exact key p.1 p.2
    · intro e
      have hlt : n.factorial < (n + 2) * (n - 1).factorial := by
        rcases n with _ | n
        · simp
        · rw [Nat.factorial_succ]
          simp only [Nat.add_sub_cancel]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos n)
      have : ((n.factorial : ℕ) : ℂ) = (((n + 2) * (n - 1).factorial : ℕ) : ℂ) := by
        rw [e]; push_cast; ring
      exact absurd (Nat.cast_injective this) (ne_of_lt hlt)
    · intro i j
      have := congrFun hv (i, j)
      rw [hess_mulVec] at this
      simpa using this
  have hinj : Function.Injective (Matrix.of (hessEntry n)).mulVec := by
    intro v w hvw
    have := hker (v - w) (by rw [Matrix.mulVec_sub, hvw, sub_self])
    exact sub_eq_zero.mp this
  rw [Matrix.rank_of_isUnit _ (Matrix.mulVec_injective_iff_isUnit.mp hinj)]
  simp [Fintype.card_prod, sq]
