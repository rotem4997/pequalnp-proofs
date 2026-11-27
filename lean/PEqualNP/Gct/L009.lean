import PEqualNP.Defs
import PEqualNP.Gct.L013
import PEqualNP.Gct.Helpers.MignonRessayre

/-! L-gct-009: over `ℂ`, every determinantal expression of `perm_m` has size at least `m²/2`
(Mignon and Ressayre 2004). For `m ≥ 2`, the permanent has a zero with Hessian of rank `m²`
(L-gct-013), and at a zero the Hessian of a polynomial with an expression of size `n` has rank
at most `2n` (the argument of L-gct-014). For `m = 1`, the size cannot be `0`. -/

theorem PEqualNP.Gct.L009 :
    ∀ m n : ℕ, PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ 2 * n := by
  intro m n hp
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        obtain ⟨A, -, hA⟩ := hp
        rw [Matrix.det_isEmpty] at hA
        have h1 := congrArg (MvPolynomial.eval (fun _ => (0 : ℂ))) hA
        simp [PEqualNP.Gct.permPoly, Matrix.permanent] at h1
      · omega
  · obtain ⟨x, hx0, hrank⟩ := PEqualNP.Gct.L013 m hm
    rw [← hrank]
    exact PEqualNP.Gct.Helpers.rank_hess_detExpr_gen _ x hp hx0
