import PEqualNP.Gct.Helpers.BadZero

open PEqualNP.Gct.Helpers.BadZero in
/-- The zero of the permanent with `-1` at the corner, ones at `(0,1)`, `(1,0)` and on the rest of
the diagonal, written out, with a linear space of dimension `(k + 1) k / 2` through it inside the
permanent hypersurface. Corrects L-gct-081, which did not name the zero. -/
theorem PEqualNP.Gct.L085 : ∀ k : ℕ, ∃ L : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ), (∀ t ∈ L, MvPolynomial.eval ((fun p : Fin (k + 2) × Fin (k + 2) => if (p.1 : ℕ) = 0 ∧ (p.2 : ℕ) = 0 then (-1 : ℂ) else if p.1 = p.2 ∨ ((p.1 : ℕ) = 0 ∧ (p.2 : ℕ) = 1) ∨ ((p.1 : ℕ) = 1 ∧ (p.2 : ℕ) = 0) then 1 else 0) + t) (PEqualNP.Gct.permPoly ℂ (k + 2)) = 0) ∧ 2 * Module.finrank ℂ L = (k + 1) * k := by
  intro k
  refine ⟨upperSpace k, fun t ht => ?_, two_mul_finrank_upperSpace k⟩
  have h := eval_badZero_add (k := k) ht
  have e : (fun p : Fin (k + 2) × Fin (k + 2) => if (p.1 : ℕ) = 0 ∧ (p.2 : ℕ) = 0 then (-1 : ℂ) else if p.1 = p.2 ∨ ((p.1 : ℕ) = 0 ∧ (p.2 : ℕ) = 1) ∨ ((p.1 : ℕ) = 1 ∧ (p.2 : ℕ) = 0) then 1 else 0) = badZero k := by
    funext p
    obtain ⟨a, b⟩ := p
    simp only [badZero, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_one]
  rw [e]; exact h
