import PEqualNP.Gct.Helpers.LS4.PermFour

/-! Helper for L-gct-091 (LS(4) <= 5), the `r <= 1` cases of the split by `dim (L ∩ DC)`.
`W_c` is the space of `4 x 4` matrices `t` with every column sum zero (`t (i, j)`: row `i`,
column `j`). On `W_c`, `perm (J + t) - 24 = -2 Σ_i e₂(row i) + 2 Σ_i e₃(row i) + perm t`, where
`e₂`, `e₃` are the elementary symmetric polynomials of the four entries of a row.
The hypothesis is satisfiable (`t = 0`, or any `t` with rows `u, -u, 0, 0`); without it the
identity fails (sympy check, `t` the single entry `t (0, 0) = 1` gives `perm (J + t) - 24 = 6`
against `0`). -/

namespace PEqualNP.Gct.LS4

open Finset

/-- `e₂` of row `i`. -/
def rowE2 (t : Fin 4 × Fin 4 → ℂ) (i : Fin 4) : ℂ :=
  t (i, 0) * t (i, 1) + t (i, 0) * t (i, 2) + t (i, 0) * t (i, 3) +
    t (i, 1) * t (i, 2) + t (i, 1) * t (i, 3) + t (i, 2) * t (i, 3)

/-- `e₃` of row `i`. -/
def rowE3 (t : Fin 4 × Fin 4 → ℂ) (i : Fin 4) : ℂ :=
  t (i, 0) * t (i, 1) * t (i, 2) + t (i, 0) * t (i, 1) * t (i, 3) +
    t (i, 0) * t (i, 2) * t (i, 3) + t (i, 1) * t (i, 2) * t (i, 3)

/-- The `W_c` identity. -/
theorem perm_J_add_of_colsum_zero (t : Fin 4 × Fin 4 → ℂ) (hc : ∀ j, ∑ i, t (i, j) = 0) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) - 24 =
      -2 * ∑ i, rowE2 t i + 2 * ∑ i, rowE3 t i +
        MvPolynomial.eval t (PEqualNP.Gct.permPoly ℂ 4) := by
  have h3 : ∀ j, t (3, j) = -(t (0, j) + t (1, j) + t (2, j)) := by
    intro j
    have := hc j
    rw [Fin.sum_univ_four] at this
    linear_combination this
  rw [eval_perm_four, eval_perm_four]
  simp only [Fin.sum_univ_four, rowE2, rowE3, h3]
  ring

/-- The identity is not vacuous and needs its hypothesis: at the single entry `t (0, 0) = 1`
(column sum `1`) the left side is `6`, while every row has at most one nonzero entry, so the
  right side is `0`. -/
theorem perm_J_add_single_ne :
    MvPolynomial.eval (fun p => 1 + (if p = ((0 : Fin 4), (0 : Fin 4)) then (1 : ℂ) else 0))
        (PEqualNP.Gct.permPoly ℂ 4) - 24 = 6 := by
  rw [eval_perm_four]
  simp
  norm_num

end PEqualNP.Gct.LS4
