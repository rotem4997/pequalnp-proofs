import PEqualNP.Gct.Helpers.LS4.PermFour

/-! Helper for L-gct-091 (LS(4) <= 5), the `r <= 1` gluing step. `twoCol y z` is the `4 x 4`
matrix with columns `y, z, 0, 0`; `oneRow r w` has row `r` equal to `w` and is zero elsewhere.
When `y, z, w` have sum zero (so `twoCol y z` has zero column sums and `oneRow r w` zero row
sums), the part of `perm (J + A + R)` odd in `A = twoCol y z` is `2 (w 0 * y r + w 1 * z r)`:
`perm (J + A + R) - perm (J - A + R) = 4 (w 0 * y r + w 1 * z r)`. Consequence: a level space
(`perm (J + t) = 24` on it) containing such `A` and `R` has `w 0 * y r + w 1 * z r = 0`, so a
one- or two-column level space whose first column is nonzero at row `r` never glues with the
one-row space at row `r` (take `w = (1, 0, -1, 0)`). -/

namespace PEqualNP.Gct.LS4

open Finset

/-- Columns `y, z, 0, 0`. -/
def twoCol (y z : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.2 = 0 then y p.1 else if p.2 = 1 then z p.1 else 0

/-- Row `r` equal to `w`, zero elsewhere. -/
def oneRow (r : Fin 4) (w : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ :=
  if p.1 = r then w p.2 else 0

theorem odd_twoCol_oneRow (y z w : Fin 4 → ℂ) (r : Fin 4) (hy : ∑ i, y i = 0)
    (hz : ∑ i, z i = 0) (hw : ∑ j, w j = 0) :
    MvPolynomial.eval (fun p => 1 + (twoCol y z p + oneRow r w p)) (PEqualNP.Gct.permPoly ℂ 4) -
      MvPolynomial.eval (fun p => 1 + (-twoCol y z p + oneRow r w p))
        (PEqualNP.Gct.permPoly ℂ 4) = 4 * (w 0 * y r + w 1 * z r) := by
  rw [Fin.sum_univ_four] at hy hz hw
  have hy3 : y 3 = -(y 0 + y 1 + y 2) := by linear_combination hy
  have hz3 : z 3 = -(z 0 + z 1 + z 2) := by linear_combination hz
  have hw3 : w 3 = -(w 0 + w 1 + w 2) := by linear_combination hw
  rw [eval_perm_four, eval_perm_four]
  fin_cases r <;> simp [twoCol, oneRow, hy3, hz3, hw3] <;> ring

/-- In a level space, `A = twoCol y z` and `R = oneRow r w` (sums zero) satisfy
`w 0 * y r + w 1 * z r = 0`. -/
theorem level_twoCol_oneRow (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (y z w : Fin 4 → ℂ) (r : Fin 4) (hy : ∑ i, y i = 0) (hz : ∑ i, z i = 0)
    (hw : ∑ j, w j = 0) (hA : twoCol y z ∈ L) (hR : oneRow r w ∈ L) :
    w 0 * y r + w 1 * z r = 0 := by
  have h1 := hL _ (L.add_mem hA hR)
  have h2 := hL _ (L.add_mem (L.neg_mem hA) hR)
  have h := odd_twoCol_oneRow y z w r hy hz hw
  simp only [Pi.add_apply, Pi.neg_apply] at h1 h2
  rw [h1, h2] at h
  linear_combination -h / 4

/-- Gluing: a level space containing the whole one-row space at row `r` contains no
`twoCol y z` (sums zero) with `y r ≠ 0`. -/
theorem no_glue_oneRow (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (r : Fin 4) (hrow : ∀ w : Fin 4 → ℂ, ∑ j, w j = 0 → oneRow r w ∈ L)
    (y z : Fin 4 → ℂ) (hy : ∑ i, y i = 0) (hz : ∑ i, z i = 0) (hA : twoCol y z ∈ L) :
    y r = 0 := by
  have hw : ∑ j, (![1, 0, -1, 0] : Fin 4 → ℂ) j = 0 := by simp [Fin.sum_univ_four]
  have := level_twoCol_oneRow L hL y z ![1, 0, -1, 0] r hy hz hw hA (hrow _ hw)
  simpa using this

/-- Non-vacuity: the one-row space at row `r` is level. -/
theorem oneRow_level (r : Fin 4) (w : Fin 4 → ℂ) (hw : ∑ j, w j = 0) :
    MvPolynomial.eval (fun p => 1 + oneRow r w p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
  rw [Fin.sum_univ_four] at hw
  have hw3 : w 3 = -(w 0 + w 1 + w 2) := by linear_combination hw
  rw [eval_perm_four]
  fin_cases r <;> simp [oneRow, hw3] <;> ring

/-- Two-column level spaces: with sums zero, `perm (J + twoCol y z) - 24 = -2 Σ y i * z i`. -/
theorem twoCol_level (y z : Fin 4 → ℂ) (hy : ∑ i, y i = 0) (hz : ∑ i, z i = 0) :
    MvPolynomial.eval (fun p => 1 + twoCol y z p) (PEqualNP.Gct.permPoly ℂ 4) - 24 =
      -2 * ∑ i, y i * z i := by
  rw [Fin.sum_univ_four] at hy hz
  have hy3 : y 3 = -(y 0 + y 1 + y 2) := by linear_combination hy
  have hz3 : z 3 = -(z 0 + z 1 + z 2) := by linear_combination hz
  rw [eval_perm_four]
  simp [twoCol, Fin.sum_univ_four, hy3, hz3]
  ring

end PEqualNP.Gct.LS4
