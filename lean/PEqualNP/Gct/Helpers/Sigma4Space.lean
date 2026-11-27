import PEqualNP.Gct.Helpers.BorderedPerm
import PEqualNP.Gct.Helpers.BlockIsotropic

/-! Helper module for L-gct-087. An explicit seven dimensional linear space of `4 × 4` complex
matrices, through the all ones matrix with corner `-3`, on which the permanent vanishes. With
`w` a root of `w ^ 2 + w + 1`, put `U1 = (3, 0, 3 + 3 w, 2 + w)` and `U2 = (0, 3, -3 w, 1 - w)`.
The space is the set of matrices with rows `s1 U1 + t1 U2`, `s2 U1 + t2 U2`,
`(3 a, 3 b, -3 w a + 3 (1 + w) b, c)` and
`(3 a, 3 b, -3 w a + 3 (1 + w) b, 2 (w - 1) a - (4 + 2 w) b - c)`. Its permanent is
`(108 (s1 s2 + t1 t2) a b - 54 (s1 t2 + t1 s2) (a ^ 2 + b ^ 2)) * (w ^ 2 + w + 1)`. -/

namespace PEqualNP.Gct.Helpers.Sigma4Space

open Finset

/-- The permanent of a `4 × 4` matrix, written out. -/
theorem permanent_four (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.permanent =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 +
      A 0 0 * A 1 1 * A 2 3 * A 3 2 +
      A 0 0 * A 1 2 * A 2 1 * A 3 3 +
      A 0 0 * A 1 2 * A 2 3 * A 3 1 +
      A 0 0 * A 1 3 * A 2 1 * A 3 2 +
      A 0 0 * A 1 3 * A 2 2 * A 3 1 +
      A 0 1 * A 1 0 * A 2 2 * A 3 3 +
      A 0 1 * A 1 0 * A 2 3 * A 3 2 +
      A 0 1 * A 1 2 * A 2 0 * A 3 3 +
      A 0 1 * A 1 2 * A 2 3 * A 3 0 +
      A 0 1 * A 1 3 * A 2 0 * A 3 2 +
      A 0 1 * A 1 3 * A 2 2 * A 3 0 +
      A 0 2 * A 1 0 * A 2 1 * A 3 3 +
      A 0 2 * A 1 0 * A 2 3 * A 3 1 +
      A 0 2 * A 1 1 * A 2 0 * A 3 3 +
      A 0 2 * A 1 1 * A 2 3 * A 3 0 +
      A 0 2 * A 1 3 * A 2 0 * A 3 1 +
      A 0 2 * A 1 3 * A 2 1 * A 3 0 +
      A 0 3 * A 1 0 * A 2 1 * A 3 2 +
      A 0 3 * A 1 0 * A 2 2 * A 3 1 +
      A 0 3 * A 1 1 * A 2 0 * A 3 2 +
      A 0 3 * A 1 1 * A 2 2 * A 3 0 +
      A 0 3 * A 1 2 * A 2 0 * A 3 1 +
      A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  have h00 : (0 : Fin 4).succAbove (0 : Fin 3) = 1 := by decide
  have h01 : (0 : Fin 4).succAbove (1 : Fin 3) = 2 := by decide
  have h02 : (0 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h10 : (1 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
  have h11 : (1 : Fin 4).succAbove (1 : Fin 3) = 2 := by decide
  have h12 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h20 : (2 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
  have h21 : (2 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h22 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have h30 : (3 : Fin 4).succAbove (0 : Fin 3) = 0 := by decide
  have h31 : (3 : Fin 4).succAbove (1 : Fin 3) = 1 := by decide
  have h32 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  have c0 : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := by decide
  have c1 : Fin.castSucc (1 : Fin 3) = (1 : Fin 4) := by decide
  have c2 : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := by decide
  have hl : Fin.last 3 = (3 : Fin 4) := by decide
  rw [BorderedPerm.permanent_succ_last, Fin.sum_univ_four]
  simp only [PEqualNP.Gct.Helpers.BlockIso.permanent_three, Matrix.submatrix_apply,
    h00, h01, h02, h10, h11, h12, h20, h21, h22, h30, h31, h32, c0, c1, c2, hl]
  ring

/-- The entries of the general member of the space, as a matrix. -/
def entry (w : ℂ) (z : Fin 7 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  ![![3 * z 0, 3 * z 1, (3 + 3 * w) * z 0 - 3 * w * z 1, (2 + w) * z 0 + (1 - w) * z 1],
    ![3 * z 2, 3 * z 3, (3 + 3 * w) * z 2 - 3 * w * z 3, (2 + w) * z 2 + (1 - w) * z 3],
    ![3 * z 4, 3 * z 5, -(3 * w) * z 4 + (3 + 3 * w) * z 5, z 6],
    ![3 * z 4, 3 * z 5, -(3 * w) * z 4 + (3 + 3 * w) * z 5,
      (2 * w - 2) * z 4 - (4 + 2 * w) * z 5 - z 6]]

/-- The parametrisation of the space by seven complex numbers. -/
def param (w : ℂ) : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) where
  toFun z := fun p => entry w z p.1 p.2
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring

theorem param_apply (w : ℂ) (z : Fin 7 → ℂ) (i j : Fin 4) : param w z (i, j) = entry w z i j :=
  rfl

theorem param_injective (w : ℂ) : Function.Injective (param w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h : ∀ i j, entry w z i j = 0 := fun i j => by
    rw [← param_apply, hz]; rfl
  have e0 := h 0 0
  have e1 := h 0 1
  have e2 := h 1 0
  have e3 := h 1 1
  have e4 := h 2 0
  have e5 := h 2 1
  have e6 := h 2 3
  simp [entry] at e0 e1 e2 e3 e4 e5 e6
  funext k
  fin_cases k <;> simp [e0, e1, e2, e3, e4, e5, e6]

/-- The permanent vanishes on the whole space. -/
theorem eval_param (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (z : Fin 7 → ℂ) :
    MvPolynomial.eval (param w z) (PEqualNP.Gct.permPoly ℂ 4) = 0 := by
  rw [PEqualNP.Gct.MethodCeiling.eval_permPoly, permanent_four]
  simp only [Matrix.of_apply, param_apply]
  simp [entry]
  linear_combination
    (108 * (z 0 * z 2 + z 1 * z 3) * z 4 * z 5 -
      54 * (z 0 * z 3 + z 1 * z 2) * (z 4 ^ 2 + z 5 ^ 2)) * hw

/-- The all ones matrix with corner `-3` is the member with parameters
`(1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 1)`. -/
theorem sigma_eq_param (w : ℂ) :
    (fun p : Fin 4 × Fin 4 => if p.1.val = 3 ∧ p.2.val = 3 then (-3 : ℂ) else 1) =
      param w ![1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 3, 1 / 3, 1] := by
  funext ⟨i, j⟩
  rw [param_apply]
  fin_cases i <;> fin_cases j <;> simp [entry] <;> ring

/-- A root of `w ^ 2 + w + 1` in the complex numbers. -/
theorem exists_root : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
  have hs : (Complex.I * (Real.sqrt 3 : ℂ)) ^ 2 = -3 := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  exact ⟨(-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2, by linear_combination hs / 4⟩

/-- The space: seven dimensional, and the permanent vanishes on the translate of it through the
all ones matrix with corner `-3` (which is a member, so the translate is the space). -/
theorem main : ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), 7 ≤ Module.finrank ℂ L ∧ ∀ t ∈ L,
    MvPolynomial.eval ((fun p : Fin 4 × Fin 4 => if p.1.val = 3 ∧ p.2.val = 3 then (-3 : ℂ)
      else 1) + t) (PEqualNP.Gct.permPoly ℂ 4) = 0 := by
  obtain ⟨w, hw⟩ := exists_root
  refine ⟨LinearMap.range (param w), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (param_injective w), Module.finrank_fin_fun]
  · rintro t ⟨z, rfl⟩
    rw [sigma_eq_param w, ← map_add]
    exact eval_param w hw _

end PEqualNP.Gct.Helpers.Sigma4Space
